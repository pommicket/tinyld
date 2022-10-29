use fs::File;
use io::{BufRead, BufReader, Read, Seek};
use std::collections::HashMap;
use std::{fmt, fs, io, mem};

pub enum ElfError {
	NotAnElf,
	Not32Bit,
	NotLE,
	BadVersion,
	BadType,
	BadMachine,
	BadUtf8,
	BadSymtab,
	BadRelHeader,
	IO(io::Error),
}

impl From<&ElfError> for String {
	fn from(e: &ElfError) -> String {
		format!("{e}")
	}
}

impl fmt::Display for ElfError {
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), std::fmt::Error> {
		use ElfError::*;
		match self {
			// Display for UnexpectedEof *should* be this but is less clear
			//  ("failed to fill whole buffer")
			IO(i) if i.kind() == io::ErrorKind::UnexpectedEof => write!(f, "unexpected EOF"),
			IO(i) => write!(f, "IO error: {i}"),
			NotAnElf => write!(f, "not an ELF file"),
			Not32Bit => write!(f, "ELF file is not 32-bit"),
			NotLE => write!(f, "ELF file is not little-endian"),
			BadVersion => write!(f, "ELF version is not 1 (are you living in the future?)"),
			BadType => write!(f, "wrong type of ELF file"),
			BadMachine => write!(
				f,
				"unsupported architecture (only x86 is currently supported)"
			),
			BadUtf8 => write!(f, "bad UTF-8 in ELF file"),
			BadSymtab => write!(f, "bad ELF symbol table"),
			BadRelHeader => write!(f, "bad ELF relocation header"),
		}
	}
}

impl From<io::Error> for ElfError {
	fn from(e: io::Error) -> ElfError {
		ElfError::IO(e)
	}
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct SourceIndex(u32);

enum SymbolType {
	Function,
	Object,
}

enum SymbolValue {
	Bss(u64),
	Data(u64), // index into Linker.data
	Absolute(u64),
}

#[allow(dead_code)] // @TODO @TEMPORARY
struct SymbolInfo {
	r#type: SymbolType,
	value: SymbolValue,
	size: u64,
}

struct Symbols {
	global: HashMap<String, SymbolInfo>,
	weak: HashMap<String, SymbolInfo>,
	local: HashMap<(SourceIndex, String), SymbolInfo>,
}

impl Symbols {
	fn new() -> Self {
		Self {
			global: HashMap::new(),
			weak: HashMap::new(),
			local: HashMap::new(),
		}
	}

	fn add_weak(&mut self, name: String, info: SymbolInfo) {
		self.weak.insert(name, info);
	}

	fn add_local(&mut self, source: SourceIndex, name: String, info: SymbolInfo) {
		self.local.insert((source, name), info);
	}

	fn add_global(&mut self, name: String, info: SymbolInfo) {
		self.global.insert(name, info);
	}
}

#[allow(dead_code)] // @TODO @TEMPORARY
struct Relocation {
	offset: u64,
	info: u64,
	addend: i64,
}

#[repr(C)]
#[derive(Clone)]
struct ElfShdr {
	name: u32,
	r#type: u32,
	flags: u32,
	addr: u32,
	offset: u32,
	size: u32,
	link: u32,
	info: u32,
	addralign: u32,
	entsize: u32,
}

struct Linker {
	strtab_offset: u64,
	data: Vec<u8>, // contains all data from all objects.
	source_count: u32,
	symbols: Symbols,
	relocations: Vec<Relocation>,
	sections: Vec<ElfShdr>,
	bss_size: u64,
}

impl Linker {
	fn new() -> Self {
		Linker {
			symbols: Symbols::new(),
			source_count: 0,
			strtab_offset: 0,
			bss_size: 0,
			data: vec![],
			sections: vec![],
			relocations: vec![],
		}
	}

	fn get_str(&self, reader: &mut BufReader<File>, offset: u32) -> Result<String, ElfError> {
		reader.seek(io::SeekFrom::Start(offset as u64 + self.strtab_offset))?;
		let mut bytes = vec![];
		reader.read_until(0, &mut bytes)?;
		bytes.pop(); // remove terminating \0
		String::from_utf8(bytes).map_err(|_| ElfError::BadUtf8)
	}

	// returns name of symbol
	fn add_symbol(
		&mut self,
		source: SourceIndex,
		source_offset: u64,
		reader: &mut BufReader<File>,
	) -> Result<String, ElfError> {
		#[repr(C)]
		pub struct ElfSym {
			name: u32,
			value: u32,
			size: u32,
			info: u8,
			other: u8,
			shndx: u16,
		}

		let mut sym_buf = [0u8; 16];
		reader.read_exact(&mut sym_buf)?;
		let sym: ElfSym = unsafe { mem::transmute(sym_buf) };
		let r#type = sym.info & 0xf;
		let bind = sym.info >> 4;
		let name = self.get_str(reader, sym.name)?;
		let size = sym.size as u64;

		const STT_OBJECT: u8 = 1;
		const STT_FUNC: u8 = 2;
		const STB_LOCAL: u8 = 0;
		const STB_GLOBAL: u8 = 1;
		const STB_WEAK: u8 = 2;
		const SHN_UNDEF: u16 = 0;
		const SHN_ABS: u16 = 0xfff1;
		const SHN_COMMON: u16 = 0xfff2;

		let r#type = match r#type {
			STT_OBJECT => SymbolType::Object,
			STT_FUNC => SymbolType::Function,
			_ => return Ok(name), // what can we do
		};

		let value = match sym.shndx {
			SHN_UNDEF | SHN_COMMON => None,
			SHN_ABS => Some(SymbolValue::Absolute(sym.value as u64)),
			ndx if (ndx as usize) < self.sections.len() => {
				let ndx = ndx as usize;
				match self.get_str(reader, self.sections[ndx].name)?.as_str() {
					".text" | ".data" | ".data1" | ".rodata" | ".rodata1" => {
						Some(SymbolValue::Data(source_offset + self.sections[ndx].offset as u64 + sym.value as u64))
					}
					".bss" => {
						let p = self.bss_size;
						self.bss_size += size;
						Some(SymbolValue::Bss(p))
					}
					_ => None, // huh
				}
			}
			_ => None,
		};

		if let Some(value) = value {
			let info = SymbolInfo {
				r#type,
				value,
				size,
			};
			match bind {
				STB_LOCAL => self.symbols.add_local(source, name.clone(), info),
				STB_GLOBAL => self.symbols.add_global(name.clone(), info),
				STB_WEAK => self.symbols.add_weak(name.clone(), info),
				_ => {}
			}
		}

		Ok(name)
	}

	fn add_relocation(&mut self, offset: u64, info: u64, addend: i64) {
		self.relocations.push(Relocation { offset, info, addend })
	}

	pub fn process_object(&mut self, reader: &mut BufReader<File>) -> Result<(), ElfError> {
		use ElfError::*;
		let source_offset = self.data.len() as u64;
		reader.read_to_end(&mut self.data)?;
		reader.seek(io::SeekFrom::Start(0))?;

		let source_idx = SourceIndex(self.source_count);
		self.source_count += 1;

		#[repr(C)]
		struct ElfHeader {
			ident: [u8; 4],
			class: u8,
			data: u8,
			version: u8,
			abi: u8,
			abiversion: u8,
			pad: [u8; 7],
			r#type: u16,
			machine: u16,
			version2: u32,
			entry: u32,
			phoff: u32,
			shoff: u32,
			flags: u32,
			ehsize: u16,
			phentsize: u16,
			phnum: u16,
			shentsize: u16,
			shnum: u16,
			shstrndx: u16,
		}


		impl ElfHeader {
			fn section_offset(&self, ndx: u16) -> u64 {
				ndx as u64 * self.shentsize as u64 + self.shoff as u64
			}

			fn section_seek(&self, ndx: u16) -> io::SeekFrom {
				io::SeekFrom::Start(self.section_offset(ndx))
			}
		}

		let mut elf = [0u8; 0x34];
		reader.read_exact(&mut elf)?;
		let elf: ElfHeader = unsafe { mem::transmute(elf) };

		if elf.ident != [0x7f, b'E', b'L', b'F'] {
			return Err(NotAnElf);
		}
		if elf.class != 1 {
			return Err(Not32Bit);
		}
		if elf.data != 1 {
			return Err(NotLE);
		}
		if elf.version != 1 || elf.version2 != 1 {
			return Err(BadVersion);
		}
		if elf.r#type != 1 {
			return Err(BadType);
		}
		if elf.machine != 3 {
			return Err(BadMachine);
		}

		let mut shdr_buf = [0u8; 0x28];
		self.strtab_offset = {
			// read .strtab header
			reader.seek(elf.section_seek(elf.shstrndx))?;
			reader.read_exact(&mut shdr_buf)?;
			let shdr: ElfShdr = unsafe { mem::transmute(shdr_buf) };
			shdr.offset as u64
		};

		let mut sections_by_name = HashMap::with_capacity(elf.shnum as _);
		self.sections.reserve(elf.shnum as _);
		for s_idx in 0..elf.shnum {
			reader.seek(elf.section_seek(s_idx))?;
			reader.read_exact(&mut shdr_buf)?;
			let shdr: ElfShdr = unsafe { mem::transmute(shdr_buf) };
			let name = self.get_str(reader, shdr.name)?;
			sections_by_name.insert(name.clone(), shdr.clone());
			self.sections.push(shdr);
		}

		let mut symtab = HashMap::new();
		if let Some(shdr) = sections_by_name.get(".symtab") {
			// read .symtab
			let size = shdr.size as u64;
			let entsize = shdr.entsize as u64;
			let offset = shdr.offset as u64;
			if size % entsize != 0 || entsize < 16 {
				return Err(BadSymtab);
			}
			let count = (size / entsize) as u64;
			symtab.reserve(count as _);
			for sym_idx in 0..count {
				reader.seek(io::SeekFrom::Start(offset + sym_idx * entsize))?;
				let name = self.add_symbol(source_idx, source_offset, reader)?;
				symtab.insert(sym_idx, name);
			}
		}
		
		for shdr in sections_by_name.values() {
			const SHT_RELA: u32 = 4;
			const SHT_REL: u32 = 9;
			match shdr.r#type {
				SHT_RELA => {
					let size = shdr.size as u64;
					let entsize = shdr.entsize as u64;
					if size % entsize != 0 || entsize < 12 {
						return Err(BadRelHeader);
					}
					let count = size / entsize;
					for _ in 0..count {
						#[repr(C)]
						struct ElfRela {
							offset: u32,
							info: u32,
							addend: i32
						}
						let mut rela_buf = [0; 12];
						reader.read_exact(&mut rela_buf)?;
						let rela: ElfRela = unsafe { mem::transmute(rela_buf) };
						self.add_relocation(rela.offset as _, rela.info as _, rela.addend as _);
					}
				},
				SHT_REL => {
					let size = shdr.size as u64;
					let entsize = shdr.entsize as u64;
					if size % entsize != 0 || entsize < 8 {
						return Err(BadRelHeader);
					}
					let count = size / entsize;
					for _ in 0..count {
						#[repr(C)]
						struct ElfRel {
							offset: u32,
							info: u32,
						}
						let mut rel_buf = [0; 8];
						reader.read_exact(&mut rel_buf)?;
						let rel: ElfRel = unsafe { mem::transmute(rel_buf) };
						self.add_relocation(rel.offset as _, rel.info as _, 0);
					}
				},
				_ => {},
			}
		}

		Ok(())
	}
}

fn main() {
	let mut args = std::env::args();
	args.next(); // program name
	let args: Vec<String> = args.collect();
	if args.len() == 1 && args[0] == "--nya" {
		println!("hai uwu ^_^");
		return;
	}
	let mut inputs: Vec<String> = args;
	if inputs.is_empty() {
		if cfg!(debug_assertions) {
			inputs.push("test.o".into());
		} else {
			eprintln!("no arguments provided.");
			return;
		}
	}

	let mut object_files = vec![];
	let mut libraries = vec![];

	for input in inputs {
		if input.ends_with(".o") {
			object_files.push(input);
		} else if input.ends_with(".so") {
			libraries.push(input);
		}
	}

	let mut linker = Linker::new();

	for filename in &object_files {
		let file = match File::open(filename) {
			Ok(file) => file,
			Err(e) => {
				eprintln!("Error opening {filename}: {e}");
				return;
			}
		};
		let mut file = BufReader::new(file);
		if let Err(e) = linker.process_object(&mut file) {
			eprintln!("Error processing object file {filename}: {e}");
			return;
		}
	}
}
