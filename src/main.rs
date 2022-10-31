use fs::File;
use io::{BufRead, BufReader, BufWriter, Read, Seek, Write};
use std::collections::HashMap;
use std::{fmt, fs, io, mem, ptr};

mod elf;

pub enum LinkError {
	IO(io::Error),
	TooLarge,
}

impl fmt::Display for LinkError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use LinkError::*;
		match self {
			IO(e) => write!(f, "IO error: {e}"),
			TooLarge => write!(f, "executable file would be too large."),
		}
	}
}

impl From<io::Error> for LinkError {
	fn from(e: io::Error) -> Self {
		Self::IO(e)
	}
}

impl From<&LinkError> for String {
	fn from(e: &LinkError) -> Self {
		format!("{e}")
	}
}

pub enum LinkWarning {
	SymNotFound(String),
}

impl fmt::Display for LinkWarning {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use LinkWarning::*;
		match self {
			SymNotFound(s) => write!(f, "symbol not found: {s}"),
		}
	}
}

impl From<&LinkWarning> for String {
	fn from(e: &LinkWarning) -> Self {
		format!("{e}")
	}
}

pub enum ElfError {
	NotAnElf,
	Not32Bit,
	NotLE,
	BadVersion,
	BadType,
	BadMachine,
	BadUtf8,
	BadSymtab,
	BadLink(u64),
	BadRelHeader,
	UnsupportedRelocation(u8),
	BadSymIdx(u64),
	IO(io::Error),
}

impl From<&ElfError> for String {
	fn from(e: &ElfError) -> String {
		format!("{e}")
	}
}

impl fmt::Display for ElfError {
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
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
			UnsupportedRelocation(x) => write!(f, "unsupported relocation type: {x}"),
			BadLink(i) => write!(f, "bad ELF link: {i}"),
			BadSymIdx(i) => write!(f, "bad symbol index: {i}"),
		}
	}
}

impl From<io::Error> for ElfError {
	fn from(e: io::Error) -> ElfError {
		ElfError::IO(e)
	}
}

// to be more efficient™, we use integers to keep track of symbol names.
type SymbolNameType = u32;
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
struct SymbolName(SymbolNameType);
struct SymbolNames {
	count: SymbolNameType,
	to_string: Vec<String>,
	by_string: HashMap<String, SymbolName>,
}

impl SymbolNames {
	fn new() -> Self {
		Self {
			count: 0,
			to_string: vec![],
			by_string: HashMap::new(),
		}
	}

	fn add(&mut self, name: String) -> SymbolName {
		match self.by_string.get(&name) {
			Some(id) => *id,
			None => {
				// new symbol
				let id = SymbolName(self.count);
				self.count += 1;
				self.by_string.insert(name.clone(), id);
				self.to_string.push(name);
				id
			}
		}
	}

	#[allow(dead_code)]
	fn get_str(&self, id: SymbolName) -> Option<&str> {
		self.to_string.get(id.0 as usize).map(|s| &s[..])
	}

	#[allow(dead_code)]
	fn get(&self, name: &str) -> Option<SymbolName> {
		self.by_string.get(name).map(|r| *r)
	}
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct SourceId(u32);

#[derive(Copy, Clone, Debug)]
enum SymbolType {
	Function,
	Object,
	Other,
}

#[derive(Copy, Clone, Debug)]
enum SymbolValue {
	Bss(u64),
	Data(u64), // index into Linker.data
	Absolute(u64),
}

#[allow(dead_code)] // @TODO @TEMPORARY
#[derive(Debug)]
struct SymbolInfo {
	r#type: SymbolType,
	value: Option<SymbolValue>,
	size: u64,
}

struct Symbols {
	global: HashMap<SymbolName, SymbolInfo>,
	weak: HashMap<SymbolName, SymbolInfo>,
	local: HashMap<(SourceId, SymbolName), SymbolInfo>,
}

impl Symbols {
	fn new() -> Self {
		Self {
			global: HashMap::new(),
			weak: HashMap::new(),
			local: HashMap::new(),
		}
	}

	fn add_weak(&mut self, name: SymbolName, info: SymbolInfo) {
		self.weak.insert(name, info);
	}

	fn add_local(&mut self, source: SourceId, name: SymbolName, info: SymbolInfo) {
		self.local.insert((source, name), info);
	}

	fn add_global(&mut self, name: SymbolName, info: SymbolInfo) {
		self.global.insert(name, info);
	}

	fn get(&self, source: SourceId, name: SymbolName) -> Option<&SymbolInfo> {
		self.local
			.get(&(source, name))
			.or_else(|| self.global.get(&name))
			.or_else(|| self.weak.get(&name))
	}
}

#[allow(dead_code)] // @TODO @TEMPORARY
#[derive(Debug, Clone, Copy)]
enum RelocationType {
	Direct32,
	Pc32,
	GotOff32,
	GotPc32,
}

impl RelocationType {
	fn from_x86_u8(id: u8) -> Result<Self, ElfError> {
		use RelocationType::*;
		Ok(match id {
			1 => Direct32,
			2 => Pc32,
			9 => GotOff32,
			10 => GotPc32,
			_ => return Err(ElfError::UnsupportedRelocation(id)),
		})
	}
}

#[derive(Debug, Clone)]
#[allow(dead_code)] // @TODO @TEMPORARY
struct Relocation {
	offset: u64,
	source_id: SourceId,
	sym: SymbolName,
	r#type: RelocationType,
	addend: i64,
}

impl Relocation {
	fn new_x86(
		symtab: &HashMap<u32, SymbolName>,
		source_id: SourceId,
		offset: u64,
		info: u32,
		addend: i32,
	) -> Result<Self, ElfError> {
		let r#type = info as u8;
		let sym_idx = info >> 8;
		match symtab.get(&sym_idx) {
			Some(sym) => Ok(Self {
				offset,
				source_id,
				sym: *sym,
				r#type: RelocationType::from_x86_u8(r#type)?,
				addend: addend.into(),
			}),
			None => Err(ElfError::BadSymIdx(sym_idx.into())),
		}
	}
}

struct Linker {
	strtab_offset: u64,
	data: Vec<u8>, // contains all data from all objects.
	source_count: u32,
	symbols: Symbols,
	symbol_names: SymbolNames,
	relocations: Vec<Relocation>,
	sections: Vec<elf::Shdr32>,
	warnings: Vec<LinkWarning>,
	bss_size: u64,
}

impl Linker {
	fn new() -> Self {
		Linker {
			symbols: Symbols::new(),
			symbol_names: SymbolNames::new(),
			source_count: 0,
			strtab_offset: 0,
			bss_size: 0,
			data: vec![],
			sections: vec![],
			relocations: vec![],
			warnings: vec![],
		}
	}

	fn get_str(&self, reader: &mut BufReader<File>, offset: u32) -> Result<String, ElfError> {
		reader.seek(io::SeekFrom::Start(offset as u64 + self.strtab_offset))?;
		let mut bytes = vec![];
		reader.read_until(0, &mut bytes)?;
		bytes.pop(); // remove terminating \0
		String::from_utf8(bytes).map_err(|_| ElfError::BadUtf8)
	}

	// returns SymbolName corresponding to the symbol
	fn add_symbol(
		&mut self,
		source: SourceId,
		source_offset: u64,
		reader: &mut BufReader<File>,
	) -> Result<SymbolName, ElfError> {
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
		let name_id = self.symbol_names.add(name);
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
			_ => SymbolType::Other,
		};

		let value = match sym.shndx {
			SHN_UNDEF | SHN_COMMON => None,
			SHN_ABS => Some(SymbolValue::Absolute(sym.value as u64)),
			ndx if (ndx as usize) < self.sections.len() => {
				let ndx = ndx as usize;
				match self.get_str(reader, self.sections[ndx].name)?.as_str() {
					".text" | ".data" | ".data1" | ".rodata" | ".rodata1" => {
						Some(SymbolValue::Data(
							source_offset + self.sections[ndx].offset as u64 + sym.value as u64,
						))
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

		let info = SymbolInfo {
			r#type,
			value,
			size,
		};
		match bind {
			STB_LOCAL => self.symbols.add_local(source, name_id, info),
			STB_GLOBAL => self.symbols.add_global(name_id, info),
			STB_WEAK => self.symbols.add_weak(name_id, info),
			_ => {}
		}

		Ok(name_id)
	}

	pub fn process_object(&mut self, reader: &mut BufReader<File>) -> Result<(), ElfError> {
		use ElfError::*;
		let source_offset = self.data.len() as u64;
		reader.read_to_end(&mut self.data)?;
		reader.seek(io::SeekFrom::Start(0))?;

		let source_id = SourceId(self.source_count);
		self.source_count += 1;

		let mut elf = [0u8; 0x34];
		reader.read_exact(&mut elf)?;
		let elf: elf::Header32 = unsafe { mem::transmute(elf) };

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
		if elf.r#type != elf::ET_REL {
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
			let shdr: elf::Shdr32 = unsafe { mem::transmute(shdr_buf) };
			shdr.offset as u64
		};

		let mut sections_by_name = HashMap::with_capacity(elf.shnum as _);
		self.sections.reserve(elf.shnum as _);
		for s_idx in 0..elf.shnum {
			reader.seek(elf.section_seek(s_idx))?;
			reader.read_exact(&mut shdr_buf)?;
			let shdr: elf::Shdr32 = unsafe { mem::transmute(shdr_buf) };
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
			let count: u32 = (size / entsize).try_into().map_err(|_| BadSymtab)?; // 4 billion symbols is ridiculous
			symtab.reserve(count as usize);
			for sym_idx in 0..count {
				reader.seek(io::SeekFrom::Start(offset + sym_idx as u64 * entsize))?;
				let name = self.add_symbol(source_id, source_offset, reader)?;
				symtab.insert(sym_idx, name);
			}
		}

		for shdr in sections_by_name.values() {
			// we only process relocations relating to .symtab currently.
			match self.sections.get(shdr.link as usize) {
				None => continue,
				Some(h) => {
					if self.get_str(reader, h.name)? != ".symtab" {
						continue;
					}
				}
			}

			fn read_relocations<RelType>(
				reader: &mut BufReader<File>,
				shdr: &elf::Shdr32,
			) -> Result<Vec<RelType>, ElfError> {
				let offset = shdr.offset as u64;
				let size = shdr.size as u64;
				let entsize = shdr.entsize as u64;
				if size % entsize != 0 || entsize < mem::size_of::<RelType>() as u64 {
					return Err(BadRelHeader);
				}
				let count = size / entsize;
				let mut relocations = Vec::with_capacity(count as _);
				// annoyingly, array sizes can't depend on the size of a type parameter.
				// if they could, we could just use transmute and everyone would be happier.
				let mut rel_buf = [0; 32];
				let rel_data = &mut rel_buf[..mem::size_of::<RelType>()];

				for rel_idx in 0..count {
					reader.seek(io::SeekFrom::Start(offset + rel_idx * entsize))?;

					reader.read_exact(rel_data)?;
					let mut rel = mem::MaybeUninit::uninit();
					let rel = unsafe {
						ptr::copy_nonoverlapping(
							(&rel_data[0]) as *const u8,
							rel.as_mut_ptr() as *mut u8,
							mem::size_of::<RelType>(),
						);
						rel.assume_init()
					};

					relocations.push(rel);
				}
				Ok(relocations)
			}

			let info_section_offset = source_offset
				+ self
					.sections
					.get(shdr.info as usize)
					.ok_or(BadLink(shdr.info as u64))?
					.offset as u64;

			let add_relocation_x86 =
				|me: &mut Self, offset: u32, info: u32, addend: i32| -> Result<(), ElfError> {
					me.relocations.push(Relocation::new_x86(
						&symtab,
						source_id,
						info_section_offset + offset as u64,
						info,
						addend,
					)?);
					Ok(())
				};

			const SHT_RELA: u32 = 4;
			const SHT_REL: u32 = 9;
			match shdr.r#type {
				SHT_RELA => {
					#[repr(C)]
					struct ElfRela {
						offset: u32,
						info: u32,
						addend: i32,
					}
					let rels: Vec<ElfRela> = read_relocations(reader, shdr)?;
					for rela in rels {
						add_relocation_x86(
							self,
							rela.offset as _,
							rela.info as _,
							rela.addend as _,
						)?;
					}
				}
				SHT_REL => {
					#[repr(C)]
					struct ElfRel {
						offset: u32,
						info: u32,
					}
					let rels: Vec<ElfRel> = read_relocations(reader, shdr)?;
					for rel in rels {
						add_relocation_x86(self, rel.offset as _, rel.info as _, 0)?;
					}
				}
				_ => {}
			}
		}

		Ok(())
	}

	fn get_sym_name(&self, id: SymbolName) -> Option<&str> {
		self.symbol_names.get_str(id)
	}

	// get symbol, producing a warning if it does not exist.
	fn get_symbol(&mut self, source_id: SourceId, id: SymbolName) -> Option<&SymbolInfo> {
		let sym = self.symbols.get(source_id, id);
		if sym.is_none() {
			let warn = LinkWarning::SymNotFound(self.get_sym_name(id).unwrap_or("???").into());
			self.warnings.push(warn);
		}
		sym
	}

	fn apply_relocation(&mut self, rel: Relocation) -> Result<(), LinkError> {
		let symbol = match self.get_symbol(rel.source_id, rel.sym) {
			None => return Ok(()),
			Some(sym) => sym,
		};
		println!("{rel:?} {symbol:?}");
		Ok(())
	}

	pub fn link<T: Write>(
		&mut self,
		out: &mut BufWriter<T>,
	) -> Result<Vec<LinkWarning>, LinkError> {
		// we have to use an index because for all rust knows,
		// apply_relocation modifies self.relocations (it doesn't).
		for i in 0..self.relocations.len() {
			self.apply_relocation(self.relocations[i].clone())?;
		}

		const SEGMENT_ADDR: u32 = 0x400000;

		let data_size = 0;

		let mut header = elf::Header32::default();
		let header_size: u32 = header.ehsize.into();
		let phdr_size: u32 = header.phentsize.into();
		let file_size = header_size + phdr_size + data_size;
		let entry_point = SEGMENT_ADDR + header_size + phdr_size;
		header.phnum = 1;
		header.phoff = header_size;
		header.entry = entry_point;
		out.write_all(&header.to_bytes())?;

		let bss_size: u32 = self.bss_size.try_into().map_err(|_| LinkError::TooLarge)?;

		let phdr = elf::Phdr32 {
			flags: 0b111, // read, write, execute
			offset: 0,
			vaddr: SEGMENT_ADDR,
			filesz: file_size,
			memsz: file_size + bss_size,
			..Default::default()
		};
		out.write_all(&phdr.to_bytes())?;

		Ok(mem::take(&mut self.warnings))
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

	use std::os::unix::fs::OpenOptionsExt;
	let mut out_options = fs::OpenOptions::new();
	out_options
		.write(true)
		.create(true)
		.truncate(true)
		.mode(0o755);

	let mut output = match out_options.open("a.out") {
		Ok(out) => BufWriter::new(out),
		Err(e) => {
			eprintln!("Error opening output file: {e}");
			return;
		}
	};

	if let Err(e) = linker.link(&mut output) {
		eprintln!("Error linking: {e}");
	}
}
