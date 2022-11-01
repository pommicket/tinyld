use fs::File;
use io::{BufRead, BufReader, BufWriter, Read, Seek, Write};
use std::collections::{BTreeMap, HashMap};
use std::{fmt, fs, io, mem, ptr};

#[cfg(target_endian = "big")]
compile_error! {"WHY do you have a big endian machine???? it's the 21st century, buddy. this program won't work fuck you"}

mod elf;

pub enum LinkError {
	IO(io::Error),
	TooLarge,
	NoEntry(String),         // no entry point
	EntryNotDefined(String), // entry point is declared, but not defined
}

impl fmt::Display for LinkError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use LinkError::*;
		match self {
			IO(e) => write!(f, "IO error: {e}"),
			TooLarge => write!(f, "executable file would be too large."),
			NoEntry(name) => write!(f, "entry point '{name}' not found."),
			EntryNotDefined(name) => write!(f, "entry point '{name}' declared, but not defined."),
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
	RelSymNotFound { source: String, name: String },
	RelOOB(String, u64),
	RelNoData(String, u64),
	RelNoValue(String),
}

impl fmt::Display for LinkWarning {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use LinkWarning::*;
		match self {
			RelSymNotFound { source, name } => write!(f, "undefined symbol '{name}' (in {source}) (relocation ignored)."),
			RelOOB(text, offset) => write!(f, "relocation applied to {text}+0x{offset:x}, which goes outside of the symbol (it will be ignored)."),
			RelNoData(source, offset) => write!(
				f,
				"offset {source}+0x{offset:x} not in a data/text section. relocation will be ignored."
			),
			RelNoValue(name) => write!(f, "can't figure out value of symbol '{name}' (relocation ignored)."),
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
	NoStrtab,
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
			NoStrtab => write!(f, "object has no .strtab section"),
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

impl SourceId {
	const NONE: Self = Self(u32::MAX);
}

type SymbolIdType = u32;
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct SymbolId(SymbolIdType);

#[derive(Copy, Clone, Debug)]
enum SymbolType {
	Function,
	Object,
	Other,
}

#[derive(Debug)]
enum SymbolValue {
	Bss(u64),
	Data(Vec<u8>),
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
	info: Vec<SymbolInfo>,
	// this field isn't strictly needed for linking,
	// but it lets us print nice error messages like
	//   error linking main.c:some_function instead of
	//   error linking symbol 387
	locations: HashMap<SymbolId, (SourceId, SymbolName)>,
	global: HashMap<SymbolName, SymbolId>,
	weak: HashMap<SymbolName, SymbolId>,
	local: HashMap<(SourceId, SymbolName), SymbolId>,
}

impl Symbols {
	fn new() -> Self {
		Self {
			info: vec![],
			global: HashMap::new(),
			weak: HashMap::new(),
			local: HashMap::new(),
			locations: HashMap::new(),
		}
	}

	fn add_(&mut self, source: SourceId, name: SymbolName, info: SymbolInfo) -> SymbolId {
		let id = SymbolId(self.info.len() as _);
		self.info.push(info);
		self.locations.insert(id, (source, name));
		id
	}

	fn add_weak(&mut self, source: SourceId, name: SymbolName, info: SymbolInfo) -> SymbolId {
		let id = self.add_(source, name, info);
		self.weak.insert(name, id);
		id
	}

	fn add_local(&mut self, source: SourceId, name: SymbolName, info: SymbolInfo) -> SymbolId {
		let id = self.add_(source, name, info);
		self.local.insert((source, name), id);
		id
	}

	fn add_global(&mut self, source: SourceId, name: SymbolName, info: SymbolInfo) -> SymbolId {
		let id = self.add_(source, name, info);
		self.global.insert(name, id);
		id
	}

	fn get_mut_info_from_id(&mut self, id: SymbolId) -> Option<&mut SymbolInfo> {
		self.info.get_mut(id.0 as usize)
	}

	fn get_info_from_id(&self, id: SymbolId) -> Option<&SymbolInfo> {
		self.info.get(id.0 as usize)
	}

	fn get_id_from_name(&self, source: SourceId, name: SymbolName) -> Option<SymbolId> {
		self.local
			.get(&(source, name))
			.or_else(|| self.global.get(&name))
			.or_else(|| self.weak.get(&name))
			.map(|r| *r)
	}

	fn get_location_from_id(&self, id: SymbolId) -> Option<(SourceId, SymbolName)> {
		self.locations.get(&id).map(|r| *r)
	}

	fn count(&self) -> usize {
		self.info.len()
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
	r#where: (SymbolId, u64), // (symbol containing relocation, offset in symbol where relocation needs to be applied)
	source_id: SourceId,
	source_offset: u64,
	sym: SymbolName,
	r#type: RelocationType,
	addend: i64,
}

struct Linker {
	src_strtab_offset: u64,   // .strtab offset in current object file
	src_shstrtab_offset: u64, // .shstrtab offset in current object file
	symbols: Symbols,
	symbol_names: SymbolNames,
	relocations: Vec<Relocation>,
	sections: Vec<elf::Shdr32>,
	sources: Vec<String>,
	bss_size: u64,                        // output bss size
	bss_addr: u64,                        // output bss address
	data_addr: u64,                       // output data address
	symbol_addrs: HashMap<SymbolId, u64>, // output addresses of symbols
	warn: fn(LinkWarning),
}

// this maps between offsets in an object file and symbols defined in that file.
// this is used to figure out where relocations are taking place.
struct AddrMap {
	map: BTreeMap<(u64, u64), SymbolId>,
}

impl AddrMap {
	fn new() -> Self {
		AddrMap {
			map: BTreeMap::new(),
		}
	}

	fn add_symbol(&mut self, offset: u64, size: u64, id: SymbolId) {
		if size > 0 {
			self.map.insert((offset, offset + size), id);
		}
	}

	// returns symbol, offset in symbol.
	// e.g. a relocation might happen at main+0x33.
	fn get(&self, offset: u64) -> Option<(SymbolId, u64)> {
		let mut r = self.map.range(..(offset, u64::MAX));
		let (key, value) = r.next_back()?;
		if offset >= key.0 && offset < key.1 {
			// offset corresponds to somewhere in this symbol
			Some((*value, offset - key.0))
		} else {
			None
		}
	}
}

// graph of which symbols use which symbols
// this is needed so we don't emit anything for unused symbols.
type SymbolGraph = HashMap<SymbolId, Vec<SymbolId>>;

const MAX_REL_SIZE: usize = 8; // this seems reasonable

impl Linker {
	fn default_warn_handler(warning: LinkWarning) {
		eprintln!("warning: {warning}");
	}

	// why use fn of all things to transmit warnings?
	// well, it's very nice for stuff to not need a mutable reference
	// to emit warnings, and this is basically the only way of doing it.
	// if you need to mutate state in your warning handler, you can always
	// use a mutex.
	pub fn _set_warning_handler(&mut self, warn: fn(LinkWarning)) {
		self.warn = warn;
	}

	pub fn new() -> Self {
		Linker {
			symbols: Symbols::new(),
			symbol_names: SymbolNames::new(),
			src_strtab_offset: 0,
			src_shstrtab_offset: 0,
			bss_addr: 0,
			bss_size: 0,
			data_addr: 0,
			sections: vec![],
			relocations: vec![],
			sources: vec![],
			symbol_addrs: HashMap::new(),
			warn: Self::default_warn_handler,
		}
	}

	fn source_name(&self, id: SourceId) -> &str {
		&self.sources[id.0 as usize]
	}

	fn get_shstrtab(&self, reader: &mut BufReader<File>, offset: u32) -> Result<String, ElfError> {
		reader.seek(io::SeekFrom::Start(
			offset as u64 + self.src_shstrtab_offset,
		))?;
		let mut bytes = vec![];
		reader.read_until(0, &mut bytes)?;
		bytes.pop(); // remove terminating \0
		String::from_utf8(bytes).map_err(|_| ElfError::BadUtf8)
	}

	fn get_strtab(&self, reader: &mut BufReader<File>, offset: u32) -> Result<String, ElfError> {
		reader.seek(io::SeekFrom::Start(offset as u64 + self.src_strtab_offset))?;
		let mut bytes = vec![];
		reader.read_until(0, &mut bytes)?;
		bytes.pop(); // remove terminating \0
		String::from_utf8(bytes).map_err(|_| ElfError::BadUtf8)
	}

	// returns SymbolName corresponding to the symbol
	fn read_symbol(
		&mut self,
		source: SourceId,
		addr_map: &mut AddrMap,
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
		let name = self.get_strtab(reader, sym.name)?;
		let name_id = self.symbol_names.add(name);
		let size = sym.size as u64;

		let r#type = match r#type {
			elf::STT_OBJECT => SymbolType::Object,
			elf::STT_FUNC => SymbolType::Function,
			_ => SymbolType::Other,
		};

		let mut data_offset = None;

		let value = match sym.shndx {
			elf::SHN_UNDEF | elf::SHN_COMMON => None,
			elf::SHN_ABS => Some(SymbolValue::Absolute(sym.value as u64)),
			ndx if (ndx as usize) < self.sections.len() => {
				let ndx = ndx as usize;
				match self.sections[ndx].r#type {
					elf::SHT_PROGBITS => {
						let offset = self.sections[ndx].offset as u64 + sym.value as u64;
						data_offset = Some(offset);
						reader.seek(io::SeekFrom::Start(offset))?;
						let mut data = vec![0; size as usize];
						reader.read_exact(&mut data)?;
						Some(SymbolValue::Data(data))
					}
					elf::SHT_NOBITS => {
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
		let symbol_id = match bind {
			elf::STB_LOCAL => self.symbols.add_local(source, name_id, info),
			elf::STB_GLOBAL => self.symbols.add_global(source, name_id, info),
			elf::STB_WEAK => self.symbols.add_weak(source, name_id, info),
			_ => return Ok(name_id),
		};

		if let Some(offset) = data_offset {
			addr_map.add_symbol(offset, size, symbol_id);
		}
		Ok(name_id)
	}

	fn add_relocation_x86(
		&mut self,
		symtab: &[SymbolName],
		addr_map: &AddrMap,
		source_id: SourceId,
		offset: u64,
		info: u32,
		addend: i32,
	) -> Result<(), ElfError> {
		let r#type = info as u8;
		let sym_idx = info >> 8;

		if let Some(r#where) = addr_map.get(offset) {
			match symtab.get(sym_idx as usize) {
				Some(sym) => {
					self.relocations.push(Relocation {
						r#where,
						source_id,
						source_offset: offset,
						sym: *sym,
						r#type: RelocationType::from_x86_u8(r#type)?,
						addend: addend.into(),
					});
				}
				None => return Err(ElfError::BadSymIdx(sym_idx.into())),
			}
		} else {
			self.emit_warning(LinkWarning::RelNoData(
				self.source_name(source_id).into(),
				offset,
			));
		}
		Ok(())
	}

	pub fn process_object(
		&mut self,
		name: &str,
		reader: &mut BufReader<File>,
	) -> Result<(), ElfError> {
		use ElfError::*;

		let mut addr_map = AddrMap::new();

		reader.seek(io::SeekFrom::Start(0))?;

		let source_id = SourceId(self.sources.len() as _);
		self.sources.push(name.into());

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
		self.src_shstrtab_offset = {
			// read .shstrtab header
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
			let name = self.get_shstrtab(reader, shdr.name)?;
			sections_by_name.insert(name.clone(), shdr.clone());
			self.sections.push(shdr);
		}

		self.src_strtab_offset = if let Some(strtab) = sections_by_name.get(".strtab") {
			strtab.offset.into()
		} else {
			return Err(NoStrtab);
		};

		let mut symtab = vec![];
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
				let name = self.read_symbol(source_id, &mut addr_map, reader)?;
				symtab.push(name);
			}
		}

		for shdr in sections_by_name.values() {
			// @TODO @FIX we only process relocations relating to .symtab currently.
			match self.sections.get(shdr.link as usize) {
				None => continue,
				Some(h) => {
					if self.get_shstrtab(reader, h.name)? != ".symtab" {
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

			let info_section_offset = self
				.sections
				.get(shdr.info as usize)
				.ok_or(BadLink(shdr.info as u64))?
				.offset as u64;

			let add_relocation_x86 =
				|me: &mut Self, offset: u32, info: u32, addend: i32| -> Result<(), ElfError> {
					me.add_relocation_x86(
						&symtab,
						&addr_map,
						source_id,
						info_section_offset + offset as u64,
						info,
						addend,
					)
				};

			match shdr.r#type {
				elf::SHT_RELA => {
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
				elf::SHT_REL => {
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

	fn symbol_name_str(&self, id: SymbolName) -> &str {
		self.symbol_names.get_str(id).unwrap_or("???")
	}

	fn emit_warning(&self, warning: LinkWarning) {
		(self.warn)(warning);
	}

	fn emit_warning_rel_sym_not_found(&self, source: SourceId, name: SymbolName) {
		let warn = LinkWarning::RelSymNotFound {
			source: self.source_name(source).into(),
			name: self.symbol_name_str(name).into(),
		};
		self.emit_warning(warn);
	}

	// get symbol ID, producing a warning if it does not exist.
	fn get_symbol_id(&self, source_id: SourceId, name: SymbolName) -> Option<SymbolId> {
		// @TODO: don't warn about the same symbol twice
		let sym = self.symbols.get_id_from_name(source_id, name);
		if sym.is_none() {
			self.emit_warning_rel_sym_not_found(source_id, name);
		}
		sym
	}

	// generates a string like main.c:some_function
	fn symbol_id_location_string(&self, id: SymbolId) -> String {
		if let Some((source, name)) = self.symbols.get_location_from_id(id) {
			return format!(
				"{}:{}",
				self.source_name(source),
				self.symbol_name_str(name)
			);
		}
		"???".into()
	}

	fn get_symbol_value(&self, sym: SymbolId) -> Option<u64> {
		let info = self.symbols.get_info_from_id(sym)?;
		use SymbolValue::*;
		match (&info.value).as_ref()? {
			Data(_) => self.symbol_addrs.get(&sym).map(|r| *r),
			Bss(x) => Some(self.bss_addr + *x),
			Absolute(a) => Some(*a),
		}
	}

	fn get_relocation_data(
		&self,
		rel: &Relocation,
		pc: u64,
		data: &mut [u8; MAX_REL_SIZE],
	) -> Result<usize, LinkError> {
		//		use RelocationType::*;

		let symbol = match self.get_symbol_id(rel.source_id, rel.sym) {
			None => return Ok(0), // we emitted a warning in get_symbol_id
			Some(sym) => sym,
		};

		let symbol_value = match self.get_symbol_value(symbol) {
			None => {
				self.emit_warning(LinkWarning::RelNoValue(self.symbol_id_location_string(symbol)));
				return Ok(0)
			},
			Some(v) => v,
		};
		
		let addend = rel.addend;
		
		enum Value {
			U32(u32),
		}
		use Value::*;
		use RelocationType::*;
		
		let value = match rel.r#type {
			Direct32 => U32(symbol_value as u32 + addend as u32),
			Pc32 => U32(symbol_value as u32 + addend as u32 - pc as u32),
			_ => todo!(),
		};
		
		match value {
			U32(u) => {
				(&mut data[..4]).copy_from_slice(&u32::to_le_bytes(u));
				Ok(4)
			},
		}
	}

	fn apply_relocation(&mut self, rel: Relocation) -> Result<(), LinkError> {
		let apply_symbol = rel.r#where.0;
		let apply_offset = rel.r#where.1;

		let apply_addr = match self.symbol_addrs.get(&apply_symbol) {
			None => return Ok(()), // this relocation isn't in a section we care about
			Some(a) => *a,
		};

		let mut rel_data = [0; MAX_REL_SIZE];
		let rel_data_size = self.get_relocation_data(&rel, apply_addr, &mut rel_data)?;
		let rel_data = &rel_data[..rel_data_size];

		let apply_symbol_info = match self.symbols.get_mut_info_from_id(apply_symbol) {
			Some(info) => info,
			None => {
				// this shouldn't happen.
				self.emit_warning_rel_sym_not_found(rel.source_id, rel.sym);
				return Ok(());
			}
		};

		use SymbolValue::*;
		let mut oob = false;
		match &mut apply_symbol_info.value {
			Some(Data(data)) => {
				let apply_start = apply_offset as usize;
				let apply_end = apply_start + rel_data.len();
				if apply_end < apply_start || apply_end > data.len() {
					oob = true;
				} else {
					(&mut data[apply_start..apply_end]).copy_from_slice(rel_data);
				}
			}
			_ => {
				self.emit_warning(LinkWarning::RelNoData(
					self.source_name(rel.source_id).into(),
					rel.source_offset,
				));
			}
		}

		if oob {
			// prevent double mut borrow by moving this here
			self.emit_warning(LinkWarning::RelOOB(
				self.symbol_id_location_string(apply_symbol),
				apply_offset,
			));
		}

		Ok(())
	}

	// we don't want to link unused symbols.
	// we start by calling this on the entry function, then it recursively calls itself for each symbol used.
	pub fn add_data_for_symbol(
		&mut self,
		data: &mut Vec<u8>,
		symbol_graph: &SymbolGraph,
		id: SymbolId,
	) -> Result<(), LinkError> {
		// deal with cycles
		if self.symbol_addrs.contains_key(&id) {
			return Ok(());
		}
		self.symbol_addrs
			.insert(id, self.data_addr + (data.len() as u64));
		for reference in symbol_graph.get(&id).unwrap_or(&vec![]) {
			self.add_data_for_symbol(data, symbol_graph, *reference)?;
		}

		Ok(())
	}

	pub fn link<T: Write>(&mut self, out: &mut BufWriter<T>) -> Result<(), LinkError> {
		let mut symbol_graph = SymbolGraph::with_capacity(self.symbols.count());

		let relocations = mem::take(&mut self.relocations);

		// compute symbol graph
		for rel in relocations.iter() {
			use std::collections::hash_map::Entry;
			if let Some(symbol) = self.get_symbol_id(rel.source_id, rel.sym) {
				let apply_symbol = rel.r#where.0;
				match symbol_graph.entry(apply_symbol) {
					Entry::Occupied(mut o) => {
						o.get_mut().push(symbol);
					}
					Entry::Vacant(v) => {
						v.insert(vec![symbol]);
					}
				}
			}
		}

		let symbol_graph = symbol_graph; // no more mutating

		let segment_addr: u32 = 0x400000;

		let data_size = 0;

		let mut header = elf::Header32::default();
		let ehdr_size: u32 = header.ehsize.into();
		let phdr_size: u32 = header.phentsize.into();
		let header_size = ehdr_size + phdr_size;
		let file_size = header_size + data_size;
		let entry_point = segment_addr + header_size;
		header.phnum = 1;
		header.phoff = ehdr_size;
		header.entry = entry_point;
		out.write_all(&header.to_bytes())?;

		let data_addr = segment_addr + header_size;
		self.data_addr = data_addr.into();
		let bss_addr = segment_addr + file_size;
		self.bss_addr = bss_addr.into();
		let bss_size: u32 = self.bss_size.try_into().map_err(|_| LinkError::TooLarge)?;

		let entry_name_str = "entry";
		let entry_name_id = self
			.symbol_names
			.get(entry_name_str)
			.ok_or_else(|| LinkError::NoEntry(entry_name_str.into()))?;
		let entry_id = self
			.symbols
			.get_id_from_name(SourceId::NONE, entry_name_id)
			.ok_or_else(|| LinkError::EntryNotDefined(entry_name_str.into()))?;

		let mut data = vec![];
		self.add_data_for_symbol(&mut data, &symbol_graph, entry_id)?;

		for rel in relocations {
			self.apply_relocation(rel)?;
		}

		let phdr = elf::Phdr32 {
			flags: 0b111, // read, write, execute
			offset: 0,
			vaddr: segment_addr,
			filesz: file_size,
			memsz: file_size + bss_size,
			..Default::default()
		};
		out.write_all(&phdr.to_bytes())?;

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
		if let Err(e) = linker.process_object(filename, &mut file) {
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
