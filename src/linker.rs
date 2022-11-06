use crate::{elf, util};
use io::{BufRead, Seek, Write};
use std::collections::{BTreeMap, HashMap};
use std::{fmt, io, mem, fs, path};

use elf::ToBytes;
use elf::Reader as ELFReader;
use util::u32_from_le_slice;

pub enum LinkError {
	IO(io::Error),
	TooLarge,
	NoEntry(String),         // no entry point
	EntryNotDefined(String), // entry point is declared, but not defined
}

type LinkResult<T> = Result<T, LinkError>;

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
	RelUnsupported(u8),
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
				"relocation {source}+0x{offset:x} not in a data/text section. it will be ignored."
			),
			RelNoValue(name) => write!(f, "can't figure out value of symbol '{name}' (relocation ignored)."),
			RelUnsupported(x) => write!(f, "Unsupported relocation type {x} (relocation ignored)."),
		}
	}
}

impl From<&LinkWarning> for String {
	fn from(e: &LinkWarning) -> Self {
		format!("{e}")
	}
}

pub enum ObjectError {
	Elf(elf::Error),
	BadType,
	BadUtf8,
	BadSymtab,
	BadLink(u64),
	BadRelHeader,
	UnsupportedRelocation(u8),
	BadSymIdx(u64),
	NoStrtab,
}

impl From<elf::Error> for ObjectError {
	fn from(e: elf::Error) -> Self {
		Self::Elf(e)
	}
}

impl From<&ObjectError> for String {
	fn from(e: &ObjectError) -> String {
		format!("{e}")
	}
}

impl fmt::Display for ObjectError {
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		use ObjectError::*;
		match self {
			// Display for UnexpectedEof *should* be this but is less clear
			//  ("failed to fill whole buffer")
			Elf(e) => write!(f, "{e}"),
			BadType => write!(f, "wrong type of ELF file (not an object file)"),
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
		self.by_string.get(name).copied()
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
#[allow(dead_code)] // @TODO @TEMPORARY
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
	r#type: elf::SymbolType,
	value: Option<SymbolValue>,
	size: u64,
}

struct Symbols {
	info: Vec<SymbolInfo>,
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
			.copied()
	}

	fn get_location_from_id(&self, id: SymbolId) -> Option<(SourceId, SymbolName)> {
		self.locations.get(&id).copied()
	}

	fn count(&self) -> usize {
		self.info.len()
	}
}

#[derive(Debug, Clone)]
struct Relocation {
	r#where: (SymbolId, u64), // (symbol containing relocation, offset in symbol where relocation needs to be applied)
	source_id: SourceId,
	sym: SymbolName,
	r#type: elf::RelType,
	addend: i64,
}

pub struct Linker {
	symbols: Symbols,
	symbol_names: SymbolNames,
	relocations: Vec<Relocation>,
	undefined_relocations: Vec<Relocation>, // library relocations
	sources: Vec<String>, // object files
	libraries: Vec<String>,
	bss_size: u64,                               // output bss size
	bss_addr: u64,                               // output bss address
	data_addr: u64,                              // output data address
	symbol_data_offsets: HashMap<SymbolId, u64>, // for symbols with data, this holds the offsets into the data segment.
	warn: fn(LinkWarning),
}

// this maps between offsets in an object file and symbols defined in that file.
// this is used to figure out where relocations are taking place.
struct SymbolOffsetMap {
	map: BTreeMap<(u64, u64), SymbolId>,
}

impl SymbolOffsetMap {
	fn new() -> Self {
		SymbolOffsetMap {
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

struct Executable {
	interp: Vec<u8>,
	load_addr: u64,
	bss: Option<(u64, u64)>,
	relocations: Vec<(Relocation, u64)>,
	strtab: Vec<u8>,
	symbol_strtab_offsets: HashMap<SymbolName, u64>,
	lib_strtab_offsets: Vec<u64>,
}

impl Executable {
	pub fn new(load_addr: u64) -> Self {
		Self {
			bss: None,
			load_addr,
			interp: vec![],
			relocations: vec![],
			lib_strtab_offsets: vec![],
			symbol_strtab_offsets: HashMap::new(),
			strtab: vec![0],
		}
	}

	pub fn set_bss(&mut self, addr: u64, size: u64) {
		self.bss = Some((addr, size));
	}

	pub fn set_interp(&mut self, interp: &str) {
		self.interp = interp.as_bytes().into();
		self.interp.push(b'\0');
	}

	fn add_string(&mut self, s: &str) -> u64 {
		let ret = self.strtab.len() as u64;
		self.strtab.extend(s.as_bytes());
		self.strtab.push(b'\0');
		ret
	}

	pub fn add_lib(&mut self, lib: &str) {
		let s = self.add_string(lib);
		self.lib_strtab_offsets.push(s);
	}

	pub fn add_relocation(&mut self, symbol_names: &SymbolNames, rel: &Relocation, addr: u64) {
		let name = rel.sym;

		if self.symbol_strtab_offsets.get(&name).is_none() {
			let s = symbol_names.get_str(name).unwrap();
			let offset = self.add_string(s);
			self.symbol_strtab_offsets.insert(name, offset);
		}
		self.relocations.push((rel.clone(), addr));
	}

	fn segment_count(&self) -> u16 {
		let mut count = 1 /*data*/;
		if !self.interp.is_empty() {
			count += 2 /*interp,dyntab*/;
		}
		if self.bss.is_some() {
			count += 1 /*bss*/;
		}
		count
	}

	fn ph_offset(&self) -> u64 {
		elf::Ehdr32::size_of() as u64
	}

	fn ph_size(&self) -> u64 {
		elf::Phdr32::size_of() as u64 * u64::from(self.segment_count())
	}

	fn data_offset(&self) -> u64 {
		self.ph_offset() + self.ph_size()
	}

	pub fn data_addr(&self) -> u64 {
		self.load_addr + self.data_offset()
	}

	pub fn write<T: Write + Seek>(&self, data: &[u8], mut out: T) -> LinkResult<()> {
		let load_addr = self.load_addr as u32;

		// start by writing data.
		out.seek(io::SeekFrom::Start(self.data_offset()))?;
		out.write_all(data)?;

		let mut interp_offset = 0;
		let mut dyntab_offset = 0;
		let mut interp_size = 0;
		let mut dyntab_size = 0;
		if !self.interp.is_empty() {
			// now interp
			interp_offset = out.stream_position()?;
			out.write_all(&self.interp)?;
			interp_size = self.interp.len() as u32;
			// now strtab
			let strtab_offset = out.stream_position()?;
			out.write_all(&self.strtab)?;
			// now symtab
			let symtab_offset = out.stream_position()?;
			let null_symbol = [0; mem::size_of::<elf::Sym32>()];
			out.write_all(&null_symbol)?;
			let mut symbols: HashMap<SymbolName, u32> = HashMap::new();
			for (i, (sym, strtab_offset)) in self.symbol_strtab_offsets.iter().enumerate() {
				symbols.insert(*sym, (i + 1) as u32);
				// @TODO: allow STT_OBJECT as fell
				let sym = elf::Sym32 {
					name: *strtab_offset as u32,
					info: elf::STB_GLOBAL << 4 | elf::STT_FUNC,
					value: 0,
					size: 0,
					other: 0,
					shndx: 0,
				};
				out.write_all(&sym.to_bytes())?;
			}
			// now reltab
			let reltab_offset = out.stream_position()?;
			for (reloc, addr) in self.relocations.iter() {
				let index = *symbols.get(&reloc.sym).unwrap();
				let rel = elf::Rel32 {
					offset: *addr as u32,
					info: index << 8 | u32::from(reloc.r#type.to_x86_u8().unwrap()),
				};
				out.write_all(&rel.to_bytes())?;
			}
			let reltab_size = out.stream_position()? - reltab_offset;
			// now hash
			let hashtab_offset = out.stream_position()?;
			// put everything in a single bucket
			let nsymbols = symbols.len() as u32;
			out.write_all(&u32::to_le_bytes(1))?; // nbucket
			out.write_all(&u32::to_le_bytes(nsymbols + 1))?; // nchain
			out.write_all(&u32::to_le_bytes(0))?; // bucket begins at 0
									  // chain 1 -> 2 -> 3 -> ... -> n -> 0
			for i in 1..nsymbols {
				out.write_all(&u32::to_le_bytes(i))?;
			}
			out.write_all(&u32::to_le_bytes(0))?;
			// i don't know why this needs to be here.
			out.write_all(&u32::to_le_bytes(0))?;

			// now dyntab
			dyntab_offset = out.stream_position()?;
			let mut dyn_data = vec![
				elf::DT_RELSZ,
				reltab_size as u32,
				elf::DT_RELENT,
				8,
				elf::DT_REL,
				load_addr + reltab_offset as u32,
				elf::DT_STRSZ,
				self.strtab.len() as u32,
				elf::DT_STRTAB,
				load_addr + strtab_offset as u32,
				elf::DT_SYMENT,
				16,
				elf::DT_SYMTAB,
				load_addr + symtab_offset as u32,
				elf::DT_HASH,
				load_addr + hashtab_offset as u32,
			];
			for lib in &self.lib_strtab_offsets {
				dyn_data.extend([elf::DT_NEEDED, *lib as u32]);
			}
			dyn_data.extend([elf::DT_NULL, 0]);
			let mut dyn_bytes = Vec::with_capacity(dyn_data.len() * 4);
			for x in dyn_data {
				dyn_bytes.extend(u32::to_le_bytes(x));
			}
			dyntab_size = dyn_bytes.len() as u32;
			out.write_all(&dyn_bytes)?;
		}

		let file_size: u32 = out
			.stream_position()?
			.try_into()
			.map_err(|_| LinkError::TooLarge)?;

		out.seek(io::SeekFrom::Start(0))?;

		let ehdr = elf::Ehdr32 {
			phnum: self.segment_count(),
			phoff: elf::Ehdr32::size_of() as u32,
			entry: self
				.data_addr()
				.try_into()
				.map_err(|_| LinkError::TooLarge)?,
			..Default::default()
		};
		out.write_all(&ehdr.to_bytes())?;

		let phdr_data = elf::Phdr32 {
			flags: elf::PF_R | elf::PF_W | elf::PF_X, // read, write, execute
			offset: 0,
			vaddr: load_addr,
			filesz: file_size,
			memsz: file_size,
			..Default::default()
		};
		out.write_all(&phdr_data.to_bytes())?;

		if let Some((bss_addr, bss_size)) = self.bss {
			// for some reason, linux doesn't like executables
			// with memsz > filesz != 0
			// so we need two segments.
			let bss_size: u32 = bss_size.try_into().map_err(|_| LinkError::TooLarge)?;
			let phdr_bss = elf::Phdr32 {
				flags: elf::PF_R | elf::PF_W, // read, write
				offset: 0,
				vaddr: bss_addr as u32,
				filesz: 0,
				memsz: bss_size as u32,
				..Default::default()
			};
			out.write_all(&phdr_bss.to_bytes())?;
		}

		if !self.interp.is_empty() {
			let phdr_interp = elf::Phdr32 {
				r#type: elf::PT_INTERP,
				flags: elf::PF_R,
				offset: interp_offset as u32,
				vaddr: load_addr + interp_offset as u32,
				filesz: interp_size as u32,
				memsz: interp_size as u32,
				align: 1,
				..Default::default()
			};
			out.write_all(&phdr_interp.to_bytes())?;

			let phdr_dynamic = elf::Phdr32 {
				r#type: elf::PT_DYNAMIC,
				flags: elf::PF_R,
				offset: dyntab_offset as u32,
				vaddr: load_addr + dyntab_offset as u32,
				filesz: dyntab_size as u32,
				memsz: dyntab_size as u32,
				align: 1,
				..Default::default()
			};
			out.write_all(&phdr_dynamic.to_bytes())?;
		}

		Ok(())
	}
}

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
			bss_addr: 0,
			bss_size: 0,
			data_addr: 0,
			relocations: vec![],
			undefined_relocations: vec![],
			sources: vec![],
			libraries: vec![],
			symbol_data_offsets: HashMap::new(),
			warn: Self::default_warn_handler,
		}
	}

	fn source_name(&self, id: SourceId) -> &str {
		&self.sources[id.0 as usize]
	}

	fn add_symbol(
		&mut self,
		source: SourceId,
		elf: &elf::Reader32LE,
		offset_map: &mut SymbolOffsetMap,
		symbol: &elf::Symbol,
	) -> Result<(), ObjectError> {
		let mut data_offset = None;
		let name = elf.symbol_name(symbol)?;
		let name_id = self.symbol_names.add(name);

		let value = match symbol.value {
			elf::SymbolValue::Undefined => None,
			elf::SymbolValue::Absolute(n) => Some(SymbolValue::Absolute(n)),
			elf::SymbolValue::SectionOffset(shndx, offset) => {
				match elf.section_type(shndx) {
					Some(elf::SectionType::ProgBits) => {
						let mut data = vec![0; symbol.size as usize];
						data_offset = Some(elf.section_offset(shndx).unwrap() + offset);
						elf.read_section_data_exact(shndx, offset, &mut data)?;
						Some(SymbolValue::Data(data))
					},
					Some(elf::SectionType::NoBits) => {
						let p = self.bss_size;
						self.bss_size += symbol.size;
						Some(SymbolValue::Bss(p))
					},
					_ => None, // huh
				}
			}
		};

		let info = SymbolInfo {
			r#type: symbol.r#type,
			value,
			size: symbol.size,
		};
		let symbol_id = match symbol.bind {
			elf::SymbolBind::Local => self.symbols.add_local(source, name_id, info),
			elf::SymbolBind::Global => self.symbols.add_global(source, name_id, info),
			elf::SymbolBind::Weak => self.symbols.add_weak(source, name_id, info),
			_ => return Ok(()), // eh
		};

		if let Some(offset) = data_offset {
			offset_map.add_symbol(offset, symbol.size, symbol_id);
		}
		Ok(())
	}

	/// add an object file (.o).
	/// name doesn't need to correspond to the actual file name.
	/// it only exists for debugging purposes.
	pub fn add_object<T: BufRead + Seek>(
		&mut self,
		name: &str,
		reader: T,
	) -> Result<(), ObjectError> {
		use ObjectError::*;

		let mut offset_map = SymbolOffsetMap::new();

		let source_id = SourceId(self.sources.len() as _);
		self.sources.push(name.into());

		let elf = elf::Reader32LE::new(reader)?;
		if elf.r#type() != elf::Type::Rel {
			return Err(BadType);
		}
		
		for symbol in elf.symbols() {
			self.add_symbol(source_id, &elf, &mut offset_map, symbol)?;
		}
		
		for rel in elf.relocations() {
			if let Some(r#where) = offset_map.get(rel.offset) {
				let sym = self.symbol_names.add(elf.symbol_name(&rel.symbol)?);
				self.relocations.push(Relocation {
					r#where,
					source_id,
					sym,
					r#type: rel.r#type,
					addend: rel.addend,
				});
			} else {
				self.emit_warning(LinkWarning::RelNoData(
					self.source_name(source_id).into(),
					rel.entry_offset
				));
			}
		}

		Ok(())
	}
	
	pub fn add_library(&mut self, name: &str) -> Result<(), ObjectError> {
		self.libraries.push(name.into());
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
		match info.value.as_ref()? {
			Data(_) => self
				.symbol_data_offsets
				.get(&sym)
				.map(|&o| o + self.data_addr),
			Bss(x) => Some(self.bss_addr + *x),
			Absolute(a) => Some(*a),
		}
	}

	fn get_rel_apply_data_offset(&self, rel: &Relocation) -> Option<u64> {
		let apply_symbol = rel.r#where.0;
		let r = self.symbol_data_offsets.get(&apply_symbol)?;
		Some(*r + rel.r#where.1)
	}

	fn apply_relocation(&mut self, rel: Relocation, data: &mut [u8]) -> Result<(), LinkError> {
		let apply_symbol = rel.r#where.0;
		let apply_offset = match self.get_rel_apply_data_offset(&rel) {
			Some(data_offset) => data_offset,
			None => return Ok(()), // this relocation isn't in a data section so there's nothing we can do about it
		};
		let pc = apply_offset + self.data_addr;

		let symbol = match self.get_symbol_id(rel.source_id, rel.sym) {
			None => return Ok(()), // we emitted a warning in get_symbol_id
			Some(sym) => sym,
		};

		let symbol_value = match self.get_symbol_value(symbol) {
			None => {
				// this symbol is defined in a library
				//self.emit_warning(LinkWarning::RelNoValue(self.symbol_id_location_string(symbol)));
				self.undefined_relocations.push(rel);
				return Ok(());
			}
			Some(v) => v,
		};

		let addend = rel.addend;

		enum Value {
			U32(u32),
		}
		use elf::RelType::*;
		use Value::*;

		let value = match rel.r#type {
			Direct32 => U32(symbol_value as u32 + addend as u32),
			Pc32 => U32(symbol_value as u32 + addend as u32 - pc as u32),
			Other(x) => {self.emit_warning(LinkWarning::RelUnsupported(x)); return Ok(()) },
		};

		let apply_symbol_info = match self.symbols.get_mut_info_from_id(apply_symbol) {
			Some(info) => info,
			None => {
				// this shouldn't happen.
				self.emit_warning_rel_sym_not_found(rel.source_id, rel.sym);
				return Ok(());
			}
		};

		use SymbolValue::*;

		// guarantee failure if apply_offset can't be converted to usize.
		let apply_start = apply_offset.try_into().unwrap_or(usize::MAX - 32);

		match apply_symbol_info.value {
			Some(Data(_)) => {
				let mut in_bounds = true;
				match value {
					U32(u) => {
						if let Some(apply_to) = data.get_mut(apply_start..apply_start + 4) {
							let curr_val = u32_from_le_slice(apply_to);
							apply_to.copy_from_slice(&(u + curr_val).to_le_bytes());
						} else {
							in_bounds = false;
						}
					}
				};

				if !in_bounds {
					self.emit_warning(LinkWarning::RelOOB(
						self.symbol_id_location_string(apply_symbol),
						apply_offset,
					));
				}
			}
			_ => {
				self.emit_warning(LinkWarning::RelNoData(
					self.source_name(rel.source_id).into(),
					apply_offset,
				));
			}
		}

		Ok(())
	}
	
	/// "easy" input API.
	/// infers the file type of input, and calls the appropriate function (e.g. `add_object`)
	/// if there return value is `Err(s)`, `s` will be a nicely formatted error string.
	pub fn add_input(&mut self, input: &str) -> Result<(), String> {
		enum FileType {
			Object,
			DynamicLibrary,
			Other
		}
		
		use FileType::*;
		
		fn file_type(input: &str) -> FileType {
			if input.ends_with(".o") {
				return Object;
			}
			if input.ends_with(".so") {
				return DynamicLibrary;
			}
			if input.find(".so.").is_some() {
				// e.g. libc.so.6, some_library.so.12.7.3
				return DynamicLibrary;
			}
			Other
		}
		
		match file_type(input) {
			Object => {
				let file = fs::File::open(input)
					.map_err(|e| format!("Error opening {input}: {e}"))?;
				let mut file = io::BufReader::new(file);
				self.add_object(input, &mut file)
					.map_err(|e| format!("Error processing object file {input}: {e}"))
			},
			DynamicLibrary => {
				self.add_library(input)
					.map_err(|e| format!("Error processing library file {input}: {e}"))
			},
			Other => {
				Err(format!("Unrecognized file type: {input}"))
			}
		}
	}


	// we don't want to link unused symbols.
	// we start by calling this on the entry function, then it recursively calls itself for each symbol used.
	fn add_data_for_symbol(
		&mut self,
		data: &mut Vec<u8>,
		symbol_graph: &SymbolGraph,
		id: SymbolId,
	) -> Result<(), LinkError> {
		// deal with cycles
		if self.symbol_data_offsets.contains_key(&id) {
			return Ok(());
		}

		if let Some(info) = self.symbols.get_info_from_id(id) {
			if let Some(SymbolValue::Data(d)) = &info.value {
				// set address
				self.symbol_data_offsets.insert(id, data.len() as u64);
				// add data
				data.extend(d);
			}
		}

		for reference in symbol_graph.get(&id).unwrap_or(&vec![]) {
			self.add_data_for_symbol(data, symbol_graph, *reference)?;
		}

		Ok(())
	}

	pub fn link<T: Write + Seek>(mut self, out: T, entry: &str) -> LinkResult<()> {
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

		let mut exec = Executable::new(0x400000);
		self.bss_addr = 0x50000000;
		exec.set_bss(self.bss_addr, self.bss_size);
		exec.set_interp("/lib/ld-linux.so.2");
		for lib in self.libraries.iter() {
			exec.add_lib(lib);
		}
		
		self.data_addr = exec.data_addr();

		let entry_name_id = self
			.symbol_names
			.get(entry)
			.ok_or_else(|| LinkError::NoEntry(entry.into()))?;
		let entry_id = self
			.symbols
			.get_id_from_name(SourceId::NONE, entry_name_id)
			.ok_or_else(|| LinkError::EntryNotDefined(entry.into()))?;

		let mut data = vec![];
		self.add_data_for_symbol(&mut data, &symbol_graph, entry_id)?;

		for rel in relocations {
			self.apply_relocation(rel, &mut data)?;
		}

		for rel in mem::take(&mut self.undefined_relocations) {
			if let Some(data_offset) = self.get_rel_apply_data_offset(&rel) {
				exec.add_relocation(&self.symbol_names, &rel, self.data_addr + data_offset);
			}
		}

		exec.write(&data, out)
	}
	
	/// "easy" linking API.
	pub fn link_to_file<P: AsRef<path::Path>>(self, path: P, entry: &str) -> Result<(), String> {
		let path = path.as_ref();
		let mut out_options = fs::OpenOptions::new();
		out_options
			.write(true)
			.create(true)
			.truncate(true);
		#[cfg(unix)]
		{
			use std::os::unix::fs::OpenOptionsExt;
			out_options.mode(0o755);
		}
		
		let output = out_options.open(path)
			.map_err(|e| format!("Error opening output file {}: {e}", path.to_string_lossy()))?;
		let mut output = io::BufWriter::new(output);
	
		self.link(&mut output, entry)
			.map_err(|e| format!("Error linking {}: {e}", path.to_string_lossy()))
	}
}