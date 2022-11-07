/*!
Linker producing small executables.
Smallness is the *only* goal.
This linker makes "bad" executables in many ways. For example,
all initialized data will be executable. All code will be writable.
You shouldn't use this unless all you want is a tiny little executable file.

Currently, only 32-bit ELF is supported.
If you are using C, you will need `gcc-multilib` for the 32-bit headers.

Position-independent code is NOT supported, and makes executables
larger anyways. Make sure you compile with `-fno-pic` or equivalent.

Example usage:
```
let mut linker = Linker::new();
linker.add_input("main.o")?;
linker.add_input("libc.so.6")?;
linker.link_to_file("a.out", "entry")?;
```

`.eh_frame` and any debugging information is ignored.
As such, the resulting executable will be difficult to debug and *C++ exceptions
may not work*. 
*/

use crate::elf;
use io::{BufRead, Seek, Write};
use std::collections::{BTreeMap, HashMap};
use std::{fmt, fs, io, mem, path};

use elf::Reader as ELFReader;
use elf::ToBytes;

pub enum LinkError {
	IO(io::Error),
	/// executable is too large (>4GB on 32-bit platforms)
	TooLarge,
	/// entry point not found
	NoEntry(String),
	/// entry point was declared, but not defined
	EntryNotDefined(String),
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
	/// unsupported relocation type
	RelUnsupported(u8),
	/// relocation is too large to fit inside its symbol
	RelOOB(String, u64),
	/// relocation does not take place in a symbol's data
	RelNoSym(String, u64),
}

impl fmt::Display for LinkWarning {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use LinkWarning::*;
		match self {
			RelOOB(text, offset) => write!(f, "relocation applied to {text}+0x{offset:x}, which goes outside of the symbol (it will be ignored)."),
			RelNoSym(source, offset) => write!(
				f,
				"relocation {source}+0x{offset:x} not in a data/text section. it will be ignored."
			),
			RelUnsupported(x) => write!(f, "Unsupported relocation type {x} (relocation ignored)."),
		}
	}
}

impl From<&LinkWarning> for String {
	fn from(e: &LinkWarning) -> Self {
		format!("{e}")
	}
}

/// error produced by [Linker::add_object]
pub enum ObjectError {
	/// ELF format error
	Elf(elf::Error),
	/// wrong type of ELF file
	BadType,
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
		}
	}
}

type SymbolNameType = u32;
/// To be more efficient™, we use integers to keep track of symbol names.
///
/// A `SymbolName` doesn't need to refer to a symbol which has been defined.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
struct SymbolName(SymbolNameType);
/// Keeps track of string-[SymbolName] conversion.
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

	fn get_str(&self, id: SymbolName) -> Option<&str> {
		self.to_string.get(id.0 as usize).map(|s| &s[..])
	}

	fn get(&self, name: &str) -> Option<SymbolName> {
		self.by_string.get(name).copied()
	}
}

/// A source is a file where symbols are defined (currently only object files).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct SourceId(u32);

impl SourceId {
	const NONE: Self = Self(u32::MAX);
}

type SymbolIdType = u32;

/// A symbol ID refers to a specific *definition* of a symbol.
///
/// There might be multiple `SymbolId`s corresponding to a single [SymbolName],
/// since local symbols with the same name can be defined in separate object files.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct SymbolId(SymbolIdType);

/// Value of a symbol.
#[derive(Debug)]
enum SymbolValue {
	/// offset into BSS section
	Bss(u64),
	/// Data associated with this symbol (machine code for functions,
	/// bytes making up string literals, etc.)
	Data(Vec<u8>),
	/// An absolute value. This corresponds to relocations with
	/// `shndx == SHN_ABS`.
	Absolute(u64),
}

/// Information about a defined symbol.
#[derive(Debug)]
struct SymbolInfo {
	value: SymbolValue,
}

/// information about all symbols in all sources
struct Symbols {
	/// `info[n]` = symbol info corresponding to ID #`n`
	info: Vec<SymbolInfo>,
	/// `locations[n]` = where symbol with ID `n` was defined + symbol name
	locations: Vec<(SourceId, SymbolName)>,
	/// all global symbols
	global: HashMap<SymbolName, SymbolId>,
	/// all weak symbols (weak symbols are like global symbols but have lower precedence)
	weak: HashMap<SymbolName, SymbolId>,
	/// all local symbols
	local: HashMap<(SourceId, SymbolName), SymbolId>,
}

impl Symbols {
	fn new() -> Self {
		Self {
			info: vec![],
			locations: vec![],
			global: HashMap::new(),
			weak: HashMap::new(),
			local: HashMap::new(),
		}
	}

	fn add_(&mut self, source: SourceId, name: SymbolName, info: SymbolInfo) -> SymbolId {
		let id = SymbolId(self.info.len() as _);
		self.info.push(info);
		self.locations.push((source, name));
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

	fn get_info_from_id(&self, id: SymbolId) -> &SymbolInfo {
		// Self::add_ is the only function that constructs SymbolIds.
		// unless someone uses a SymbolId across Symbols instances (why would you do that),
		// this should never panic.
		self.info.get(id.0 as usize).expect("bad symbol ID")
	}

	/// Get symbol ID from source and symbol name. The source ID is needed
	/// for local symbols -- to find a global/weak symbol with a given name,
	/// ignoring local symbols, you can pass in [SourceId::NONE].
	///
	/// The precedence rules according to ELF are: local then global then weak.
	///
	/// Returns `None` if the symbol hasn't been defined.
	fn get_id_from_name(&self, source: SourceId, name: SymbolName) -> Option<SymbolId> {
		self.local
			.get(&(source, name))
			.or_else(|| self.global.get(&name))
			.or_else(|| self.weak.get(&name))
			.copied()
	}

	fn get_location_from_id(&self, id: SymbolId) -> (SourceId, SymbolName) {
		*self.locations.get(id.0 as usize).expect("bad symbol ID")
	}

	/// Number of defined symbols.
	fn count(&self) -> usize {
		self.info.len()
	}
}

/// An ELF relocation.
#[derive(Debug, Clone)]
struct Relocation {
	/// (symbol containing relocation, offset in symbol where relocation needs to be applied)
	r#where: (SymbolId, u64),
	/// which source is asking for this relocation
	source_id: SourceId,
	/// symbol that needs to be supplied
	sym: SymbolName,
	r#type: elf::RelType,
	/// type of `sym`
	symbol_type: elf::SymbolType,
	addend: i64,
}

pub struct Linker<'a> {
	symbols: Symbols,
	symbol_names: SymbolNames,
	relocations: Vec<Relocation>,
	/// `sources[n]` = name of source corresponding to [SourceId]`(n)`.
	/// These aren't necessarily valid paths. They're just names
	/// we can use in error messages.
	sources: Vec<String>,
	/// dynamic libraries which have been added.
	libraries: Vec<String>,
	/// Output bss size.
	/// As more objects are added, this grows.
	bss_size: u64,
	/// Warning callback.
	warn: Box<dyn Fn(LinkWarning) + 'a>,
}

/// Maps between offsets in an object file and symbols defined in that file.
///
/// (Note: this is specific to a single object file, and only kept around temporarily
/// during a call to [Linker::add_object].)
/// This is used to figure out where relocations are taking place.
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

	/// returns (symbol, offset in symbol).
	/// e.g. a relocation might happen at `main+0x33`.
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

/// Graph of which symbols depend on which symbols.
///
/// This is needed so we don't emit anything for unused symbols.
struct SymbolGraph {
	graph: Vec<Vec<SymbolId>>,
}

impl SymbolGraph {
	fn new(symbol_count: usize) -> Self {
		Self {
			graph: vec![vec![]; symbol_count],
		}
	}

	fn add_dependency(&mut self, sym: SymbolId, depends_on: SymbolId) {
		self.graph
			.get_mut(sym.0 as usize)
			.expect("bad symbol ID")
			.push(depends_on);
	}

	fn get_dependencies(&self, sym: SymbolId) -> &[SymbolId] {
		self.graph.get(sym.0 as usize).expect("bad symbol ID")
	}
}

struct LinkerOutput {
	/// for symbols with data, this holds the offsets into the data segment.
	symbol_data_offsets: HashMap<SymbolId, u64>,
	interp: Vec<u8>,
	/// virtual address of big ol' section containing data + elf header + etc.
	load_addr: u64,
	/// .bss section address and size if there is one.
	bss: Option<(u64, u64)>,
	/// these bytes will make up the text+data section of our executable.
	data: Vec<u8>,
	/// array of (relocation, apply address).
	/// These are only relocations which weren't applied by the linker
	/// and need to be loaded from dynamic libraries.
	relocations: Vec<(Relocation, u64)>,
	/// contents of dynamic strtab.
	strtab: Vec<u8>,
	/// (offset into strtab, type) 
	/// Seems like no one sets the type of undefined symbols.
	/// Still, might as well pretend they do.
	dynsyms: HashMap<SymbolName, (u64, elf::SymbolType)>,
	/// array of stratb pointers to library names.
	lib_strtab_offsets: Vec<u64>,
}

impl LinkerOutput {
	pub fn new(load_addr: u64) -> Self {
		Self {
			symbol_data_offsets: HashMap::new(),
			bss: None,
			load_addr,
			data: vec![],
			interp: vec![],
			relocations: vec![],
			lib_strtab_offsets: vec![],
			dynsyms: HashMap::new(),
			strtab: vec![0],
		}
	}

	/// add a bss section, or replace the existing one.
	pub fn set_bss(&mut self, addr: u64, size: u64) {
		self.bss = Some((addr, size));
	}

	/// set the ELF interpreter (typically `/lib/ld-linux.so.2`)
	pub fn set_interp(&mut self, interp: &str) {
		self.interp = interp.as_bytes().into();
		self.interp.push(b'\0');
	}

	/// returns offset into strtab
	fn add_string(&mut self, s: &str) -> u64 {
		let ret = self.strtab.len() as u64;
		self.strtab.extend(s.as_bytes());
		self.strtab.push(b'\0');
		ret
	}

	/// add a dynamic library
	pub fn add_library(&mut self, lib: &str) {
		let s = self.add_string(lib);
		self.lib_strtab_offsets.push(s);
	}

	/// add a relocation (used for dynamic library relocations only)
	pub fn add_relocation(&mut self, symbol_names: &SymbolNames, rel: &Relocation, addr: u64) {
		let name = rel.sym;

		if self.dynsyms.get(&name).is_none() {
			let s = symbol_names.get_str(name).unwrap();
			let offset = self.add_string(s);
			self.dynsyms.insert(name, (offset, rel.symbol_type));
		}
		self.relocations.push((rel.clone(), addr));
	}

	/// number of segments in output ELF file, according to current information.
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

	/// offset of program headers
	fn ph_offset(&self) -> u64 {
		elf::Ehdr32::size_of() as u64
	}

	/// size of program headers
	fn ph_size(&self) -> u64 {
		elf::Phdr32::size_of() as u64 * u64::from(self.segment_count())
	}

	/// offset of data
	fn data_offset(&self) -> u64 {
		self.ph_offset() + self.ph_size()
	}

	/// virtual address of data
	pub fn data_addr(&self) -> u64 {
		self.load_addr + self.data_offset()
	}

	/// virtual address of bss
	pub fn bss_addr(&self) -> Option<u64> {
		self.bss.map(|(a, _)| a)
	}

	/// has a data symbol been added with this ID?
	pub fn is_data_symbol(&self, id: SymbolId) -> bool {
		self.symbol_data_offsets.contains_key(&id)
	}

	/// add some data to the executable, and associate it with the given symbol ID.
	pub fn add_data_symbol(&mut self, id: SymbolId, data: &[u8]) {
		// set address
		self.symbol_data_offsets.insert(id, self.data.len() as u64);
		// add data
		self.data.extend(data);
	}

	/// get offset in data section where relocation should be applied
	pub fn get_rel_data_offset(&self, rel: &Relocation) -> Option<u64> {
		let apply_symbol = rel.r#where.0;
		let r = self.symbol_data_offsets.get(&apply_symbol)?;
		Some(*r + rel.r#where.1)
	}

	/// get the actual value of a [SymbolValue]
	pub fn eval_symbol_value(&self, id: SymbolId, value: &SymbolValue) -> u64 {
		use SymbolValue::*;
		match value {
			Data(_) => {
				self.symbol_data_offsets
					.get(&id)
					.unwrap() // @TODO: can this panic?
					+ self.data_addr()
			}
			Bss(x) => {
				// this shouldn't panic, since we always generate a bss section
				// @TODO: make bss optional
				self.bss_addr().expect("no bss") + x
			}
			Absolute(a) => *a,
		}
	}

	/// output the executable.
	pub fn write(&self, mut out: impl Write + Seek) -> LinkResult<()> {
		let load_addr = self.load_addr as u32;

		// start by writing data.
		out.seek(io::SeekFrom::Start(self.data_offset()))?;
		out.write_all(&self.data)?;

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
			for (i, (sym, (strtab_offset, symbol_type))) in self.dynsyms.iter().enumerate() {
				symbols.insert(*sym, (i + 1) as u32);
				let sym = elf::Sym32 {
					name: *strtab_offset as u32,
					info: elf::STB_GLOBAL << 4 | u8::from(*symbol_type),
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

impl<'a> Linker<'a> {
	fn default_warning_handler(warning: LinkWarning) {
		eprintln!("warning: {warning}");
	}

	/// Set function to be called when there is a warning.
	/// By default, warnings are printed to stderr.
	pub fn set_warning_handler<T: Fn(LinkWarning) + 'a>(&mut self, warn: T) {
		self.warn = Box::new(warn);
	}

	pub fn new() -> Self {
		Linker {
			symbols: Symbols::new(),
			symbol_names: SymbolNames::new(),
			bss_size: 0,
			relocations: vec![],
			sources: vec![],
			libraries: vec![],
			warn: Box::new(Self::default_warning_handler),
		}
	}

	/// Get name of source file.
	fn source_name(&self, id: SourceId) -> &str {
		&self.sources[id.0 as usize]
	}

	/// add a symbol from a source file.
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
					}
					Some(elf::SectionType::NoBits) => {
						let p = self.bss_size;
						self.bss_size += symbol.size;
						Some(SymbolValue::Bss(p))
					}
					_ => None, // huh
				}
			}
		};

		if let Some(value) = value {
			let info = SymbolInfo { value };
			let symbol_id = match symbol.bind {
				elf::SymbolBind::Local => self.symbols.add_local(source, name_id, info),
				elf::SymbolBind::Global => self.symbols.add_global(source, name_id, info),
				elf::SymbolBind::Weak => self.symbols.add_weak(source, name_id, info),
				_ => return Ok(()), // eh
			};

			if let Some(offset) = data_offset {
				offset_map.add_symbol(offset, symbol.size, symbol_id);
			}
		}
		Ok(())
	}

	/// add an object file (.o).
	/// name doesn't need to correspond to the actual file name.
	/// it only exists for debugging purposes.
	pub fn add_object(
		&mut self,
		name: &str,
		reader: impl BufRead + Seek,
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
					symbol_type: rel.symbol.r#type,
					r#type: rel.r#type,
					addend: rel.addend,
				});
			} else {
				self.emit_warning(LinkWarning::RelNoSym(
					self.source_name(source_id).into(),
					rel.entry_offset,
				));
			}
		}

		Ok(())
	}

	/// Add a dynamic library (.so). `name` can be a full path or
	/// something like "libc.so.6" --- any string you would pass to `dlopen`.
	pub fn add_dynamic_library(&mut self, name: &str) -> Result<(), ObjectError> {
		self.libraries.push(name.into());
		Ok(())
	}

	/// Get name of symbol.
	fn symbol_name_str(&self, id: SymbolName) -> &str {
		self.symbol_names.get_str(id).unwrap_or("???")
	}

	/// Do a warning.
	fn emit_warning(&self, warning: LinkWarning) {
		(self.warn)(warning);
	}

	/// Get symbol ID from symbol name.
	/// Returns `None` if the symbol is not defined.
	fn get_symbol_id(&self, source_id: SourceId, name: SymbolName) -> Option<SymbolId> {
		self.symbols.get_id_from_name(source_id, name)
	}

	/// Generates a string like "main.c:some_function".
	fn symbol_id_location_string(&self, id: SymbolId) -> String {
		let (source, name) = self.symbols.get_location_from_id(id);
		format!(
			"{}:{}",
			self.source_name(source),
			self.symbol_name_str(name)
		)
	}

	/// Get value of symbol (e.g. ID of main → address of main).
	fn get_symbol_value(&self, exec: &LinkerOutput, sym: SymbolId) -> u64 {
		let info = self.symbols.get_info_from_id(sym);
		exec.eval_symbol_value(sym, &info.value)
	}

	/// Apply relocation to executable.
	fn apply_relocation(&self, exec: &mut LinkerOutput, rel: &Relocation) -> LinkResult<()> {
		let apply_symbol = rel.r#where.0;
		let apply_offset = match exec.get_rel_data_offset(rel) {
			Some(data_offset) => data_offset,
			None => {
				// this relocation isn't in a data section so there's nothing we can do about it
				return Ok(());
			}
		};
		let pc = apply_offset + exec.data_addr();

		let symbol = match self.get_symbol_id(rel.source_id, rel.sym) {
			None => {
				// symbol not defined. it should come from a library.
				exec.add_relocation(&self.symbol_names, rel, exec.data_addr() + apply_offset);
				return Ok(());
			}
			Some(sym) => sym,
		};

		let symbol_value = self.get_symbol_value(exec, symbol);

		let addend = rel.addend;

		enum Value {
			U32(u32),
		}
		use elf::RelType::*;
		use Value::*;

		let value = match rel.r#type {
			Direct32 => U32(symbol_value as u32 + addend as u32),
			Pc32 => U32(symbol_value as u32 + addend as u32 - pc as u32),
			Other(x) => {
				self.emit_warning(LinkWarning::RelUnsupported(x));
				return Ok(());
			}
		};

		let apply_symbol_info = self.symbols.get_info_from_id(apply_symbol);

		use SymbolValue::*;

		// guarantee failure if apply_offset can't be converted to usize.
		let apply_start = apply_offset.try_into().unwrap_or(usize::MAX - 1000);

		fn u32_from_le_slice(data: &[u8]) -> u32 {
			u32::from_le_bytes([data[0], data[1], data[2], data[3]])
		}
		

		match apply_symbol_info.value {
			Data(_) => {
				let mut in_bounds = true;
				match value {
					U32(u) => {
						if let Some(apply_to) = exec.data.get_mut(apply_start..apply_start + 4) {
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
				self.emit_warning(LinkWarning::RelNoSym(
					self.source_name(rel.source_id).into(),
					apply_offset,
				));
			}
		}

		Ok(())
	}

	/// Easy input API.
	/// Infers the file type of input, and calls the appropriate function (e.g. [Self::add_object]).
	pub fn add_input(&mut self, input: &str) -> Result<(), String> {
		enum FileType {
			Object,
			DynamicLibrary,
			Other,
		}

		use FileType::*;

		fn file_type(input: &str) -> FileType {
			if input.ends_with(".o") {
				return Object;
			}
			if input.ends_with(".so") {
				return DynamicLibrary;
			}
			if input.contains(".so.") {
				// e.g. libc.so.6, some_library.so.12.7.3
				return DynamicLibrary;
			}
			Other
		}

		match file_type(input) {
			Object => {
				let file =
					fs::File::open(input).map_err(|e| format!("Couldn't open {input}: {e}"))?;
				let mut file = io::BufReader::new(file);
				self.add_object(input, &mut file)
					.map_err(|e| format!("Failed to process object file {input}: {e}"))
			}
			DynamicLibrary => self
				.add_dynamic_library(input)
				.map_err(|e| format!("Failed to process library file {input}: {e}")),
			Other => Err(format!("Unrecognized file type: {input}")),
		}
	}

	/// Add data for a symbol.
	/// We don't want to link unused symbols.
	/// We start by calling this on the entry function,
	/// then it recursively calls itself for each symbol used.
	fn add_data_for_symbol(
		&self,
		exec: &mut LinkerOutput,
		symbol_graph: &SymbolGraph,
		id: SymbolId,
	) -> Result<(), LinkError> {
		// deal with cycles
		if exec.is_data_symbol(id) {
			return Ok(());
		}

		let info = self.symbols.get_info_from_id(id);
		if let SymbolValue::Data(d) = &info.value {
			exec.add_data_symbol(id, d);
		}

		for reference in symbol_graph.get_dependencies(id) {
			self.add_data_for_symbol(exec, symbol_graph, *reference)?;
		}

		Ok(())
	}

	/// Link everything together.
	pub fn link(&self, out: impl Write + Seek, entry: &str) -> LinkResult<()> {
		let mut symbol_graph = SymbolGraph::new(self.symbols.count());

		// compute symbol graph
		for rel in self.relocations.iter() {
			if let Some(symbol) = self.get_symbol_id(rel.source_id, rel.sym) {
				let apply_symbol = rel.r#where.0;
				symbol_graph.add_dependency(apply_symbol, symbol);
			}
		}

		let symbol_graph = symbol_graph; // no more mutating

		let mut exec = LinkerOutput::new(0x400000);
		exec.set_bss(0x70000000, self.bss_size);
		exec.set_interp("/lib/ld-linux.so.2");
		for lib in self.libraries.iter() {
			exec.add_library(lib);
		}

		let entry_name_id = self
			.symbol_names
			.get(entry)
			.ok_or_else(|| LinkError::NoEntry(entry.into()))?;
		let entry_id = self
			.symbols
			.get_id_from_name(SourceId::NONE, entry_name_id)
			.ok_or_else(|| LinkError::EntryNotDefined(entry.into()))?;

		self.add_data_for_symbol(&mut exec, &symbol_graph, entry_id)?;

		for rel in self.relocations.iter() {
			self.apply_relocation(&mut exec, rel)?;
		}

		exec.write(out)
	}

	/// Easy linking API. Just provide a path and the name of the entry function.
	///
	/// Important: don't just go writing a C program and defining `int main(int argc, char **argv)`.
	/// Instead, define `void <main/entry/something_else>(void)`, and make sure you call `exit`,
	/// or do an exit system interrupt at the end of the function --- if you just return,
	/// you'll get a segmentation fault.
	pub fn link_to_file(&self, path: impl AsRef<path::Path>, entry: &str) -> Result<(), String> {
		let path = path.as_ref();
		let mut out_options = fs::OpenOptions::new();
		out_options.write(true).create(true).truncate(true);
		#[cfg(unix)]
		{
			use std::os::unix::fs::OpenOptionsExt;
			out_options.mode(0o755);
		}

		let output = out_options
			.open(path)
			.map_err(|e| format!("Error opening output file {}: {e}", path.to_string_lossy()))?;
		let mut output = io::BufWriter::new(output);

		self.link(&mut output, entry)
			.map_err(|e| format!("Error linking {}: {e}", path.to_string_lossy()))
	}
}

impl<'a> Default for Linker<'a> {
	fn default() -> Self {
		Self::new()
	}
}
