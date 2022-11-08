/*!
Linker producing small executables.

Smallness is the *only* goal.
This linker makes "bad" executables in many ways. For example,
all initialized data will be executable. All code will be writable.
There's no debugging information.
You shouldn't use this unless all you want is a tiny little executable file.

Currently, only 32-bit ELF is supported.

Position-independent code is NOT supported, and makes executables
larger anyways. Make sure you compile with `-fno-pic` or equivalent.

Example usage:
```
let mut linker = Linker::new();
linker.add_input("main.o")?;
linker.add_input("libc.so.6")?;
linker.add_input("libstdc++.so.6")?;
linker.link_to_file("a.out", "entry")?;
```

Notes about using C/C++:

- You need to call exit or do an exit syscall at the end of your entry function.
  Otherwise you will get a segfault/illegal instruction/etc:
```c
(extern "C") void entry() {
	...
	exit(0);
}
```
- You will need `gcc-multilib` for the 32-bit headers.

Notes about using C++:

- I recommend you do something like this:
```c
extern "C" void entry() {
	exit(main());
}
int main() {
	...
}
```
This ensures that all destructors are called for local objects in main.
- You will need `g++-multilib`.
- Exceptions may not work (since `.eh_frame` is stripped).
- If you want a small executable, it's best not to use the STL.
- For some reason, `std::cout` and `std::cin` don't work. If you can figure out why, please let me know.
  You can get around this with something like
```
std::ofstream cout("/dev/stdout");
std::ifstream cin("/dev/stdin");
```
or use `printf`, `scanf` for smaller executables.
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
	/// entry point defined, but has no data (e.g. `int entry[36];`)
	EntryNoData(String),
}

impl LinkError {
	/// convert `u` to `u32`, returning [LinkError::TooLarge] if it overflows.
	fn u64_to_u32(u: u64) -> LinkResult<u32> {
		u.try_into().map_err(|_| LinkError::TooLarge)
	}
	
	/// convert `u` to `u32`, returning [LinkError::TooLarge] if it overflows.
	fn usize_to_u32(u: usize) -> LinkResult<u32> {
		u.try_into().map_err(|_| LinkError::TooLarge)
	}
	
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
			EntryNoData(name) => write!(f, "entry point '{name}' has no data."),
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
	/// relocation is too large
	RelOOB(String, u64),
	/// relocation does not take place in a symbol's data
	RelNoSym(String, u64),
}

impl fmt::Display for LinkWarning {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use LinkWarning::*;
		match self {
			RelOOB(source, offset) => write!(f, "relocation {source}+0x{offset:x} goes outside of its section (it will be ignored)."),
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
	IO(io::Error),
	/// ELF format error
	Elf(elf::Error),
	/// wrong type of ELF file
	BadType,
	/// compile command failed
	CommandFailed(std::process::ExitStatus),
}

impl From<io::Error> for ObjectError {
	fn from(e: io::Error) -> Self {
		Self::IO(e)
	}
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
			IO(e) => write!(f, "{e}"),
			Elf(e) => write!(f, "{e}"),
			BadType => write!(f, "wrong type of ELF file (not an object file)"),
			CommandFailed(status) => write!(f, "command failed: {status}"),
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
	/// this symbol has data in `source` at `offset..offset+size`
	Data { source: SourceId, offset: u64, size: u64 },
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
		let id = SymbolId(self.info.len().try_into().expect("too many symbols wtf is wrong with you"));
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
}

/// An ELF relocation.
#[derive(Debug, Clone)]
struct Relocation {
	/// (source containing relocation, offset in source where it should be applied)
	r#where: (SourceId, u64),
	/// symbol that needs to be supplied
	sym: SymbolName,
	r#type: elf::RelType,
	/// type of `sym`
	symbol_type: elf::SymbolType,
	addend: i64,
	/// relocation metadata offset (for debugging)
	#[cfg(debug_assertions)]
	#[allow(unused)]
	entry_offset: u64,
}

pub struct Linker<'a> {
	symbols: Symbols,
	symbol_names: SymbolNames,
	/// C compiler
	cc: String,
	/// C compiler flags
	cflags: Vec<String>,
	/// C++ compiler
	cxx: String,
	/// C++ compiler flags
	cxxflags: Vec<String>,
	/// `relocations[n][addr]` = relocation in source `n` at offset `addr`.
	relocations: Vec<BTreeMap<u64, Relocation>>,
	/// `sources[n]` = name of source corresponding to [SourceId]`(n)`.
	/// These aren't necessarily valid paths. They're just names
	/// we can use in error messages.
	sources: Vec<String>,
	/// all source data. yes we keep it all in memory.
	/// this is kind of needed since relocations can be little bitches and
	/// demand a negative addend on a symbol (get stuff in data section *before* symbol).
	source_data: Vec<Vec<u8>>,
	/// dynamic libraries which have been added.
	libraries: Vec<String>,
	/// Output bss size.
	/// As more objects are added, this grows.
	bss_size: u64,
	/// Warning callback.
	warn: Box<dyn Fn(LinkWarning) + 'a>,
}

#[derive(Clone)]
struct SourceRanges {
	/// keys are (offset, size).
	/// INVARIANT: ranges are disjoint, and
	/// non-adjacent (e.g. [5,10) + [10, 12) should be combined to [5, 12))
	map: BTreeMap<(u64, u64), u64>,
}

impl SourceRanges {
	fn new() -> Self {
		Self { map: BTreeMap::new() }
	}
	
	fn add(&mut self, start: u64, size: u64) -> bool {
		let mut l = start;
		let mut r = start + size;
		
		if let Some((&l_range, _)) = self.map.range(..=(l, u64::MAX)).last() {
			if l_range.0 + l_range.1 >= r {
				// [l, r) contained entirely inside l_range
				return false;
			}
			if l_range.0 + l_range.1 >= l {
				// extend left
				l = l_range.0;
				self.map.remove(&l_range);
			}
		}
		
		if let Some((&r_range, _)) = self.map.range((r, 0)..).next() {
			if r_range.0 <= r {
				// extend right
				r = r_range.0 + r_range.1;
				self.map.remove(&r_range);
			}
		}
		
		// delete subranges of [l,r)
		// (only subranges will overlap [l,r] now)
		// unfortunately there's no BTreeMap::drain yet.
		let mut keys = vec![];
		for (k, _) in self.map.range((l, 0)..=(r, u64::MAX)) {
			assert!(k.0 >= l && k.1 <= r);
			keys.push(*k);
		}
		for key in keys {
			self.map.remove(&key);
		}
		
		// insert [l,r)
		self.map.insert((l, r - l), 0);
		true
	}
	
	fn translate_offset(&self, offset: u64) -> Option<u64> {
		let (range, &out) = self.map.range(..=(offset, u64::MAX)).last()?;
		if offset >= range.0 && offset < range.0 + range.1 {
			Some(out + (offset - range.0))
		} else {
			None
		}
	}
	
	fn set_output_offsets(&mut self, size: &mut u64) {
		for (range, value) in self.map.iter_mut() {
			// we should only call this function once
			assert_eq!(*value, 0);
			
			*value = *size;
			*size += range.1;
		}
	}
}

// @TODO: doc
struct RangeSet {
	/// `ranges[i]` = ranges for source #`i`.
	ranges: Vec<SourceRanges>,
}

impl RangeSet {
	fn new(source_count: usize) -> Self {
		Self { ranges: vec![SourceRanges::new(); source_count] }
	}
	
	/// Returns true if the range is not redundant with the current ranges.
	fn add(&mut self, source: SourceId, start: u64, size: u64) -> bool {
		self.ranges[source.0 as usize].add(start, size)
	}
	
	fn to_map(mut self) -> OffsetMap {
		let mut size = 0u64;
		for range in self.ranges.iter_mut() {
			range.set_output_offsets(&mut size)
		}
		OffsetMap {
			size,
			ranges: mem::take(&mut self.ranges)
		}
	}
}

// @TODO: doc
struct OffsetMap {
	size: u64,
	ranges: Vec<SourceRanges>,
}

impl OffsetMap {
	fn translate_offset(&self, src: SourceId, offset: u64) -> Option<u64> {
		self.ranges[src.0 as usize].translate_offset(offset)
	}
	
	/// get offset in data section where relocation should be applied
	fn translate_rel_offset(&self, rel: &Relocation) -> Option<u64> {
		self.translate_offset(rel.r#where.0, rel.r#where.1)
	}
	
	fn size(&self) -> u64 {
		self.size
	}
	
	fn for_each(&self, mut f: impl FnMut(SourceId, u64, u64, u64)) {
		for (src, ranges) in self.ranges.iter().enumerate() {
			let src_id = SourceId(src.try_into().unwrap());
			for (&(offset, size), &dest_offset) in ranges.map.iter() {
				f(src_id, offset, size, dest_offset);
			}
		}
	}
}

struct LinkerOutput {
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
		elf::Ehdr32::size_of().into()
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
	
	/// set data section
	pub fn set_data(&mut self, data: Vec<u8>) {
		self.data = data;
	}


	/// get the actual value of a [SymbolValue]
	pub fn eval_symbol_value(&self, map: &OffsetMap, value: &SymbolValue) -> u64 {
		use SymbolValue::*;
		match value {
			Data { source, offset, .. } => {
				match map.translate_offset(*source, *offset) {
					// in theory, this should only be None when we emitted a warning
					// about a fucked up relocation
					None => return 0,
					Some(o) => o + self.data_addr(),
				}
			}
			Bss(x) => {
				// this shouldn't panic, since we always generate a bss section
				// if there are any BSS symbols.
				self.bss_addr().expect("no bss") + x
			}
			Absolute(a) => *a,
		}
	}

	/// output the executable.
	pub fn write(&self, mut out: impl Write + Seek, entry_point: u64) -> LinkResult<()> {
		let u64_to_u32 = LinkError::u64_to_u32;
		let usize_to_u32 = LinkError::usize_to_u32;
		
		fn stream_position32(out: &mut impl Seek) -> LinkResult<u32> {
			LinkError::u64_to_u32(out.stream_position()?)
		}
		
		let load_addr = u64_to_u32(self.load_addr)?;

		// start by writing data.
		out.seek(io::SeekFrom::Start(self.data_offset()))?;
		out.write_all(&self.data)?;

		let mut interp_offset = 0;
		let mut dyntab_offset = 0;
		let mut interp_size = 0;
		let mut dyntab_size = 0;
		if !self.interp.is_empty() {
			// now interp
			interp_offset = stream_position32(&mut out)?;
			out.write_all(&self.interp)?;
			interp_size = usize_to_u32(self.interp.len())?;
			// now strtab
			let strtab_offset = stream_position32(&mut out)?;
			out.write_all(&self.strtab)?;
			// now symtab
			let symtab_offset = stream_position32(&mut out)?;
			let null_symbol = [0; mem::size_of::<elf::Sym32>()];
			out.write_all(&null_symbol)?;
			let mut symbols: HashMap<SymbolName, u32> = HashMap::new();
			for (i, (sym, (strtab_offset, symbol_type))) in self.dynsyms.iter().enumerate() {
				symbols.insert(*sym, usize_to_u32(i + 1)?);
				let sym = elf::Sym32 {
					name: u64_to_u32(*strtab_offset)?,
					info: elf::STB_GLOBAL << 4 | u8::from(*symbol_type),
					value: 0,
					size: 0,
					other: 0,
					shndx: 0,
				};
				out.write_all(&sym.to_bytes())?;
			}
			// now reltab
			let reltab_offset = stream_position32(&mut out)?;
			for (reloc, addr) in self.relocations.iter() {
				let index = *symbols.get(&reloc.sym).unwrap();
				let rel = elf::Rel32 {
					offset: u64_to_u32(*addr)?,
					info: index << 8 | u32::from(reloc.r#type.to_x86_u8()),
				};
				out.write_all(&rel.to_bytes())?;
			}
			let reltab_size = stream_position32(&mut out)? - reltab_offset;
			// now hash
			let hashtab_offset = stream_position32(&mut out)?;
			// put everything in a single bucket
			let nsymbols = u64_to_u32(symbols.len() as u64)?;
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
			dyntab_offset = stream_position32(&mut out)?;
			let mut dyn_data = vec![
				elf::DT_RELSZ,
				reltab_size,
				elf::DT_RELENT,
				8,
				elf::DT_REL,
				load_addr + reltab_offset,
				elf::DT_STRSZ,
				usize_to_u32(self.strtab.len())?,
				elf::DT_STRTAB,
				load_addr + strtab_offset,
				elf::DT_SYMENT,
				16,
				elf::DT_SYMTAB,
				load_addr + symtab_offset,
				elf::DT_HASH,
				load_addr + hashtab_offset,
			];
			for lib in &self.lib_strtab_offsets {
				dyn_data.extend([elf::DT_NEEDED, u64_to_u32(*lib)?]);
			}
			dyn_data.extend([elf::DT_NULL, 0]);
			let mut dyn_bytes = Vec::with_capacity(dyn_data.len() * 4);
			for x in dyn_data {
				dyn_bytes.extend(u32::to_le_bytes(x));
			}
			dyntab_size = usize_to_u32(dyn_bytes.len())?;
			out.write_all(&dyn_bytes)?;
		}

		let file_size: u32 = stream_position32(&mut out)?;

		out.seek(io::SeekFrom::Start(0))?;

		let ehdr = elf::Ehdr32 {
			phnum: self.segment_count(),
			phoff: elf::Ehdr32::size_of().into(),
			// apparently you're supposed to set this to zero if there are no sections.
			// at least, that's what readelf seems to think.
			shentsize: 0,
			entry: u64_to_u32(entry_point)?,
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
			// so we do need two segments.
			let phdr_bss = elf::Phdr32 {
				flags: elf::PF_R | elf::PF_W, // read, write
				offset: 0,
				vaddr: u64_to_u32(bss_addr)?,
				filesz: 0,
				memsz: u64_to_u32(bss_size)?,
				..Default::default()
			};
			out.write_all(&phdr_bss.to_bytes())?;
		}

		if !self.interp.is_empty() {
			let phdr_interp = elf::Phdr32 {
				r#type: elf::PT_INTERP,
				flags: elf::PF_R,
				offset: interp_offset,
				vaddr: load_addr + interp_offset,
				filesz: interp_size,
				memsz: interp_size,
				align: 1,
				..Default::default()
			};
			out.write_all(&phdr_interp.to_bytes())?;

			let phdr_dynamic = elf::Phdr32 {
				r#type: elf::PT_DYNAMIC,
				flags: elf::PF_R,
				offset: dyntab_offset,
				vaddr: load_addr + dyntab_offset,
				filesz: dyntab_size,
				memsz: dyntab_size,
				align: 1,
				..Default::default()
			};
			out.write_all(&phdr_dynamic.to_bytes())?;
		}

		Ok(())
	}
}

impl<'a> Linker<'a> {
	pub const DEFAULT_CFLAGS: [&str; 5] = ["-Wall", "-Os", "-m32", "-fno-pic", "-c"];
	pub const DEFAULT_CXXFLAGS: [&str; 5] = Self::DEFAULT_CFLAGS;
	
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
			cc: "gcc".into(),
			cxx: "g++".into(),
			cflags: Self::DEFAULT_CFLAGS.iter().map(|&r| r.into()).collect(),
			cxxflags: Self::DEFAULT_CXXFLAGS.iter().map(|&r| r.into()).collect(),
			relocations: vec![],
			sources: vec![],
			libraries: vec![],
			source_data: vec![],
			warn: Box::new(Self::default_warning_handler),
		}
	}
	
	/// Set the C compiler.
	pub fn set_cc(&mut self, cc: &str) {
		self.cc = cc.into();
	}

	/// Set the C compiler flags.
	///
	/// These had better include something like `-c` and
	/// something like `-fno-pic`.
	pub fn set_cflags(&mut self, cflags: &[String]) {
		self.cflags = cflags.to_vec();
	}
	
	/// Set the C++ compiler.
	pub fn set_cxx(&mut self, cxx: &str) {
		self.cxx = cxx.into();
	}

	/// Set the C++ compiler flags.
	///
	/// These had better include something like `-c` and
	/// something like `-fno-pic`.
	pub fn set_cxxflags(&mut self, cxxflags: &[String]) {
		self.cxxflags = cxxflags.to_vec();
	}

	/// add a symbol from a source file.
	fn add_symbol(
		&mut self,
		source: SourceId,
		elf: &elf::Reader32LE,
		symbol: &elf::Symbol,
	) -> Result<(), ObjectError> {
		let name = elf.symbol_name(symbol)?;
//		let dbg_name = name.clone();
		let name_id = self.symbol_names.add(name);
		let size = symbol.size;
		
		let value = match symbol.value {
			elf::SymbolValue::Undefined => None,
			elf::SymbolValue::Absolute(n) => Some(SymbolValue::Absolute(n)),
			elf::SymbolValue::SectionOffset(shndx, sec_offset) => {
				match elf.section_type(shndx) {
					Some(elf::SectionType::ProgBits) => {
						let offset = elf.section_offset(shndx).unwrap() + sec_offset;
						Some(SymbolValue::Data { source, offset, size })
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
			match symbol.bind {
				elf::SymbolBind::Local => self.symbols.add_local(source, name_id, info),
				elf::SymbolBind::Global => self.symbols.add_global(source, name_id, info),
				elf::SymbolBind::Weak => self.symbols.add_weak(source, name_id, info),
				_ => return Ok(()), // eh
			};
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
		
		let source_id = SourceId(self.sources.len() as _);

		let elf = elf::Reader32LE::new(reader)?;
		if elf.r#type() != elf::Type::Rel {
			return Err(BadType);
		}

		for symbol in elf.symbols() {
			self.add_symbol(source_id, &elf, symbol)?;
		}

		let mut relocations = BTreeMap::new();
		for rel in elf.relocations() {
			let sym = self.symbol_names.add(elf.symbol_name(&rel.symbol)?);
			relocations.insert(rel.offset, Relocation {
				r#where: (source_id, rel.offset),
				sym,
				symbol_type: rel.symbol.r#type,
				r#type: rel.r#type,
				addend: rel.addend,
				#[cfg(debug_assertions)]
				entry_offset: rel.entry_offset,
			});
		}
		
		self.relocations.push(relocations);
		self.sources.push(name.into());
		self.source_data.push(elf.to_data());

		Ok(())
	}

	pub fn add_object_from_file(&mut self, path: impl AsRef<path::Path>) -> Result<(), ObjectError> {
		let path = path.as_ref();
		let file = fs::File::open(path)?;
		let mut file = io::BufReader::new(file);
		self.add_object(&path.to_string_lossy(), &mut file)
	}

	/// Add a dynamic library (.so). `name` can be a full path or
	/// something like "libc.so.6" --- any string you would pass to `dlopen`.
	pub fn add_dynamic_library(&mut self, name: &str) -> Result<(), ObjectError> {
		self.libraries.push(name.into());
		Ok(())
	}
	
	fn compile(&self, compiler: &str, flags: &[String], path: &str) -> Result<String, ObjectError> {
		use std::process::Command;
		
		let ext_idx = path.rfind('.').unwrap_or(path.len());
		let output_filename = path[..ext_idx].to_string() + ".o";
		
		let status = Command::new(compiler)
			.args(flags)
			.arg(path)
			.arg("-o")
			.arg(&output_filename)
			.status()?;
		if status.success() {
			Ok(output_filename)
		} else {
			Err(ObjectError::CommandFailed(status))
		}
	}
	
	/// Add a C file (.c). This calls out to an external C compiler.
	pub fn add_c(&mut self, path: &str) -> Result<(), ObjectError> {
		let output = self.compile(&self.cc, &self.cflags, path)?;
		self.add_object_from_file(&output)
	}
	
	/// Add a C++ file (.cpp/.cc/etc). This calls out to an external C++ compiler.
	pub fn add_cpp(&mut self, path: &str) -> Result<(), ObjectError> {
		let output = self.compile(&self.cxx, &self.cxxflags, path)?;
		self.add_object_from_file(&output)
	}
	
	/// Easy input API.
	/// Infers the file type of input, and calls the appropriate function (e.g. [Self::add_object]).
	pub fn add_input(&mut self, input: &str) -> Result<(), String> {
		enum FileType {
			Object,
			DynamicLibrary,
			C,
			CPlusPlus,
			Other,
		}

		use FileType::*;

		fn file_type(input: &str) -> FileType {
			if input.ends_with(".o") {
				return Object;
			}
			if input.ends_with(".c") {
				return C;
			}
			if input.ends_with(".cpp") || input.ends_with(".cc") || input.ends_with(".cxx")
				|| input.ends_with(".C") {
				return CPlusPlus;
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
				self.add_object_from_file(input)
					.map_err(|e| format!("Failed to process object file {input}: {e}"))
			}
			C => {
				self.add_c(input)
					.map_err(|e| format!("Failed to process C file {input}: {e}"))
			},
			CPlusPlus => {
				self.add_cpp(input)
					.map_err(|e| format!("Failed to process C++ file {input}: {e}"))
			},
			DynamicLibrary => self
				.add_dynamic_library(input)
				.map_err(|e| format!("Failed to process library file {input}: {e}")),
			Other => Err(format!("Unrecognized file type: {input}")),
		}
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
	
	/// Get value of symbol (e.g. ID of main → address of main).
	fn get_symbol_value(&self, map: &OffsetMap, exec: &LinkerOutput, sym: SymbolId) -> u64 {
		let info = self.symbols.get_info_from_id(sym);
		exec.eval_symbol_value(map, &info.value)
	}

	fn source_name(&self, id: SourceId) -> &str {
		&self.sources[id.0 as usize]
	}

	// @TODO: move me back into apply_relocation
	/// The value of the relocation *before* taking its type into account.
	fn relocation_absolute_value(&self, rel: &Relocation, symbol_value: u64, current_data: &[u8]) -> Result<u64, LinkWarning> {
		// currently this only deals with 32-bit relocations
		if current_data.len() < 4 {
			return Err(LinkWarning::RelOOB(self.source_name(rel.r#where.0).into(), rel.r#where.1));
		}
		
		let current_val = u32::from_le_bytes([
			current_data[0],
			current_data[1],
			current_data[2],
			current_data[3],
		]);
		
		
		Ok(symbol_value.wrapping_add(rel.addend as u64).wrapping_add(current_val.into()))
	}

	/// Apply relocation to executable.
	fn apply_relocation(&self, exec: &mut LinkerOutput, map: &OffsetMap, rel: &Relocation) -> LinkResult<()> {
		let apply_offset = match map.translate_rel_offset(rel) {
			Some(data_offset) => data_offset,
			None => {
				// this relocation isn't in a data section so there's nothing we can do about it
				return Ok(());
			}
		};
		let pc = apply_offset + exec.data_addr();

		let symbol = match self.get_symbol_id(rel.r#where.0, rel.sym) {
			None => {
				// symbol not defined. it should come from a library.
				exec.add_relocation(&self.symbol_names, rel, exec.data_addr() + apply_offset);
				return Ok(());
			}
			Some(sym) => sym,
		};

		let symbol_value = self.get_symbol_value(map, exec, symbol);

		// guarantee failure if apply_offset can't be converted to usize.
		// (this will probably never happen)
		let apply_start = apply_offset.try_into().unwrap_or(usize::MAX - 1000);
		let data = &mut exec.data[apply_start..];use elf::RelType::*;
		match self.relocation_absolute_value(rel, symbol_value, data) {
			Ok(value) => {
				let (value, size) = match rel.r#type {
					Direct32 => (value & u64::from(u32::MAX), 4),
					Pc32 => (value.wrapping_sub(pc) & u64::from(u32::MAX), 4),
					Other(x) => {
						self.emit_warning(LinkWarning::RelUnsupported(x));
						return Ok(())
					},
				};
				data[..size].copy_from_slice(&u64::to_le_bytes(value)[..size]);
			},
			Err(warning) => {
				self.emit_warning(warning);
			},
		}

		Ok(())
	}


	fn require_range(&self, ranges: &mut RangeSet, source: SourceId, offset: u64, size: u64) {
		if ranges.add(source, offset, size) {
			let src_idx = usize::try_from(source.0).unwrap();
			for (_, rel) in self.relocations[src_idx].range(offset..offset + size) {
				let (source, _off) = rel.r#where;
				if let Some(symbol) = self.get_symbol_id(source, rel.sym) {
					let value = &self.symbols.get_info_from_id(symbol).value;
					if let &SymbolValue::Data { source: req_source, offset: req_offset, size: req_size } = value {
						self.require_range(ranges, req_source, req_offset, req_size);
						
						// @TODO: delete
// 						let off_idx = usize::try_from(off).unwrap_or(usize::MAX);
// 						let curr_value = self.source_data[src_idx].get(off_idx..).unwrap_or(&[]);
// 						if let Ok(range_start) = self.relocation_absolute_value(rel, req_offset, curr_value) {
// 							let range_end = req_offset + req_size;
// 							if range_end < range_start {
// 								// @TODO: emit warning
// 								println!("{:x}",off);
// 								continue;
// 							}
// 							self.require_range(ranges, req_source, range_start, range_end - range_start);
// 						} // else, we'll emit a warning in apply_relocation
					} // else, it's okay, it's a bss relocation or something hopefully
				} // else, we'll deal with it in apply_relocation
			}
		}
	}
	
	/// Link everything together.
	pub fn link(&self, out: impl Write + Seek, entry: &str) -> LinkResult<()> {
		let mut exec = LinkerOutput::new(0x400000);
		if self.bss_size > 0 {
			exec.set_bss(0x70000000, self.bss_size);
		}
		if !self.libraries.is_empty() {
			exec.set_interp("/lib/ld-linux.so.2");
			for lib in self.libraries.iter() {
				exec.add_library(lib);
			}
		}

		let entry_name_id = self
			.symbol_names
			.get(entry)
			.ok_or_else(|| LinkError::NoEntry(entry.into()))?;
		let entry_id = self
			.symbols
			.get_id_from_name(SourceId::NONE, entry_name_id)
			.ok_or_else(|| LinkError::EntryNotDefined(entry.into()))?;
		
		let mut ranges = RangeSet::new(self.sources.len());
		
		let entry_value = &self.symbols.get_info_from_id(entry_id).value;
		let (entry_source, entry_offset, entry_size) = match entry_value {
			SymbolValue::Data { source, offset, size } => (*source, *offset, *size),
			_ => return Err(LinkError::EntryNoData(entry.into())),
		};
		
		self.require_range(&mut ranges, entry_source, entry_offset, entry_size);
		
		// compute offset map
		let offset_map = ranges.to_map();
		
		let mut data_section = vec![0; offset_map.size() as usize];
		
		offset_map.for_each(|source: SourceId, src_offset: u64, size: u64, dest_offset: u64| {
			let dest_start = dest_offset as usize;
			let dest_end = dest_start + size as usize;
			let src_start = src_offset as usize;
			let src_end = src_start + size as usize;
			//let dest_addr = dest_offset + exec.data_addr();
			//println!("{source:?}@{src_offset:x} => {:x}..{:x}", dest_addr,dest_addr+size); 
			data_section[dest_start..dest_end].copy_from_slice(
				&self.source_data[source.0 as usize][src_start..src_end]
			);
		});
		
		exec.set_data(data_section);
		
		for rel_map in self.relocations.iter() {
			for rel in rel_map.values() {
				self.apply_relocation(&mut exec, &offset_map, rel)?;
			}
		}

		// this should never panic, since we did require_range on the entry point.
		let entry_addr = offset_map.translate_offset(entry_source, entry_offset).unwrap() + exec.data_addr();
		exec.write(out, entry_addr)
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
