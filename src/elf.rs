// basic ELF types and constants

use io::{BufRead, Seek};
use std::{fmt, io, mem};

pub trait ToBytes<const N: usize> {
	fn to_bytes(self) -> [u8; N];
}

pub trait FromBytes<const N: usize> {
	fn from_bytes(bytes: [u8; N]) -> Self;
}

// executable type
pub const ET_REL: u16 = 1;
pub const ET_EXEC: u16 = 2;

// segment type
pub const PT_LOAD: u32 = 1;
// segment flags
pub const PF_X: u32 = 1 << 0;
pub const PF_W: u32 = 1 << 1;
pub const PF_R: u32 = 1 << 2;

pub const DT_NULL: u32 = 0;
pub const DT_NEEDED: u32 = 1;
pub const DT_HASH: u32 = 4;
pub const DT_STRTAB: u32 = 5;
pub const DT_SYMTAB: u32 = 6;
pub const DT_STRSZ: u32 = 10;
pub const DT_SYMENT: u32 = 11;
pub const DT_REL: u32 = 17;
pub const DT_RELSZ: u32 = 18;
pub const DT_RELENT: u32 = 19;

pub const PT_DYNAMIC: u32 = 2;
pub const PT_INTERP: u32 = 3;

pub const SHT_PROGBITS: u32 = 1; // Program data
pub const SHT_SYMTAB: u32 = 2; // Symbol table
pub const SHT_RELA: u32 = 4; // Relocation entries with addends
pub const SHT_NOBITS: u32 = 8; // Program space with no data (bss)
pub const SHT_REL: u32 = 9; // Relocation entries, no addends

// symbol type
pub const STT_OBJECT: u8 = 1;
pub const STT_FUNC: u8 = 2;
pub const STT_SECTION: u8 = 3;

// symbol bind
pub const STB_LOCAL: u8 = 0;
pub const STB_GLOBAL: u8 = 1;
pub const STB_WEAK: u8 = 2;

// section number (for relocations)
pub const SHN_UNDEF: u16 = 0;
pub const SHN_ABS: u16 = 0xfff1;
//pub const SHN_COMMON: u16 = 0xfff2;

#[repr(C)]
pub struct Ehdr32 {
	pub ident: [u8; 4],
	pub class: u8,
	pub data: u8,
	pub version: u8,
	pub abi: u8,
	pub abiversion: u8,
	pub pad: [u8; 7],
	pub r#type: u16,
	pub machine: u16,
	pub version2: u32,
	pub entry: u32,
	pub phoff: u32,
	pub shoff: u32,
	pub flags: u32,
	pub ehsize: u16,
	pub phentsize: u16,
	pub phnum: u16,
	pub shentsize: u16,
	pub shnum: u16,
	pub shstrndx: u16,
}

impl Default for Ehdr32 {
	fn default() -> Self {
		Self {
			ident: [0x7F, b'E', b'L', b'F'],
			class: 1,
			data: 1,
			version: 1,
			abi: 0,
			abiversion: 0,
			pad: [0; 7],
			r#type: ET_EXEC,
			machine: 3,
			version2: 1,
			entry: 0,
			phoff: 0,
			shoff: 0,
			flags: 0,
			ehsize: mem::size_of::<Self>() as _,
			phentsize: mem::size_of::<Phdr32>() as _,
			phnum: 0,
			shentsize: mem::size_of::<Shdr32>() as _,
			shnum: 0,
			shstrndx: 0,
		}
	}
}

impl Ehdr32 {
	pub fn size_of() -> u8 {
		mem::size_of::<Self>() as u8
	}
}

#[repr(C)]
#[derive(Clone)]
pub struct Shdr32 {
	pub name: u32,
	pub r#type: u32,
	pub flags: u32,
	pub addr: u32,
	pub offset: u32,
	pub size: u32,
	pub link: u32,
	pub info: u32,
	pub addralign: u32,
	pub entsize: u32,
}

#[repr(C)]
pub struct Phdr32 {
	pub r#type: u32,
	pub offset: u32,
	pub vaddr: u32,
	pub paddr: u32,
	pub filesz: u32,
	pub memsz: u32,
	pub flags: u32,
	pub align: u32,
}

impl Default for Phdr32 {
	fn default() -> Self {
		Self {
			r#type: PT_LOAD,
			offset: 0,
			vaddr: 0,
			paddr: 0,
			filesz: 0,
			memsz: 0,
			flags: 0,
			align: 0x1000,
		}
	}
}

impl Phdr32 {
	pub fn size_of() -> usize {
		mem::size_of::<Self>()
	}
}

#[repr(C)]
pub struct Sym32 {
	pub name: u32,
	pub value: u32,
	pub size: u32,
	pub info: u8,
	pub other: u8,
	pub shndx: u16,
}

#[repr(C)]
pub struct Rela32 {
	pub offset: u32,
	pub info: u32,
	pub addend: i32,
}

#[repr(C)]
pub struct Rel32 {
	pub offset: u32,
	pub info: u32,
}

macro_rules! impl_bytes {
	($type: ident, $n: literal) => {
		impl FromBytes<$n> for $type {
			fn from_bytes(bytes: [u8; $n]) -> Self {
				unsafe { mem::transmute(bytes) }
			}
		}

		impl ToBytes<$n> for $type {
			fn to_bytes(self) -> [u8; $n] {
				unsafe { mem::transmute(self) }
			}
		}
	};
}

impl_bytes!(Ehdr32, 0x34);
impl_bytes!(Shdr32, 0x28);
impl_bytes!(Phdr32, 0x20);
impl_bytes!(Sym32, 16);
impl_bytes!(Rela32, 12);
impl_bytes!(Rel32, 8);

#[derive(Debug)]
pub enum Error {
	IO(io::Error),
	NotAnElf,
	BadUtf8,
	BadVersion,
	TooLarge,
	UnsupportedClass(u8, u8),
	BadShStrNdx(u16),
	BadSymShNdx(u16),
	BadSymIndex(u64),
	BadLink(u32),
	BadSectionIndex(u16),
	NoStrtab,
}

impl From<io::Error> for Error {
	fn from(e: io::Error) -> Error {
		Error::IO(e)
	}
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> std::fmt::Result {
		use Error::*;
		match self {
			IO(i) if i.kind() == io::ErrorKind::UnexpectedEof => write!(f, "unexpected EOF"),
			IO(i) => write!(f, "IO error: {i}"),
			NotAnElf => write!(f, "Not an ELF file."),
			TooLarge => write!(f, "ELF file too large."),
			UnsupportedClass(class, data) => {
				let class_str = match class {
					1 => "32",
					2 => "64",
					_ => "??",
				};
				let data_str = match data {
					1 => "little",
					2 => "big",
					_ => "??",
				};
				write!(f, "This type of executable ({class_str}-bit {data_str}-endian) is not supported.")
			},
			BadVersion => write!(f, "Apparently you're living in the future. Where I'm from, there's only ELF version 1"),
			BadUtf8 => write!(f, "Bad UTF-8 in ELF file."),
			BadShStrNdx(n) => write!(f, "e_shstrndx ({n}) does not refer to a valid section."),
			BadSymShNdx(n) => write!(f, "Bad symbol shndx field: {n}."),
			BadSymIndex(x) => write!(f, "Bad symbol index: {x}"),
			NoStrtab => write!(f, "No .strtab section found."),
			BadLink(x) => write!(f, "Bad section link: {x}"),
			BadSectionIndex(x) => write!(f, "Bad section index: {x}"),
		}
	}
}

impl From<&Error> for String {
	fn from(e: &Error) -> String {
		format!("{e}")
	}
}

type Result<T> = std::result::Result<T, Error>;

fn bytes_to_string(bytes: Vec<u8>) -> Result<String> {
	String::from_utf8(bytes).map_err(|_| Error::BadUtf8)
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Machine {
	X86,
	Amd64,
	Other(u16),
}

impl From<u16> for Machine {
	fn from(x: u16) -> Self {
		use Machine::*;
		match x {
			3 => X86,
			0x3e => Amd64,
			_ => Other(x),
		}
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SectionType {
	ProgBits,
	NoBits,
	Rel,
	Rela,
	Symtab,
	Other(u32),
}

impl From<u32> for SectionType {
	fn from(x: u32) -> Self {
		use SectionType::*;
		match x {
			SHT_PROGBITS => ProgBits,
			SHT_NOBITS => NoBits,
			SHT_REL => Rel,
			SHT_RELA => Rela,
			SHT_SYMTAB => Symtab,
			_ => Other(x),
		}
	}
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Type {
	Rel,
	Exec,
	Other(u16),
}

impl From<u16> for Type {
	fn from(x: u16) -> Self {
		use Type::*;
		match x {
			1 => Rel,
			2 => Exec,
			_ => Other(x),
		}
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SymbolBind {
	Global,
	Weak,
	Local,
	Other(u8),
}

impl From<u8> for SymbolBind {
	fn from(x: u8) -> Self {
		use SymbolBind::*;
		match x {
			STB_GLOBAL => Global,
			STB_WEAK => Weak,
			STB_LOCAL => Local,
			_ => Other(x),
		}
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SymbolType {
	Function,
	Object,
	Section,
	Other(u8),
}

impl From<u8> for SymbolType {
	fn from(x: u8) -> Self {
		use SymbolType::*;
		match x {
			STT_FUNC => Function,
			STT_OBJECT => Object,
			STT_SECTION => Section,
			_ => Other(x),
		}
	}
}

impl From<SymbolType> for u8 {
	fn from(x: SymbolType) -> Self {
		use SymbolType::*;
		match x {
			Function => STT_FUNC,
			Object => STT_OBJECT,
			Section => STT_SECTION,
			Other(x) => x,
		}
	}
}

#[derive(Debug, Copy, Clone)]
pub enum SymbolValue {
	Undefined,
	Absolute(u64),
	SectionOffset(u16, u64),
}

#[derive(Debug, Clone)]
pub struct Symbol {
	name: String,
	pub size: u64,
	pub value: SymbolValue,
	pub bind: SymbolBind,
	pub r#type: SymbolType,
}

#[derive(Debug, Clone, Copy)]
pub enum RelType {
	Direct32,
	Pc32,
	Other(u8),
}

impl RelType {
	fn from_u8(id: u8, machine: Machine) -> Self {
		use Machine::*;
		use RelType::*;
		match (machine, id) {
			(X86, 1) => Direct32,
			(X86, 2) => Pc32,
			_ => RelType::Other(id),
		}
	}

	pub fn to_x86_u8(self) -> Option<u8> {
		use RelType::*;
		Some(match self {
			Direct32 => 1,
			Pc32 => 2,
			Other(x) => x,
		})
	}
}

pub struct Relocation {
	pub r#type: RelType,
	/// file offset of relocation metadata (for debugging)
	pub entry_offset: u64, 
	/// where the relocation should be applied. for [ET_REL], this is a file offset; otherwise, it's an address.
	pub offset: u64,
	/// symbol which should be inserted at the offset.
	pub symbol: Symbol,
	/// to be added to the symbol's value
	pub addend: i64,
}

/// There are multiple formats of ELF file (32-bit/64-bit, little/big-endian),
/// so we can make types which read those formats derive from this trait.
pub trait Reader
where
	Self: Sized,
{
	fn new(reader: impl BufRead + Seek) -> Result<Self>;
	fn r#type(&self) -> Type;
	fn machine(&self) -> Machine;
	fn entry(&self) -> u64;
	fn symbols(&self) -> &[Symbol];
	fn relocations(&self) -> &[Relocation];
	fn symbol_name(&self, sym: &Symbol) -> Result<String>;
	/// type of section with index `idx`
	fn section_type(&self, idx: u16) -> Option<SectionType>;
	/// get file data. this drops the reader.
	fn to_data(self) -> Vec<u8>;
}

/// reader for 32-bit little-endian ELF files.
pub struct Reader32LE {
	ehdr: Ehdr32,
	shdrs: Vec<Shdr32>,
	symbols: Vec<Symbol>,
	/// All data in the file.
	/// We put it all in memory.
	/// Object files usually aren't huge or anything.
	data: Vec<u8>,
	relocations: Vec<Relocation>,
}

impl Reader32LE {
	pub fn section_offset(&self, index: u16) -> Option<u64> {
		let index = usize::from(index);
		if index >= self.shdrs.len() {
			None
		} else {
			Some(self.shdrs[index].offset.into())
		}
	}
}

impl Reader for Reader32LE {
	fn new(mut reader: impl BufRead + Seek) -> Result<Self> {
		use Error::*;
		
		reader.seek(io::SeekFrom::End(0))?;
		let file_size = reader.stream_position()?;
		reader.seek(io::SeekFrom::Start(0))?;		
		let mut data = vec![0; file_size.try_into().map_err(|_| TooLarge)?];
		reader.read_exact(&mut data)?;
		reader.seek(io::SeekFrom::Start(0))?;	

		let mut hdr_buf = [0; 0x34];
		reader.read_exact(&mut hdr_buf)?;
		let ehdr = Ehdr32::from_bytes(hdr_buf);

		if ehdr.ident != [0x7f, b'E', b'L', b'F'] {
			return Err(NotAnElf);
		}
		if ehdr.class != 1 || ehdr.data != 1 {
			return Err(UnsupportedClass(ehdr.class, ehdr.data));
		}
		if ehdr.version != 1 || ehdr.version2 != 1 {
			return Err(BadVersion);
		}

		let mut shdrs = Vec::with_capacity(ehdr.shnum.into());
		// read section headers
		for i in 0..ehdr.shnum {
			let offset = u64::from(ehdr.shoff) + u64::from(ehdr.shentsize) * u64::from(i);
			reader.seek(io::SeekFrom::Start(offset))?;
			let mut shdr_buf = [0; 0x28];
			reader.read_exact(&mut shdr_buf)?;
			shdrs.push(Shdr32::from_bytes(shdr_buf));
		}

		// symtabs[i] = symbol table in section #i , or vec![] if section #i isn't a symbol table.
		let mut symtabs = Vec::with_capacity(ehdr.shnum.into());
		// all the symbols
		let mut symbols = vec![];
		let mut strtab_idx = None;

		let mut section_names = Vec::with_capacity(ehdr.shnum.into());

		// read section names, find .strtab
		for (s_idx, shdr) in shdrs.iter().enumerate() {
			if let Some(shstrhdr) = shdrs.get(ehdr.shstrndx as usize) {
				// get name
				reader.seek(io::SeekFrom::Start(
					shstrhdr.offset as u64 + shdr.name as u64,
				))?;
				let mut bytes = vec![];
				reader.read_until(0, &mut bytes)?;
				bytes.pop(); // remove terminating \0
				let name = bytes_to_string(bytes)?;
				if name == ".strtab" {
					strtab_idx = Some(s_idx);
				}
				
				section_names.push(name);

			}
		}
		
		for shdr in shdrs.iter() {
			let mut symtab = vec![];
			if shdr.r#type == SHT_SYMTAB && shdr.entsize as usize >= mem::size_of::<Sym32>() {
				// read symbol table
				for i in 0..shdr.size / shdr.entsize {
					let offset = u64::from(shdr.offset) + u64::from(shdr.entsize) * u64::from(i);
					reader.seek(io::SeekFrom::Start(offset))?;
					let mut sym_buf = [0; 16];
					reader.read_exact(&mut sym_buf)?;
					let sym = Sym32::from_bytes(sym_buf);
					let r#type = (sym.info & 0xf).into();
					let bind = (sym.info >> 4).into();
					let mut size = sym.size.into();

					let value = match sym.shndx {
						SHN_UNDEF => SymbolValue::Undefined,
						SHN_ABS => SymbolValue::Absolute(sym.value.into()),
						idx if idx < ehdr.shnum => {
							if r#type == SymbolType::Section && size == 0 {
								// section symbols have a size of 0, it seems.
								// i don't know why they don't just use the size of the section.
								// i'm replacing it here. it makes the code easier to write.
								size = shdrs[usize::from(idx)].size.into();
							}
							SymbolValue::SectionOffset(idx, sym.value.into())
						}
						x => return Err(BadSymShNdx(x)),
					};
					
					let mut name = {
						let strtab_offset = shdrs[strtab_idx.ok_or(Error::NoStrtab)?].offset;
						let strtab = &data.get(strtab_offset as usize..)
							.ok_or(Error::NoStrtab)?;
						let i = sym.name as usize;
						let mut end = i;
						while end < strtab.len() && strtab[end] != b'\0' {
							end += 1;
						}
						bytes_to_string(strtab[i..end].to_vec())?
					};
					
					if name.is_empty() {
						if r#type == SymbolType::Section {
							// section symbols have empty names.
							// this makes sense, since you don't want to repeat the strings in .strtab and .shstrtab
							// but i don't know why .strtab and .shstrtab are separate....
							name = section_names[usize::from(sym.shndx)].clone();
						}
					}
					
					let symbol = Symbol {
						name,
						value,
						r#type,
						bind,
						size,
					};
					symtab.push(symbols.len());
					symbols.push(symbol);
				}
			}
			symtabs.push(symtab);
		}

		// read relocations
		let mut relocations = vec![];
		for shdr in shdrs.iter() {
			let r#type = shdr.r#type;
			if !(r#type == SHT_REL || r#type == SHT_RELA) {
				continue;
			}
			let is_rela = r#type == SHT_RELA;

			if shdr.entsize < 8 {
				continue;
			}
			let count = shdr.size / shdr.entsize;

			reader.seek(io::SeekFrom::Start(shdr.offset.into()))?;

			let my_symbols = symtabs.get(shdr.link as usize).ok_or(BadLink(shdr.link))?;
			for r_idx in 0..count {
				let info;
				let mut offset;
				let addend;

				if is_rela {
					let mut rela_buf = [0; 12];
					reader.read_exact(&mut rela_buf)?;
					let rela = Rela32::from_bytes(rela_buf);
					info = rela.info;
					offset = rela.offset;
					addend = rela.addend;
				} else {
					let mut rel_buf = [0; 8];
					reader.read_exact(&mut rel_buf)?;
					let rel = Rel32::from_bytes(rel_buf);
					info = rel.info;
					offset = rel.offset;
					addend = 0;
				};

				if ehdr.r#type == ET_REL {
					// rel.offset is relative to section
					if let Some(info_hdr) = shdrs.get(shdr.info as usize) {
						offset += info_hdr.offset;
					}
				}

				let sym_idx = info >> 8;
				let symbols_idx = my_symbols
					.get(sym_idx as usize)
					.ok_or_else(|| BadSymIndex(sym_idx.into()))?;
				let symbol = &symbols[*symbols_idx];

				relocations.push(Relocation {
					r#type: RelType::from_u8(info as u8, ehdr.machine.into()),
					entry_offset: shdr.offset as u64 + r_idx as u64 * shdr.entsize as u64,
					symbol: symbol.clone(),
					addend: addend.into(),
					offset: offset.into(),
				});
			}
		}

		Ok(Self {
			ehdr,
			shdrs,
			symbols,
			relocations,
			data,
		})
	}

	fn r#type(&self) -> Type {
		self.ehdr.r#type.into()
	}

	fn machine(&self) -> Machine {
		self.ehdr.machine.into()
	}

	fn entry(&self) -> u64 {
		self.ehdr.entry.into()
	}

	fn relocations(&self) -> &[Relocation] {
		&self.relocations
	}

	fn symbols(&self) -> &[Symbol] {
		&self.symbols
	}

	fn symbol_name(&self, sym: &Symbol) -> Result<String> {
		Ok(sym.name.clone())
	}

	fn section_type(&self, idx: u16) -> Option<SectionType> {
		self.shdrs.get(idx as usize).map(|shdr| shdr.r#type.into())
	}

	fn to_data(self) -> Vec<u8> {
		self.data
	}
}
