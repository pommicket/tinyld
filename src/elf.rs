// basic ELF types and constants

use std::{io, mem};

pub const ET_REL: u16 = 1;
pub const ET_EXEC: u16 = 2;

#[repr(C)]
pub struct Header32 {
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

impl Default for Header32 {
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

impl Header32 {
	pub fn section_offset(&self, ndx: u16) -> u64 {
		ndx as u64 * self.shentsize as u64 + self.shoff as u64
	}

	pub fn section_seek(&self, ndx: u16) -> io::SeekFrom {
		io::SeekFrom::Start(self.section_offset(ndx))
	}

	pub fn to_bytes(self) -> [u8; 0x34] {
		unsafe { mem::transmute(self) }
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

pub const PT_LOAD: u32 = 0;

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
	pub fn to_bytes(self) -> [u8; 0x20] {
		unsafe { mem::transmute(self) }
	}
}
