use io::{BufRead, Seek, SeekFrom};
/// reads .a files
use std::{fmt, io, mem};

#[derive(Debug)]
pub enum Error {
	IO(io::Error),
	NotAnArchive,
	BadNumber,
	BadUtf8,
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		use Error::*;
		match self {
			IO(i) if i.kind() == io::ErrorKind::UnexpectedEof => write!(f, "unexpected EOF"),
			IO(e) => write!(f, "IO error: {e}"),
			NotAnArchive => write!(f, "Not an archive file."),
			BadNumber => write!(f, "Bad number in archive file (file corrupt?)"),
			BadUtf8 => write!(f, "Bad UTF-8 in file name."),
		}
	}
}

impl From<Error> for String {
	fn from(e: Error) -> Self {
		format!("{e}")
	}
}

impl From<io::Error> for Error {
	fn from(e: io::Error) -> Self {
		Self::IO(e)
	}
}

type Result<T> = std::result::Result<T, Error>;

struct FileMetadata {
	name: String,
	offset: u64,
	size: u64,
}

pub struct Archive<T: BufRead + Seek> {
	archive: T,
	files: Vec<FileMetadata>,
}

impl<T: BufRead + Seek> Archive<T> {
	pub fn new(mut archive: T) -> Result<Self> {
		use Error::*;

		fn parse_decimal(decimal: &[u8]) -> Result<u64> {
			let s = std::str::from_utf8(decimal).map_err(|_| Error::BadNumber)?;
			s.trim_end().parse().map_err(|_| Error::BadNumber)
		}

		fn parse_name(bytes: &[u8]) -> Result<&str> {
			let s = std::str::from_utf8(bytes).map_err(|_| Error::BadUtf8)?;
			Ok(&s[..=s.rfind(|c| c != ' ').unwrap_or(0)])
		}

		let mut signature = [0; 8];
		archive.read_exact(&mut signature)?;
		if &signature != b"!<arch>\n" {
			return Err(NotAnArchive);
		}

		#[repr(C)]
		#[derive(Debug)]
		struct RawMetadata {
			name: [u8; 16],
			_timestamp: [u8; 12],
			_owner_id: [u8; 6],
			_group_id: [u8; 6],
			_mode: [u8; 8],
			size: [u8; 10],
			_end_char: [u8; 2],
		}

		struct Metadata {
			name: [u8; 16],
			offset: u64,
			size: u64,
		}

		let mut metadata = vec![];

		loop {
			let mut buf = [0; mem::size_of::<RawMetadata>()];
			let size = archive.read(&mut buf)?;
			if size < buf.len() {
				break;
			}
			let raw: RawMetadata = unsafe { mem::transmute(buf) };
			let parsed = Metadata {
				name: raw.name,
				offset: archive.stream_position()?,
				size: parse_decimal(&raw.size)?,
			};
			// this can't panic, since size is 10 digits max.
			let size: i64 = parsed.size.try_into().unwrap();
			let offset = archive.seek(SeekFrom::Current(size))?;
			if offset % 2 == 1 {
				// metadata is aligned to 2 bytes
				archive.seek(SeekFrom::Current(1))?;
			}
			metadata.push(parsed);
		}

		let mut long_filenames;

		// see https://github.com/rust-lang/rust-clippy/issues/9274
		#[allow(clippy::read_zero_byte_vec)]
		{
			long_filenames = vec![];

			// in GNU archives, long filenames are stored in the "//" file.
			for f in metadata.iter() {
				if parse_name(&f.name)? == "//" {
					// we found it!
					archive.seek(SeekFrom::Start(f.offset))?;
					long_filenames = vec![0; f.size as usize];
					archive.read_exact(&mut long_filenames)?;
					break;
				}
			}
		}

		let mut files = vec![];
		for f in metadata.iter() {
			let name = parse_name(&f.name)?;
			if name == "/" || name == "//" {
				continue;
			}
			let slice = if let Some('/') = name.chars().next() {
				// a long filename
				let offset_str = name[1..].trim_end();
				let offset: usize = offset_str.parse().map_err(|_| BadNumber)?;
				let len = long_filenames[offset..]
					.iter()
					.position(|&x| x == b'/')
					.unwrap_or(0);
				let bytes = &long_filenames[offset..offset + len];
				std::str::from_utf8(bytes).map_err(|_| BadUtf8)?
			} else if let Some('/') = name.chars().last() {
				// filename is ended with / in GNU archives
				&name[..name.len() - 1]
			} else {
				name
			};
			let filename = String::from(slice);
			files.push(FileMetadata {
				name: filename,
				offset: f.offset,
				size: f.size,
			});
		}

		Ok(Self { archive, files })
	}

	/// Get number of files in archive.
	pub fn file_count(&self) -> usize {
		self.files.len()
	}

	/// Get name of file.
	pub fn file_name(&self, index: usize) -> &str {
		&self.files[index].name
	}

	/// Get all file data into memory.
	///
	/// I tried making a "sub-file" type but it was a mess.
	pub fn file_data(&mut self, index: usize) -> Result<Vec<u8>> {
		self.archive
			.seek(SeekFrom::Start(self.files[index].offset))?;
		let mut data = vec![0; self.files[index].size as usize];
		self.archive.read_exact(&mut data)?;
		Ok(data)
	}
}

/// example usage. prints out the contents of the archive file. (panics on error.)
pub fn _list(path: &str) {
	let f = std::fs::File::open(path).unwrap();
	let mut ar = Archive::new(io::BufReader::new(f)).unwrap();
	for i in 0..ar.file_count() {
		use io::Write;
		println!("\x1b[1m---{}---\x1b[0m", ar.file_name(i));
		let bytes = ar.file_data(i).unwrap();
		std::io::stdout().write_all(&bytes).unwrap();
		println!("\n");
	}
}
