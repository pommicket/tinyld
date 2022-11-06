// you will need gcc-multilib to compile a 32-bit executable (with stdlib)
// you need to use -fno-pic with gcc -- got,plt relocations aren't supported
// and also make the executable bigger.
extern crate clap;

use clap::Parser;

#[cfg(target_endian = "big")]
compile_error! {"WHY do you have a big endian machine???? it's the 21st century, buddy. this program won't work fuck you"}

mod elf;
mod util;
mod linker;

#[derive(Parser, Debug)]
struct Args {
	/// Input files: object files (.o) and shared libraries (.so) are supported.
	inputs: Vec<String>,
	/// If set, the program will not be linked against libc.
	///
	/// This makes the executable smaller.
	#[arg(long = "no-std-lib", default_value_t = false)]
	no_std_lib: bool,
	/// Output executable path.
	#[arg(short = 'o', long = "output", default_value = "a.out")]
	output: String,
	/// The name of the function which will be used as the entry point.
	#[arg(short = 'e', long = "entry", default_value = "entry")]
	entry: String,
	/// :3
	#[arg(long = "nya")]
	nya: bool
}

fn main_() -> Result<(), String> {
	let args = Args::parse();
	
	if args.nya {
		println!("hai uwu ^_^");
		return Ok(());
	}
	
	let inputs = &args.inputs;
	
	let mut linker = linker::Linker::new();
	
	if inputs.is_empty() {
		if cfg!(debug_assertions) {
			// ease of use when debugging
			linker.add_input("test.o")?;
		} else {
			return Err("no inputs provided.".into());
		}
	}

	
	if !args.no_std_lib {
		linker.add_input("libc.so.6")?;
	}

	for input in inputs.iter() {
		linker.add_input(input)?;
	}
	
	linker.link_to_file(&args.output, &args.entry)
}

fn main() {
	if let Err(e) = main_() {
		eprintln!("{e}");
	}
}

