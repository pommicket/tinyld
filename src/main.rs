/*
@TODO:
- bounds check on bss
- make bss optional
- finish docs
- disable "warning: relocation XXX not in a data/text section" for .rel.eh_frame
- make sure --no-stdlib generates a tiny executable
- make executables more tiny (overlap sections, etc.)
- static libraries
*/

extern crate clap;

use clap::Parser;

#[cfg(target_endian = "big")]
compile_error! {"WHY do you have a big endian machine???? it's the 21st century, buddy. this program won't work fuck you"}

mod elf;
pub mod linker;
mod util;

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
	nya: bool,
}

fn main_() -> Result<(), String> {
	let args = Args::parse();

	if args.nya {
		println!("hai uwu ^_^");
		return Ok(());
	}

	let inputs = &args.inputs;

	let mut linker = linker::Linker::new();

	let warning_handler = |w| {
		// termcolor is a goddamn nightmare to use
		// I DONT FUCKING CARE IF WRITING TO STDOUT FAILS
		// DONT MAKE ME UNWRAP EVERYTHING
		eprintln!("\x1b[93mwarning:\x1b[0m {w}");
	};
	linker.set_warning_handler(warning_handler);

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
		eprintln!("\x1b[91merror:\x1b[0m {e}");
	}
}
