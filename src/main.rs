/*
@TODO:
- static libraries
*/

extern crate clap;

use clap::Parser;

#[cfg(target_endian = "big")]
compile_error! {"WHY do you have a big endian machine???? it's the 21st century, buddy. this program won't work fuck you"}

use tinyld::linker;

#[derive(Parser, Debug)]
struct Args {
	/// Input files: object files (.o) and shared libraries (.so) are supported.
	inputs: Vec<String>,
	/// If set, the program will not be linked against libc.
	///
	/// This makes the executable smaller.
	#[arg(long = "no-stdlib", default_value_t = false)]
	no_std_lib: bool,
	/// If set, the program will be linked against libstdc++.
	///
	/// This is needed when using any C++ library functions.
	#[arg(long = "stdc++", default_value_t = false)]
	std_cpp: bool,
	/// Output executable path.
	#[arg(short = 'o', long = "output", default_value = "a.out")]
	output: String,
	/// The name of the function which will be used as the entry point.
	#[arg(short = 'e', long = "entry", default_value = "entry")]
	entry: String,
	/// :3
	#[arg(long = "nya")]
	nya: bool,
	/// C compiler
	///
	/// Note: clang *really* wants to generate `R_386_PLT32` relocations
	///  even when you beg it not to.
	#[arg(long = "cc", default_value = "gcc")]
	cc: String,
	/// C compiler flags
	///
	/// The C compiler is invoked using `(cc) (cflags) (C file) -o (object file)`
	#[arg(long = "cflags", default_values = linker::Linker::DEFAULT_CFLAGS)]
	cflags: Vec<String>,
	/// C++ compiler
	#[arg(long = "cxx", default_value = "g++")]
	cxx: String,
	/// C++ compiler flags
	#[arg(long = "cxxflags", default_values = linker::Linker::DEFAULT_CXXFLAGS)]
	cxxflags: Vec<String>,
}

fn main_() -> Result<(), String> {
	let args = Args::parse();

	if args.nya {
		println!("hai uwu ^_^");
		return Ok(());
	}

	let inputs = &args.inputs;

	let mut linker = linker::Linker::new();

	linker.set_cc(&args.cc);
	linker.set_cflags(&args.cflags);
	linker.set_cxx(&args.cxx);
	linker.set_cxxflags(&args.cxxflags);

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
			linker.add_input("test.c")?;
		} else {
			return Err("no inputs provided.".into());
		}
	}

	if !args.no_std_lib {
		linker.add_input("libc.so.6")?;
	}
	if args.std_cpp {
		linker.add_input("libstdc++.so.6")?;
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
