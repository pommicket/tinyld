#[cfg(test)]
mod tests {
	use std::process::{Command, Output};
	use std::fs::File;
	use tinyld::linker::{Linker, LinkWarning};
	
	fn panic_warning_handler(warning: LinkWarning) {
		eprintln!("warning: {warning}");
		panic!("this should not generate a warning");
	}

	fn test_linker<'a>() -> Linker<'a> {
		let mut linker = Linker::new();
		linker.set_warning_handler(panic_warning_handler);
		linker
	}
	
	fn file(s: &str) -> String {
		format!("./tests/{s}")
	}

	fn add(linker: &mut Linker, src: &str, is_local: bool) {
		let f = file(src);
		let s = if is_local { &f } else { src };
		linker.add_input(s).expect(&format!("failed to add {s}"));
	}
	
	fn link(linker: &Linker, out: &str, entry: &str) {
		linker.link_to_file(&file(out), entry).expect("failed to link");
	}
	
	fn run_with_stdin(name: &str, stdin: Option<&str>) -> Output {
		let mut command = Command::new(&file(name));
		if let Some(s) = stdin {
			let file = File::open(&file(s)).expect("stdin file does not exist");
			command.stdin(file);
		}
		
		let output = command
			.output()
			.expect("failed to run output executable");
		assert!(output.status.success());
		assert!(output.stderr.is_empty());
		output
	}
		
	fn run(name: &str) -> std::process::Output {
		run_with_stdin(name, None)
	}
	
	#[test]
	fn tiny_c() {
		let mut linker = test_linker();
		add(&mut linker, "tiny.c", true);
		link(&linker, "test.out", "entry");
		let output = run("tiny.out");
		assert!(output.stdout.is_empty());
	}

	#[test]
	fn basic_c() {
		let mut linker = test_linker();
		add(&mut linker, "basic.c", true);
		add(&mut linker, "libc.so.6", false);
		link(&linker, "basic.out", "entry");
		let output = run("basic.out");
		assert_eq!(output.stdout, b"137\n");
	}
	
	#[test]
	fn dylib_c() {
		let status = Command::new("gcc")
			.args(&["-m32", "-fPIC", "-shared", &file("dylib.c"), "-o", &file("dylib.so")])
			.status()
			.expect("failed to create dylib.so");
		assert!(status.success());
		
		
		let mut linker = test_linker();
		add(&mut linker, "dylib-test.c", true);
		add(&mut linker, "dylib.so", true);
		add(&mut linker, "libc.so.6", false);
		link(&linker, "dylib-test.out", "entry");
		let output = run("dylib-test.out");
		assert_eq!(output.stdout, b"7\n8\n");
	}
	
	#[test]
	fn cpp() {
		let mut linker = test_linker();
		add(&mut linker, "cpp.cpp", true);
		add(&mut linker, "libc.so.6", false);
		add(&mut linker, "libstdc++.so.6", false);
		link(&linker, "cpp.out", "main");
		let output = run_with_stdin("cpp.out", Some("cpp-input.txt"));
		assert_eq!(output.stdout, b"0\n7\n65\n212\n233\n");
	}
}
