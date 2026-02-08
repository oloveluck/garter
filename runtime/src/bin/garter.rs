//! Garter CLI Tool
//!
//! Unified command for compiling and running Garter programs.
//!
//! Usage:
//!   garter run program.garter [--heap SIZE]   # Compile and run
//!   garter build program.garter               # Compile to executable
//!   garter asm program.garter                 # Generate assembly only

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        print_usage();
        std::process::exit(1);
    }

    match args[1].as_str() {
        "run" => cmd_run(&args[2..]),
        "build" => cmd_build(&args[2..]),
        "asm" => cmd_asm(&args[2..]),
        "--help" | "-h" => print_usage(),
        _ => {
            eprintln!("Unknown command: {}", args[1]);
            print_usage();
            std::process::exit(1);
        }
    }
}

fn print_usage() {
    eprintln!("Usage: garter <command> [options]");
    eprintln!();
    eprintln!("Commands:");
    eprintln!("  run <file.garter> [--heap SIZE]  Compile and run");
    eprintln!("  build <file.garter>              Compile to executable");
    eprintln!("  asm <file.garter>                Generate assembly only");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --heap SIZE    Set heap size in words (default: 100000)");
    eprintln!();
    eprintln!("Use '-' as filename to read from stdin.");
}

fn cmd_run(args: &[String]) {
    if args.is_empty() {
        eprintln!("Error: no input file specified");
        std::process::exit(1);
    }

    let input_file = &args[0];
    let mut heap_size: Option<usize> = None;

    let mut i = 1;
    while i < args.len() {
        if args[i] == "--heap" && i + 1 < args.len() {
            heap_size = args[i + 1].parse().ok();
            i += 2;
        } else {
            i += 1;
        }
    }

    let project_root = find_project_root();

    let temp_dir = std::env::temp_dir().join("garter-build");
    fs::create_dir_all(&temp_dir).expect("Failed to create temp directory");

    let source_path = if input_file == "-" {
        let mut source = String::new();
        std::io::Read::read_to_string(&mut std::io::stdin(), &mut source)
            .expect("Failed to read from stdin");
        let stdin_path = temp_dir.join("stdin.garter");
        fs::write(&stdin_path, source).expect("Failed to write temp file");
        stdin_path
    } else {
        PathBuf::from(input_file)
    };

    let base_name = source_path.file_stem().unwrap().to_str().unwrap();
    let asm_path = temp_dir.join(format!("{}.s", base_name));
    let obj_path = temp_dir.join(format!("{}.o", base_name));
    let exe_path = temp_dir.join(format!("{}.run", base_name));

    let compiler_path = project_root.join("main");
    if !compiler_path.exists() {
        eprintln!("Error: compiler not found at {:?}", compiler_path);
        eprintln!("Run 'make main' first to build the compiler.");
        std::process::exit(1);
    }

    let asm_output = Command::new(&compiler_path)
        .arg(&source_path)
        .output()
        .expect("Failed to run compiler");

    if !asm_output.status.success() {
        eprintln!("{}", String::from_utf8_lossy(&asm_output.stderr));
        std::process::exit(1);
    }

    fs::write(&asm_path, &asm_output.stdout).expect("Failed to write assembly");

    let nasm_status = Command::new("nasm")
        .args(["-f", "macho64", "-o"])
        .arg(&obj_path)
        .arg(&asm_path)
        .status()
        .expect("Failed to run nasm");

    if !nasm_status.success() {
        eprintln!("Error: nasm failed");
        std::process::exit(1);
    }

    let runtime_lib = project_root
        .join("runtime/target/x86_64-apple-darwin/release/libgarter_runtime.a");

    if !runtime_lib.exists() {
        eprintln!("Error: runtime library not found at {:?}", runtime_lib);
        eprintln!("Run 'cd runtime && cargo build --release --target x86_64-apple-darwin' first.");
        std::process::exit(1);
    }

    let link_status = Command::new("clang")
        .args(["-arch", "x86_64", "-o"])
        .arg(&exe_path)
        .arg(&obj_path)
        .arg(&runtime_lib)
        .args(["-lpthread", "-ldl"])
        .status()
        .expect("Failed to run clang");

    if !link_status.success() {
        eprintln!("Error: linking failed");
        std::process::exit(1);
    }

    let mut cmd = Command::new("arch");
    cmd.args(["-x86_64"]).arg(&exe_path);

    if let Some(size) = heap_size {
        cmd.arg(size.to_string());
    }

    let status = cmd
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
        .expect("Failed to run program");

    std::process::exit(status.code().unwrap_or(1));
}

fn cmd_build(args: &[String]) {
    if args.is_empty() {
        eprintln!("Error: no input file specified");
        std::process::exit(1);
    }

    let input_file = &args[0];
    let project_root = find_project_root();

    let source_path = PathBuf::from(input_file);
    let base_name = source_path.file_stem().unwrap().to_str().unwrap();
    let output_dir = source_path.parent().unwrap_or(Path::new("."));

    let asm_path = output_dir.join(format!("{}.s", base_name));
    let obj_path = output_dir.join(format!("{}.o", base_name));
    let exe_path = output_dir.join(format!("{}.run", base_name));

    let compiler_path = project_root.join("main");
    if !compiler_path.exists() {
        eprintln!("Error: compiler not found at {:?}", compiler_path);
        std::process::exit(1);
    }

    let asm_output = Command::new(&compiler_path)
        .arg(&source_path)
        .output()
        .expect("Failed to run compiler");

    if !asm_output.status.success() {
        eprintln!("{}", String::from_utf8_lossy(&asm_output.stderr));
        std::process::exit(1);
    }

    fs::write(&asm_path, &asm_output.stdout).expect("Failed to write assembly");

    let nasm_status = Command::new("nasm")
        .args(["-f", "macho64", "-o"])
        .arg(&obj_path)
        .arg(&asm_path)
        .status()
        .expect("Failed to run nasm");

    if !nasm_status.success() {
        eprintln!("Error: nasm failed");
        std::process::exit(1);
    }

    let runtime_lib = project_root
        .join("runtime/target/x86_64-apple-darwin/release/libgarter_runtime.a");

    if !runtime_lib.exists() {
        eprintln!("Error: runtime library not found at {:?}", runtime_lib);
        std::process::exit(1);
    }

    let link_status = Command::new("clang")
        .args(["-arch", "x86_64", "-o"])
        .arg(&exe_path)
        .arg(&obj_path)
        .arg(&runtime_lib)
        .args(["-lpthread", "-ldl"])
        .status()
        .expect("Failed to run clang");

    if !link_status.success() {
        eprintln!("Error: linking failed");
        std::process::exit(1);
    }

    println!("Built: {}", exe_path.display());
}

fn cmd_asm(args: &[String]) {
    if args.is_empty() {
        eprintln!("Error: no input file specified");
        std::process::exit(1);
    }

    let input_file = &args[0];
    let project_root = find_project_root();

    let source_path = PathBuf::from(input_file);
    let base_name = source_path.file_stem().unwrap().to_str().unwrap();
    let output_dir = source_path.parent().unwrap_or(Path::new("."));
    let asm_path = output_dir.join(format!("{}.s", base_name));

    let compiler_path = project_root.join("main");
    if !compiler_path.exists() {
        eprintln!("Error: compiler not found at {:?}", compiler_path);
        std::process::exit(1);
    }

    let asm_output = Command::new(&compiler_path)
        .arg(&source_path)
        .output()
        .expect("Failed to run compiler");

    if !asm_output.status.success() {
        eprintln!("{}", String::from_utf8_lossy(&asm_output.stderr));
        std::process::exit(1);
    }

    fs::write(&asm_path, &asm_output.stdout).expect("Failed to write assembly");
    println!("Generated: {}", asm_path.display());
}

fn find_project_root() -> PathBuf {
    let cwd = env::current_dir().expect("Failed to get current directory");

    if cwd.ends_with("runtime") {
        return cwd.parent().unwrap().to_path_buf();
    }

    if cwd.join("Makefile").exists() {
        return cwd;
    }

    if let Some(parent) = cwd.parent() {
        if parent.join("Makefile").exists() {
            return parent.to_path_buf();
        }
    }

    cwd
}
