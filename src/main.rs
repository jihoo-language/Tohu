use std::io::Read;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: tohu <file.tohu | ->");
        return ExitCode::from(2);
    }
    let path = args[1].clone();
    let src = if path == "-" {
        let mut s = String::new();
        if let Err(e) = std::io::stdin().read_to_string(&mut s) {
            eprintln!("error: {}", e);
            return ExitCode::FAILURE;
        }
        s
    } else {
        match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error: {}: {}", path, e);
                return ExitCode::FAILURE;
            }
        }
    };
    // Recursive definitions evaluate on the native stack.
    let worker = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let mut out = std::io::stdout().lock();
            tohu::run_source(&src, &mut out)
        })
        .expect("spawn interpreter thread");
    match worker.join().expect("interpreter thread panicked") {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {}", e);
            ExitCode::FAILURE
        }
    }
}
