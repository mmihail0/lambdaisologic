use std::env;
use std::fs;
use std::process;

use curry_howard::eval::normalize_with_env;
use curry_howard::parser::{parse_program, parse_type};
use curry_howard::search::{prove_with_mode, LogicMode, DEFAULT_SEARCH_DEPTH};
use curry_howard::syntax::Term;
use curry_howard::typecheck::{check_declaration, Context};

fn usage() -> String {
    format!(
        "usage:\n  curry-howard check <file.ch>\n  curry-howard prove <proposition> [--classical] [--depth <n>]\n\noptions:\n  --check <file.ch>      verify theorems in a source file\n  --prove <proposition>  search for a proof term\n  -c, --classical        enable classical proof search (callcc/throw)\n  -i, --intuitionistic   use intuitionistic proof search (default)\n  -d, --depth <n>        maximum proof search depth (default: {})\n  -h, --help             show this help message",
        DEFAULT_SEARCH_DEPTH
    )
}

fn run_check(path: &str) -> i32 {
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(err) => {
            eprintln!("error reading '{}': {}", path, err);
            return 1;
        }
    };

    let decls = match parse_program(&source) {
        Ok(d) => d,
        Err(err) => {
            eprintln!("{}: {}", path, err);
            return 1;
        }
    };

    if decls.is_empty() {
        println!("no theorems found in {}", path);
        return 0;
    }

    let mut ctx = Context::new();
    let mut norm_env: Vec<(String, Term)> = Vec::new();
    let mut had_error = false;

    for decl in &decls {
        match check_declaration(&ctx, decl) {
            Ok(()) => {
                let normalized = normalize_with_env(&decl.proof, &norm_env);
                println!("[OK] {} : {}", decl.name, decl.ty);
                println!("  normalized: {}", normalized);
                ctx = ctx.extend(decl.name.clone(), decl.ty.clone());
                norm_env.push((decl.name.clone(), normalized));
            }
            Err(err) => {
                eprintln!(
                    "[FAIL] {} (line {}, col {}): {}",
                    decl.name, decl.span.line, decl.span.col, err
                );
                had_error = true;
            }
        }
    }

    if had_error {
        1
    } else {
        0
    }
}

fn mode_label(mode: LogicMode) -> &'static str {
    match mode {
        LogicMode::Intuitionistic => "intuitionistic",
        LogicMode::Classical => "classical",
    }
}

fn run_prove(prop_str: &str, depth: usize, mode: LogicMode) -> i32 {
    let ty = match parse_type(prop_str) {
        Ok(t) => t,
        Err(err) => {
            eprintln!("{}", err);
            return 1;
        }
    };

    let label = mode_label(mode);
    match prove_with_mode(&ty, depth, mode) {
        Some(proof) => {
            println!("[PROVED] ({}) {}", label, ty);
            println!("  proof: {}", proof);
            0
        }
        None => {
            eprintln!(
                "[UNPROVABLE] no {} proof found for {} within depth {}",
                label, ty, depth
            );
            1
        }
    }
}

fn parse_prove_args(args: &[String]) -> Result<(String, usize, LogicMode), String> {
    let mut depth = DEFAULT_SEARCH_DEPTH;
    let mut mode = LogicMode::Intuitionistic;
    let mut prop: Option<String> = None;
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--classical" | "-c" => {
                mode = LogicMode::Classical;
            }
            "--intuitionistic" | "-i" => {
                mode = LogicMode::Intuitionistic;
            }
            "--depth" | "-d" => {
                i += 1;
                if i >= args.len() {
                    return Err("missing value for --depth".to_string());
                }
                depth = args[i]
                    .parse::<usize>()
                    .map_err(|_| format!("invalid depth '{}'", args[i]))?;
            }
            flag if flag.starts_with("--depth=") => {
                let raw = &flag["--depth=".len()..];
                depth = raw
                    .parse::<usize>()
                    .map_err(|_| format!("invalid depth '{}'", raw))?;
            }
            arg => {
                if prop.is_some() {
                    return Err(format!("unexpected argument '{}'", arg));
                }
                prop = Some(arg.to_string());
            }
        }
        i += 1;
    }

    let proposition = prop.ok_or_else(|| "missing proposition for prove".to_string())?;
    Ok((proposition, depth, mode))
}

fn run(args: &[String]) -> i32 {
    if args.is_empty() {
        eprintln!("{}", usage());
        return 1;
    }

    match args[0].as_str() {
        "-h" | "--help" | "help" => {
            println!("{}", usage());
            0
        }
        "check" | "--check" => {
            if args.len() != 2 {
                eprintln!("expected exactly one file path for check\n{}", usage());
                return 1;
            }
            run_check(&args[1])
        }
        "prove" | "--prove" => match parse_prove_args(&args[1..]) {
            Ok((prop, depth, mode)) => run_prove(&prop, depth, mode),
            Err(msg) => {
                eprintln!("{}\n{}", msg, usage());
                1
            }
        },
        other => {
            eprintln!("unknown command '{}'\n{}", other, usage());
            1
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let code = run(&args);
    process::exit(code);
}
