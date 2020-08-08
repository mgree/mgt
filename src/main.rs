extern crate mgt;

use clap::{App, Arg};
use std::hash::{Hash, Hasher};

use std::fs::File;
use std::io::Read;
use std::path::Path;

use log::{error, info, warn};

use mgt::syntax::*;
use mgt::*;

fn main() {
    let config = App::new(env!("CARGO_PKG_NAME"))
        .version(env!("CARGO_PKG_VERSION"))
        .author(env!("CARGO_PKG_AUTHORS"))
        .arg(
            Arg::with_name("INPUT")
                .help("Sets the input file (defaults to '-', meaning STDIN)")
                .default_value("-")
                .index(1),
        )
        .arg(
            Arg::with_name("v")
                .short("v")
                .multiple(true)
                .help("Sets the level of verbosity"),
        )
        .arg(Arg::with_name("STRICT_IFS")
                 .help("When set, conditionals must have consistent types; without it, mismatches conditionals have type `?` (may conflict with --safe-only; defaults to off)")
                 .long("strict-ifs"))
        .arg(Arg::with_name("SAFE_ONLY")
                 .help("When set, refuses to generate coercions between inconsistent types")
                 .long("safe-only"))
        .arg(Arg::with_name("COMPILATION_MODE")
                 .help("Determines whether to `infer` and show types, `compile` and persist an executable, or compile a transient executable and `run` it.")
                 .long("mode")
                 .short("m")
                 .number_of_values(1)
                 .possible_value("infer")
                 .possible_value("compile")
                 .possible_value("run")
                 .default_value("infer"))
        .arg(Arg::with_name("ALGORITHM")
                 .help("The type inference algorithm to use (defaults to campora)")
                 .long("algorithm")
                 .short("a")
                 .number_of_values(1)
                 .possible_value("campora")
                 .possible_value("dynamic")
                 .default_value("campora"))
        .arg(Arg::with_name("OUTPUT")
                 .help("Sets the output file. If there are multiple eliminators, the files will be numbered.")
                 .long("output")
                 .short("o")
                 .number_of_values(1))
        .arg(Arg::with_name("TRANSIENT")
                 .help("Prevents persistence of the generated executable.")
                 .long("transient")
                .conflicts_with("OUTPUT"))
        .get_matches();

    let verbosity = match config.occurrences_of("v") {
        0 => log::LevelFilter::Warn,
        1 => log::LevelFilter::Info,
        2 => log::LevelFilter::Debug,
        3 | _ => log::LevelFilter::Trace,
    };
    env_logger::Builder::from_default_env()
        .filter(None, verbosity)
        .init();

    let mut options = Options::default();

    let input_source = config.value_of("INPUT").expect("input source");

    options.strict_ifs = config.is_present("STRICT_IFS");
    options.safe_only = config.is_present("SAFE_ONLY");
    options.compile = match config.value_of("COMPILATION_MODE") {
        Some("infer") | None => CompilationMode::InferOnly,
        Some("compile") => CompilationMode::Compile(CompilationOptions::compile_only()),
        Some("run") => CompilationMode::Compile(CompilationOptions::compile_and_run()),
        Some(mode) => panic!("Invalid compilation mode {}.", mode),
    };
    options.compile = match options.compile {
        // MMG weird idiom
        CompilationMode::InferOnly => {
            if config.is_present("OUTPUT") {
                warn!("Setting `-o` in infer mode has no effect.");
            }

            if config.is_present("TRANSIENT") {
                warn!("Setting `--transient` in infer mode has no effect.")
            }

            CompilationMode::InferOnly
        }
        CompilationMode::Compile(mut opts) => {
            match config.value_of("OUTPUT") {
                Some(basename) => {
                    opts.persist = true;
                    opts.basename = basename.into();
                }
                None => {
                    if input_source == "-" {
                        opts.basename = "a.out".into();
                        warn!("No output file specified for input on STDIN; using a.out.");
                    } else {
                        match Path::new(input_source).file_stem() {
                            None => warn!(
                                "Couldn't form basename from {}, using '{}'.",
                                input_source, opts.basename
                            ),
                            Some(basename) => opts.basename = basename.to_string_lossy().into(),
                        };
                    }
                }
            };

            if config.is_present("TRANSIENT") {
                opts.persist = false;
            }

            CompilationMode::Compile(opts)
        }
    };
    if options.safe_only && options.strict_ifs {
        warn!("Running with both --strict-ifs and --safe-only may break compilation.");
    }

    let mut input = String::new();
    let res = if input_source == "-" {
        std::io::stdin().read_to_string(&mut input)
    } else {
        File::open(input_source).and_then(|mut f| f.read_to_string(&mut input))
    };

    if let Err(err) = res {
        error!("I/O error: {}", err);
        std::process::exit(47);
    }

    let e = SourceExpr::parse(&input).unwrap_or_else(|e| {
        error!("Parse error:\n{}", e);
        std::process::exit(2);
    });

    let algorithm = match config
        .value_of("ALGORITHM")
        .expect("no algorithm specified")
    {
        "campora" => campora,
        "dynamic" => dynamic,
        s => panic!("Invalid algorithm '{}'", s),
    };

    eprintln!("options {:#?}", options.compile);
    // TODO have algorithm yield a unique code for each program
    // TODO have compiler just persist the whole damn directory
    for (variation, e, g) in algorithm(options.clone(), e).into_iter() {
        println!("\n{}\n:\n{}", e, g);

        match options.compile.clone() {
            CompilationMode::InferOnly => (),
            CompilationMode::Compile(opts) => {
                let compiler =                 OCamlCompiler::new(CompilationOptions { variation, ..opts });
                compiler.go(e);
                drop(compiler);
            }
        }
    }

    std::process::exit(0);
}

fn campora(options: Options, e: SourceExpr) -> Vec<(String, ExplicitExpr, GradualType)> {
    let mut ti = TypeInference::new(options.clone());
    let (e, m, ves) = ti.run(&e).unwrap_or_else(|| {
        error!("Constraint generation failed");
        std::process::exit(3);
    });

    info!("Found {} maximal typings.", ves.len());

    if ves.len() == 0 {
        warn!("Untypable; unresolved type: {}.", m);
        warn!("{}", e);
        std::process::exit(1);
    }

    let ci = CoercionInsertion::new(options);

    ves.iter()
        .map(|ve| {
            let e = e.clone().eliminate(&ve);
            let m = m.clone().eliminate(&ve);

            let (e, g) = ci.explicit(e);
            assert_eq!(m, g.clone().into());

            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            ve.hash(&mut hasher);

            (format!("{:x}", hasher.finish()), e, g)
        })
        .collect()
}

fn dynamic(options: Options, e: SourceExpr) -> Vec<(String, ExplicitExpr, GradualType)> {
    let ci = CoercionInsertion::new(options);
    let (e, g) = ci.dynamic(e).unwrap_or_else(|| {
        error!("Coercion insertion failed");
        std::process::exit(3);
    });

    vec![("dynamic".into(), e, g)]
}

#[cfg(test)]
mod test {
    extern crate assert_cli;

    use assert_cli::Assert;
    use std::io::Write;

    fn run<F>(args: Vec<&str>, s: &str, f: F)
    where
        F: Fn(Assert) -> (),
    {
        let mut args = args;

        // no args
        eprintln!("arg-free");
        f(Assert::main_binary().with_args(&args).stdin(s));

        // explicit stdin
        eprintln!("explicit stdin");
        args.push("-");
        f(Assert::main_binary().with_args(&args).stdin(s));

        // file
        args.pop();
        let mut file = tempfile::NamedTempFile::new().expect("make temporary file");
        file.write_all(s.as_bytes())
            .expect("couldn't write to temporary file");
        let file_name = file.path().to_str().unwrap();
        eprintln!("temporary file {}", file_name);

        args.push(file_name);

        f(Assert::main_binary().with_args(&args));
    }

    fn succeeds(args: Vec<&str>, s: &str) {
        run(args, s, |a| a.succeeds().unwrap());
    }

    fn fails(args: Vec<&str>, s: &str) {
        run(args, s, |a| a.fails().unwrap());
    }

    #[test]
    fn id() {
        succeeds(vec![], "\\x. x");
        succeeds(vec!["-a", "campora"], "\\x. x");
        succeeds(vec!["-a", "dynamic"], "\\x. x");
    }

    #[test]
    fn lax_if() {
        succeeds(vec![], "if true then false else 5");
        succeeds(vec!["-a", "dynamic"], "if true then false else 5");
    }

    #[test]
    fn strict_if() {
        fails(vec!["--strict-ifs"], "if true then false else 5");
    }

    #[test]
    fn lax_if_annotated() {
        succeeds(vec![], "if true then true : ? else 0 : ?");
    }

    #[test]
    fn strict_if_annotated() {
        succeeds(vec!["--strict-ifs"], "if true then true : ? else 0 : ?");
    }

    #[test]
    fn lax_if_annotated_safe_only() {
        fails(vec!["--safe-only"], "if true then true : ? else 0 : ?");
        succeeds(vec!["-a", "dynamic"], "if true then true : ? else 0 : ?");
    }

    #[test]
    fn strict_if_annotated_safe_only() {
        fails(
            vec!["--safe-only", "--strict-ifs"],
            "if true then true : ? else 0 : ?",
        );
    }

    #[test]
    fn parse_error() {
        fails(vec![], "\\x.");
        fails(vec!["-a", "campora"], "\\x.");
        fails(vec!["-a", "dynamic"], "\\x.");
    }

    #[test]
    fn type_error() {
        fails(vec![], "true true");
        fails(vec!["-a", "campora"], "true true");
        fails(vec!["-a", "dynamic"], "true true");
        fails(vec!["--algorithm", "campora"], "true true");
        fails(vec!["--algorithm", "dynamic"], "true true");
    }

    #[test]
    fn compile_id() {
        succeeds(vec!["-m", "compile"], "\\x. x");
    }

    #[test]
    fn run_lax_if() {
        succeeds(vec!["-m", "run"], "if true then 1 else false");
    }
}
