extern crate mgt;

use clap::{App, Arg};
use std::hash::{Hash, Hasher};

use std::fs::File;
use std::io::Read;
use std::path::Path;

use log::{debug, error, info, warn};

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
        .arg(Arg::with_name("COERCION_PARAMETERS")
                 .help("When set, uses coercion parameters to implement polymorphism rather than treating unresolved type variables as ?.")
                 .long("coercion-parameters"))
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
                 .help("Sets the output directory name. If there are multiple eliminators, the files will be given a unique code per eliminator.")
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
    options.dynamic_type_variables = !config.is_present("COERCION_PARAMETERS");
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
            if let Some(path) = config.value_of("OUTPUT") {
                opts.persist = true;
                opts.path = path.into();
            }

            if input_source == "-" {
                opts.basename = "a.out".into();
            } else {
                match Path::new(input_source).file_stem() {
                    None => warn!(
                        "Couldn't form basename from {}, using '{}'.",
                        input_source, opts.basename
                    ),
                    Some(basename) => opts.basename = basename.to_string_lossy().into(),
                };
            }

            if config.is_present("TRANSIENT") {
                if config.is_present("OUTPUT") {
                    warn!("Output directory was set, but so was --transient. Not saving the directory.");
                }
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

    let progs: Vec<(_, _, _)> = algorithm(options.clone(), e).into_iter().collect();

    for (variation, e, g) in progs.iter() {
        println!("\nPROGRAM {}\n{}\n:\n{}", variation, e, g);
    }

    if let CompilationMode::Compile(opts) = options.compile {
        let workdir =
            tempfile::TempDir::new_in(".").expect("allocating working directory for ocamlopt");
        let workpath: String = workdir.path().to_string_lossy().into();
        debug!("Working in {}.", workpath);

        let compiler = OCamlCompiler::new(CompilationOptions {
            path: workpath.clone(),
            ..opts.clone()
        });

        for (variation, e, g) in progs.into_iter() {
            compiler.go(&variation, e, g);
        }

        if opts.persist {
            debug!("Persisting to {}", opts.path);
            match std::fs::metadata(&opts.path) {
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                    // perfect, overwrite
                    let workdir = workdir.into_path();
                    debug!("Renaming {} to {}.", workdir.to_string_lossy(), opts.path);

                    std::fs::rename(workdir, opts.path).expect("persisting output directory");
                }
                Ok(md) if md.is_dir() => {
                    // copy everything over
                    debug!("Copying contents of {} to {}.", workpath, opts.path);

                    for entry in std::fs::read_dir(workpath).expect("persisting output directory") {
                        let src = entry.expect("persisting file (finding file)").path();
                        let tgt = Path::new(&opts.path)
                            .join(src.file_name().expect("persisting file (finding name)"));

                        if let Ok(_md) = tgt.metadata() {
                            warn!("Overwriting {}.", tgt.to_string_lossy());
                        }

                        std::fs::rename(src, tgt).expect("persisting file (rename)");
                    }

                    drop(workdir);
                }
                Ok(_) => {
                    let workdir = workdir.into_path();

                    error!(
                        "Couldn't persist to {}, file already exists and is not a directory. Leaving things in {}.",
                        opts.path,
                        workdir.to_string_lossy()
                    );
                    std::process::exit(4);
                }
                Err(e) => {
                    let workdir = workdir.into_path();

                    error!(
                        "I/O error persisting directory: {}. Leaving things in {}.",
                        e,
                        workdir.to_string_lossy()
                    );
                    std::process::exit(5);
                }
            }
        } else {
            drop(workdir);
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

    let dynamic_type_variables = options.dynamic_type_variables;
    let ci = CoercionInsertion::new(options);

    ves.iter()
        .map(|ve| {
            let mut e = e.clone().eliminate(&ve);
            let mut m = m.clone().eliminate(&ve);

            assert!(e.choices().is_empty());
            assert!(m.choices().is_empty());

            if dynamic_type_variables {
                e.dynamize_type_variables();
                m.dynamize_type_variables();
            }

            info!("{}\n  : {}\n", e, m);

            let (e, g) = ci.explicit(e);

            if m != g.clone().into() {
                error!("Eliminated type was {} but coerced typed was {}.", m, g);
            }

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
    extern crate serial_test;

    use assert_cli::Assert;
    use serial_test::serial;
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

    fn succeeds_with(args: Vec<&str>, s: &str, out: &str) {
        run(args, s, |a| {
            a.succeeds().and().stdout().contains(out).unwrap()
        });
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
    fn fact5() {
        succeeds_with(
            vec!["-m", "run"],
            "let rec fact n = if n <= 0 then 1 else n * fact (n - 1) in fact 5",
            "120",
        );
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

    // MMG: all tests doing compilation should be marked `#[serial(dir)]`, where
    // `dir` is the directory that will be used for compilation.

    #[test]
    #[serial(mgt)]
    fn compile_id() {
        succeeds(vec!["-m", "compile"], "\\x. x");
        assert!(std::fs::metadata("mgt")
            .expect("compiled directory")
            .is_dir());
        std::fs::remove_dir_all("mgt").expect("clean up output directory");
    }

    #[test]
    #[serial(mgt_run)]
    fn compile_map_mono() {
        succeeds_with(
            vec!["-m", "run", "-o", "mgt_run"],
            r"
let rec map f l =
    match l with
    | [] -> [] : [int]
    | hd::tl -> f hd :: map f tl
and sum (l : [int]) =
    match l with
    | [] -> 0
    | hd::tl -> hd + sum tl
in
sum (map (\x. 2 * x) [1;2;3;4])",
            "20", // should output sum of [2;4;6;8] = 20
        );
        assert!(std::fs::metadata("mgt_run")
            .expect("compiled directory")
            .is_dir());
        std::fs::remove_dir_all("mgt_run").expect("clean up output directory");
    }

    #[test]
    #[serial(mgt_run)]
    fn compile_run_id() {
        succeeds(vec!["-m", "run", "-o", "mgt_run"], "\\x. x");
        assert!(std::fs::metadata("mgt_run")
            .expect("compiled directory")
            .is_dir());
        std::fs::remove_dir_all("mgt_run").expect("clean up output directory");
    }

    #[test]
    #[serial(mgt_test)]
    fn compile_id_output() {
        succeeds(vec!["-m", "compile", "-o", "mgt_test"], "\\x. x");
        assert!(std::fs::metadata("mgt_test")
            .expect("compiled directory")
            .is_dir());
        std::fs::remove_dir_all("mgt_test").expect("clean up output directory");
    }

    #[test]
    #[serial(mgt)]
    fn compile_id_transient() {
        succeeds(vec!["-m", "compile", "--transient"], "\\x. x");
        assert_eq!(
            std::fs::metadata("mgt")
                .expect_err("no saved directory")
                .kind(),
            std::io::ErrorKind::NotFound
        );
    }

    #[test]
    fn run_lax_if() {
        succeeds(vec!["-m", "run"], "if true then 1 else false");
    }
}
