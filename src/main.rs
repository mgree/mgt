extern crate mgt;

use clap::{App, Arg};

use std::fs::File;
use std::io::Read;

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
                 .help("When set, we will generate coercions between inconsistent types (default to off)")
                 .long("safe-only"))
        .arg(Arg::with_name("ALGORITHM")
                 .help("The type inference algorithm to use (defaults to campora)")
                 .long("algorithm")
                 .short("a")
                 .number_of_values(1)
                 .possible_value("campora")
                 .possible_value("dynamic")
                 .default_value("campora"))
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

    options.strict_ifs = config.is_present("STRICT_IFS");
    options.safe_only = config.is_present("SAFE_ONLY");
    if options.safe_only && options.strict_ifs {
        warn!("Running with both --strict-ifs and --safe-only may break compilation.");
    }

    let input_source = config.value_of("INPUT").expect("input source");

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

    let algorithm = match config.value_of("ALGORITHM").expect("no algorithm specified") {
        "campora" => campora,
        "dynamic" => dynamic,
        s => panic!("Invalid algorithm '{}'", s),
    };

    algorithm(options, e);

    std::process::exit(0);
}

fn campora(options: Options, e: SourceExpr) {
    let mut ti = TypeInference::new(options);
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

    for (i, ve) in ves.iter().enumerate() {
        if ves.len() > 1 {
            info!("Eliminator #{}: #{}", i + 1, ve);
        } else {
            info!("Eliminator: #{}", ve);
        }

        let e = e.clone().eliminate(&ve);
        let m = m.clone().eliminate(&ve);

        let (e, g) = ci.explicit(e);
        assert_eq!(m, g.into());

        println!("{}\n: {}", e, m);
    }
}

fn dynamic(options: Options, e: SourceExpr) {
    let ci = CoercionInsertion::new(options);
    let (e, g) = ci.dynamic(e).unwrap_or_else(|| {
        error!("Coercion insertion failed");
        std::process::exit(3);
    });

    println!("{}\n: {}", e, g);
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
        f(Assert::main_binary().with_args(&args).stdin(s));

        // explicit stdin
        args.push("-");
        f(Assert::main_binary().with_args(&args).stdin(s));

        // file
        args.pop();
        let mut file = tempfile::NamedTempFile::new().expect("make temporary file");
        file.write_all(s.as_bytes())
            .expect("couldn't write to temporary file");
        args.push(file.path().to_str().unwrap());

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
}
