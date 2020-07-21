extern crate mgt;

use clap::{App, Arg};

use std::fs::File;
use std::io::Read;

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
        .get_matches();

    let input_source = config.value_of("INPUT").expect("input source");

    let mut input = String::new();
    let res = if input_source == "-" {
        std::io::stdin().read_to_string(&mut input)
    } else {
        File::open(input_source).and_then(|mut f| f.read_to_string(&mut input))
    };

    if let Err(err) = res {
        eprintln!("I/O error: {}", err);
        std::process::exit(47);
    }

    let e = SourceExpr::parse(&input).unwrap_or_else(|e| {
        eprintln!("Parse error:\n{}", e);
        std::process::exit(2);
    });

    let (e, m, ves) = TypeInference::infer(&e).unwrap_or_else(|| {
        eprintln!("Constraint generation failed");
        std::process::exit(3);
    });

    println!("Found {} maximal typings.", ves.len());

    if ves.len() == 0 {
        println!();
        println!("Untypable; unresolved type: {:?}.", m);
        println!("{:?}", e);
        std::process::exit(1);
    }

    for (i, ve) in ves.iter().enumerate() {
        let e = e.clone().eliminate(&ve);
        let m = m.clone().eliminate(&ve);

        println!();
        if ves.len() > 1 {
            println!("Eliminator #{}: #{:?}", i + 1, ve);
        } else {
            println!("Eliminator: #{:?}", ve);
        }

        println!("m = {:?}", m);
        println!("{:?}", e);
    }

    std::process::exit(0);
}
