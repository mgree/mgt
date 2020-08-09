use std::path::Path;

/// Configuration options
#[derive(Clone)]
pub struct Options {
    /// How should conditional branches of different types be treated?
    ///
    /// Consider `if b then 5 else false`. Campora et al. would simply reject
    /// this program, but it can reasonably be typed at `?`. With `strict_ifs`
    /// set, we behave like Campora et al. Without it, the program will have
    /// type `?`.
    pub strict_ifs: bool,

    /// Should we be allowed to coerce from `bool` to `int`? Such coercions are
    /// guaranteed to fail.
    ///
    /// When using `strict_ifs`, this should be set to `false` (or else you may
    /// not be able to generate coercions).
    ///
    /// The reason for this flag is top-level weirdness. `if true then (true :?)
    /// else (0 : ?)` will type check just fine in both lax and strict regimes.
    /// Coercion insertion will tag both branches as bool, but the migrational
    /// inference says the whole thing has either type bool or int, depending.
    /// At present, this crashes on an assertion in main. If you put it in a
    /// context, e.g., `false && ...`, then the right coercions will be
    /// generated and everything is fine.
    ///
    /// Annotating one branch seems to work fine. It seems like you could keep
    /// more information in an if about which return type you'd like it to be.
    /// Simply putting in annotations doens't quite cut it, because elimination
    /// will leave one side ill-typed: in the migration where the whole
    /// conditional has type `int`, the `true : int` annotation you get will
    /// break things.
    ///
    /// It's a bad situation. On the one hand, coercion insertion doesn't give
    /// you the exact inferred type. On the other hand, the inferred type sucks!
    pub safe_only: bool,

    /// Whether to just infer types, infer types and compile with the OCaml
    /// optimizing native compiler, or infer, compile, and run. Defaults to
    /// `CompilationMode::CompileAndRun`.
    pub compile: CompilationMode,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CompilationMode {
    InferOnly,
    Compile(CompilationOptions),
}

#[derive(Clone, Debug, PartialEq)]
pub struct CompilationOptions {
    /// Whether or not to run the resulting executable.
    pub run: bool,
    /// Whether or not to save the resulting executable.
    pub persist: bool,
    /// Output path.
    pub path: String,
    /// The base output name to use.
    pub basename: String,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            strict_ifs: false,
            safe_only: true,
            compile: CompilationMode::InferOnly,
        }
    }
}

impl CompilationOptions {
    pub fn compile_only() -> Self {
        CompilationOptions {
            run: false,
            persist: true,
            path: "./mgt".into(),
            basename: "out".into(),
        }
    }

    pub fn compile_and_run() -> Self {
        CompilationOptions {
            run: true,
            persist: false,
            path: "./mgt".into(),
            basename: "mgt_out".into(),
        }
    }

    pub fn file_ext(&self, variation: &str, ext: &str) -> String {
        let mut name = self.basename.clone();
        name.push('_');
        name.push_str(variation);
        name.push_str(ext);

        let path = Path::new(&self.path);
        path.join(name).to_string_lossy().into()
    }
}
