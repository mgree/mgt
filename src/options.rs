use std::path::Path;

pub const DEFAULT_WIDTH: usize = 80;

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
    /// guaranteed to fail, but may not be run in every execution of the
    /// program.
    ///
    /// When using `strict_ifs`, this should be set no higher than `Warn` (or
    /// else you may not be able to generate coercions).
    ///
    /// One reason for this flag is top-level weirdness. `if true then (true :?)
    /// else (0 : ?)` will type check just fine in both lax and strict regimes.
    /// Coercion insertion will tag both branches as bool, but the migrational
    /// inference says the whole thing has either type bool or int, depending. At
    /// present, crashes on an assertion in main. If you put it in a context,
    /// e.g., `false && ...`, then the right coercions will be generated and
    /// everything is fine.
    ///
    /// Annotating one branch seems to work fine. It seems like you could keep more
    /// information in an if about which return type you'd like it to be. Simply
    /// putting in annotations doens't quite cut it, because elimination will leave
    /// one side ill-typed: in the migration where the whole conditional has type
    /// `int`, the `true : int` annotation you get will break things.
    ///
    /// It's a bad situation. On the one hand, coercion insertion doesn't give you
    /// the exact inferred type. On the other hand, the inferred type sucks!
    pub safety_level: SafetyLevel,

    /// Should we generate coercion parameters for type variables or should we
    /// treat type variables as `?`, the dynamic type?
    ///
    /// Type variables---like all types---are consistent with `?`. But what
    /// should happen if we actually need to coerce a type variable to the
    /// dynamic type?
    ///
    /// Henglein and Rehof describe a notion of "coercion parameters", where
    /// function arguments of polymorphic that might be coerced to `?` cause the
    /// compiler to generate extra parameters for each such type variable; each
    /// instantiation/call site then passes in these coercion parameters.
    ///
    /// Setting `dynamic_type_variables` to `true` will cause every type
    /// variable to be changed to `?` before code generation.
    ///
    /// As of 2020-10-14, this defaults to `true`, since coercion parameters
    /// aren't generated yet.
    pub dynamic_type_variables: bool,

    /// Whether to show just the first result (`false`) or all results (`true`).
    /// Defaults to `false`.
    pub show_all: bool,

    /// Whether to just infer types, infer types and compile with the OCaml
    /// optimizing native compiler, or infer, compile, and run. Defaults to
    /// `CompilationMode::CompileAndRun`.
    pub compile: CompilationMode,
}

/// Safety levels for coercion insertion.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum SafetyLevel {
    Quiet,
    Warn,
    Error,
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
    /// Whether or not to enforce left-to-right evaluation in the compiled code.
    pub enforce_ltr: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            strict_ifs: false,
            safety_level: SafetyLevel::Warn,
            dynamic_type_variables: true,
            show_all: false,
            compile: CompilationMode::InferOnly,
        }
    }
}

impl CompilationOptions {
    pub fn compile_only() -> Self {
        CompilationOptions {
            run: false,
            persist: true,
            enforce_ltr: true,
            path: "./mgt".into(),
            basename: "out".into(),
        }
    }

    pub fn compile_and_run() -> Self {
        CompilationOptions {
            run: true,
            persist: false,
            enforce_ltr: true,
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
