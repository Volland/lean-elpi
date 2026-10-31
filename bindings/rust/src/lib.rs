//! Rust bindings for LeanElpi: compile ELPI (λProlog) programs and run queries on the
//! engine implemented in Lean 4.
//!
//! ```no_run
//! use leanelpi::Program;
//!
//! let p = Program::new("pred n o:int.\nn 1.\nn 2.")?;
//! let sols = p.solve("n X")?;
//! assert_eq!(sols[0].bindings["X"], "1");
//! # Ok::<(), leanelpi::Error>(())
//! ```
//!
//! Bindings come back as the strings ELPI prints ([`Solution::bindings`]) and as structured
//! [`Term`]s ([`Solution::terms`]). A [`Program`] is an immutable value:
//! [`Program::assert_clause`] and [`Program::declare`] return a new one. Programs may be
//! shared across threads.
//!
//! Host predicates are answered by a Rust closure during a run:
//!
//! ```no_run
//! use leanelpi::{Program, Term};
//!
//! let p = Program::new("pred edge i:string, o:string.\n\
//!                       pred path i:string, o:string.\n\
//!                       path X Y :- edge X Y.\npath X Z :- edge X Y, path Y Z.")?
//!     .declare("edge", "pred edge i:string, o:string.")?;
//! let edges = [("a", "b"), ("b", "c")];
//! let run = p.solve_host("path \"a\" X", 0, 0, |_name, args| {
//!     let Term::Str(from) = &args[0] else { return Err("unbound source".into()) };
//!     Ok(edges.iter().filter(|e| e.0 == from).map(|e| vec![Term::Str(e.1.into())]).collect())
//! })?;
//! assert_eq!(run.solutions.len(), 2);
//! # Ok::<(), leanelpi::Error>(())
//! ```

use std::collections::BTreeMap;
use std::ffi::{c_char, c_void, CStr, CString};
use std::fmt;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Once;

use serde::de::Error as _;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::{Map, Value};

mod ffi {
    use std::ffi::{c_char, c_void};
    pub type HostFn = extern "C" fn(ctx: *mut c_void, name: *const c_char, args: *const c_char) -> *mut c_char;
    extern "C" {
        pub fn leanelpi_init(err: *mut *mut c_char) -> i32;
        pub fn leanelpi_version() -> *const c_char;
        pub fn leanelpi_load(src: *const c_char, err: *mut *mut c_char) -> u64;
        pub fn leanelpi_assert(p: u64, clause: *const c_char, err: *mut *mut c_char) -> u64;
        pub fn leanelpi_free(p: u64);
        pub fn leanelpi_solve(
            p: u64,
            query: *const c_char,
            limit: u64,
            fuel: u64,
            err: *mut *mut c_char,
        ) -> *mut c_char;
        pub fn leanelpi_declare(p: u64, name: *const c_char, sig: *const c_char, err: *mut *mut c_char) -> u64;
        pub fn leanelpi_solve_host(
            p: u64,
            query: *const c_char,
            limit: u64,
            fuel: u64,
            host: HostFn,
            ctx: *mut c_void,
            err: *mut *mut c_char,
        ) -> *mut c_char;
        pub fn leanelpi_free_string(s: *mut c_char);
        /// The C allocator: the library frees a host answer with `free()`.
        pub fn malloc(size: usize) -> *mut c_void;
    }
}

const INVALID: u64 = u64::MAX;

/// A parse, type or runtime error reported by the engine, or a bad argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(pub String);

impl Error {
    /// Whether the run stopped because the fuel budget ran out (rather than an error in the
    /// program, the query or a host predicate).
    pub fn is_out_of_fuel(&self) -> bool {
        self.0.starts_with("out of fuel")
    }

    /// The engine's message.
    pub fn message(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// Take ownership of a string the library allocated.
unsafe fn take(s: *mut c_char) -> String {
    let out = CStr::from_ptr(s).to_string_lossy().into_owned();
    ffi::leanelpi_free_string(s);
    out
}

fn cstr(s: &str) -> Result<CString> {
    CString::new(s).map_err(|_| Error("string contains a NUL byte".into()))
}

fn ensure_started() -> Result<()> {
    static START: Once = Once::new();
    static mut FAILURE: Option<String> = None;
    // SAFETY: FAILURE is written once, inside `call_once`, and read after it returns.
    unsafe {
        START.call_once(|| {
            let mut err: *mut c_char = std::ptr::null_mut();
            if ffi::leanelpi_init(&mut err) != 0 {
                FAILURE = Some(if err.is_null() { "cannot start the Lean runtime".into() } else { take(err) });
            }
        });
        #[allow(static_mut_refs)]
        match &FAILURE {
            Some(m) => Err(Error(m.clone())),
            None => Ok(()),
        }
    }
}

/// The version of the linked engine.
pub fn version() -> Result<String> {
    ensure_started()?;
    Ok(unsafe { CStr::from_ptr(ffi::leanelpi_version()) }.to_string_lossy().into_owned())
}

/// An ELPI term as a tree: the JSON form `{"c":..,"a":[..]}`, `{"i":..}`, `{"f":..}`,
/// `{"s":..}`, `{"v":..}` and `{"o":..}` of the C ABI.
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// A constant, e.g. `foo` or `[]`.
    Const(String),
    /// A constant applied to arguments, e.g. `f 1 X` or the list cell `[1|L]` (`::`).
    App(String, Vec<Term>),
    Int(i64),
    Float(f64),
    Str(String),
    /// An unassigned variable (only in the arguments a host predicate receives, and in answers).
    Var(String),
    /// Anything else (λ-terms, applied variables, eigenvariables, an out-of-range integer),
    /// as ELPI prints it. Only ever produced by the engine; a host may not return it.
    Other(String),
}

impl Term {
    /// The terms of an ELPI list (`[]` / `::` cells), or `None` if this is not a proper list.
    pub fn as_list(&self) -> Option<Vec<&Term>> {
        let mut out = Vec::new();
        let mut t = self;
        loop {
            match t {
                Term::Const(c) if c == "[]" => return Some(out),
                Term::App(c, a) if c == "::" && a.len() == 2 => {
                    out.push(&a[0]);
                    t = &a[1];
                }
                _ => return None,
            }
        }
    }

    /// An ELPI list of `items`.
    pub fn list(items: Vec<Term>) -> Term {
        items.into_iter().rev().fold(Term::Const("[]".into()), |acc, x| Term::App("::".into(), vec![x, acc]))
    }

    fn to_value(&self) -> Value {
        let one = |k: &str, v: Value| Value::Object(Map::from_iter([(k.to_string(), v)]));
        match self {
            Term::Const(c) => one("c", Value::String(c.clone())),
            Term::App(c, a) => Value::Object(Map::from_iter([
                ("c".to_string(), Value::String(c.clone())),
                ("a".to_string(), Value::Array(a.iter().map(Term::to_value).collect())),
            ])),
            Term::Int(i) => one("i", Value::from(*i)),
            Term::Float(f) => one("f", serde_json::Number::from_f64(*f).map(Value::Number).unwrap_or(Value::Null)),
            Term::Str(s) => one("s", Value::String(s.clone())),
            Term::Var(v) => one("v", Value::String(v.clone())),
            Term::Other(o) => one("o", Value::String(o.clone())),
        }
    }

    fn from_value(v: &Value) -> std::result::Result<Term, String> {
        let o = v.as_object().ok_or_else(|| format!("a term must be a JSON object, got {v}"))?;
        let text = |k: &str, x: &Value| x.as_str().map(str::to_string).ok_or_else(|| format!("\"{k}\" must be a string"));
        if let Some(c) = o.get("c") {
            let c = text("c", c)?;
            return match o.get("a") {
                None => Ok(Term::Const(c)),
                Some(a) => {
                    let a = a.as_array().ok_or("\"a\" must be an array")?;
                    Ok(Term::App(c, a.iter().map(Term::from_value).collect::<std::result::Result<_, _>>()?))
                }
            };
        }
        if let Some(i) = o.get("i") {
            return match i {
                Value::Number(n) => Ok(n.as_i64().map(Term::Int).unwrap_or_else(|| Term::Other(n.to_string()))),
                _ => Err("\"i\" must be a number".into()),
            };
        }
        if let Some(f) = o.get("f") {
            return f.as_f64().map(Term::Float).ok_or_else(|| "\"f\" must be a number".into());
        }
        if let Some(s) = o.get("s") {
            return Ok(Term::Str(text("s", s)?));
        }
        if let Some(x) = o.get("v") {
            return Ok(Term::Var(text("v", x)?));
        }
        if let Some(x) = o.get("o") {
            return Ok(Term::Other(text("o", x)?));
        }
        Err(format!("not a term: {v}"))
    }
}

impl Serialize for Term {
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        self.to_value().serialize(s)
    }
}

impl<'de> Deserialize<'de> for Term {
    fn deserialize<D: Deserializer<'de>>(d: D) -> std::result::Result<Term, D::Error> {
        Term::from_value(&Value::deserialize(d)?).map_err(D::Error::custom)
    }
}

/// One answer: the query variables' values, as printed by ELPI and as terms, and the
/// suspended constraints.
#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct Solution {
    pub bindings: BTreeMap<String, String>,
    #[serde(default)]
    pub terms: BTreeMap<String, Term>,
    pub constraints: Vec<String>,
}

/// The outcome of [`Program::solve_host`].
#[derive(Debug, Clone, PartialEq)]
pub struct HostRun {
    pub solutions: Vec<Solution>,
    /// False when the limit cut the search short.
    pub exhausted: bool,
    /// Resolution steps the run took.
    pub fuel_used: u64,
}

#[derive(Deserialize)]
struct Answer {
    solutions: Vec<Solution>,
    exhausted: bool,
    #[serde(default, rename = "fuelUsed")]
    fuel_used: u64,
}

fn answer(json: &str) -> Result<Answer> {
    serde_json::from_str(json).map_err(|e| Error(format!("bad answer: {e}")))
}

type HostClosure<'a> = dyn FnMut(&str, &[Term]) -> std::result::Result<Vec<Vec<Term>>, String> + 'a;

/// A copy of `s` in memory from the C allocator, which the library releases with `free()`.
fn malloc_cstr(s: &str) -> *mut c_char {
    let bytes = s.as_bytes();
    // SAFETY: the buffer has room for the bytes and the NUL; a null result is passed on
    // (the library reads it as "no rows").
    unsafe {
        let p = ffi::malloc(bytes.len() + 1) as *mut u8;
        if !p.is_null() {
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), p, bytes.len());
            *p.add(bytes.len()) = 0;
        }
        p as *mut c_char
    }
}

fn panic_message(p: &(dyn std::any::Any + Send)) -> String {
    p.downcast_ref::<&str>().map(|s| s.to_string()).or_else(|| p.downcast_ref::<String>().cloned()).unwrap_or_else(|| "a panic".into())
}

/// The C host function: decodes the arguments, calls the closure behind `ctx` and encodes its
/// rows. A panic in the closure becomes an `{"error":..}` answer; it never unwinds into C.
extern "C" fn host_trampoline(ctx: *mut c_void, name: *const c_char, args: *const c_char) -> *mut c_char {
    let out = catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: `ctx` is the `&mut &mut HostClosure` that `solve_host` passed, alive and
        // exclusively ours for the synchronous call; `name` and `args` are NUL-terminated.
        let (f, name, args) = unsafe {
            (&mut *(ctx as *mut &mut HostClosure), CStr::from_ptr(name).to_string_lossy(), CStr::from_ptr(args).to_string_lossy())
        };
        let args: Vec<Term> = serde_json::from_str(&args).map_err(|e| format!("bad arguments: {e}"))?;
        f(&name, &args)
    }));
    let doc = match out {
        Ok(Ok(rows)) => serde_json::json!({ "rows": rows }),
        Ok(Err(msg)) => serde_json::json!({ "error": msg }),
        Err(p) => serde_json::json!({ "error": format!("host callback panicked: {}", panic_message(p.as_ref())) }),
    };
    malloc_cstr(&doc.to_string())
}

/// A compiled ELPI program.
#[derive(Debug)]
// @tg: implements:: [[openspec:language-bindings#Rust binding]]
pub struct Program {
    handle: u64,
}

// SAFETY: a handle is an index into a table inside the Lean runtime, which is thread-safe;
// the program it names is immutable.
unsafe impl Send for Program {}
unsafe impl Sync for Program {}

impl Program {
    /// Parse, typecheck and compile `source`.
    pub fn new(source: &str) -> Result<Program> {
        ensure_started()?;
        let src = cstr(source)?;
        let mut err = std::ptr::null_mut();
        let handle = unsafe { ffi::leanelpi_load(src.as_ptr(), &mut err) };
        if handle == INVALID {
            return Err(Error(unsafe { take(err) }));
        }
        Ok(Program { handle })
    }

    /// A new program with `clause` added; `self` is unchanged.
    pub fn assert_clause(&self, clause: &str) -> Result<Program> {
        let c = cstr(clause)?;
        let mut err = std::ptr::null_mut();
        let handle = unsafe { ffi::leanelpi_assert(self.handle, c.as_ptr(), &mut err) };
        if handle == INVALID {
            return Err(Error(unsafe { take(err) }));
        }
        Ok(Program { handle })
    }

    /// Run `query`, collecting at most `limit` solutions (`None` for all). Returns the
    /// solutions and whether the search was exhausted (false when `limit` cut it short).
    /// `fuel` bounds resolution steps; `None` uses the default budget.
    pub fn solve_with(&self, query: &str, limit: Option<u64>, fuel: Option<u64>) -> Result<(Vec<Solution>, bool)> {
        let q = cstr(query)?;
        let mut err = std::ptr::null_mut();
        let out = unsafe {
            ffi::leanelpi_solve(self.handle, q.as_ptr(), limit.unwrap_or(0), fuel.unwrap_or(0), &mut err)
        };
        if out.is_null() {
            return Err(Error(unsafe { take(err) }));
        }
        let a = answer(&unsafe { take(out) })?;
        Ok((a.solutions, a.exhausted))
    }

    /// A new program in which `name` is a host predicate with the declarations in `signature`
    /// (e.g. `"pred edge i:string, o:string."`, possibly with the kinds and types it uses).
    /// The program may already declare `name`, so its clauses can call it, but must not
    /// define clauses for it. `self` is unchanged. Calls are answered by the closure given to
    /// [`Program::solve_host`]; any other query that reaches it fails with an error.
    pub fn declare(&self, name: &str, signature: &str) -> Result<Program> {
        let (n, s) = (cstr(name)?, cstr(signature)?);
        let mut err = std::ptr::null_mut();
        let handle = unsafe { ffi::leanelpi_declare(self.handle, n.as_ptr(), s.as_ptr(), &mut err) };
        if handle == INVALID {
            return Err(Error(unsafe { take(err) }));
        }
        Ok(Program { handle })
    }

    /// Run `query`, answering every declared host predicate with `host`, synchronously on
    /// this thread. `host` receives the predicate name and one term per argument (unbound
    /// ones as [`Term::Var`]) and returns one row per answer, each holding a term for every
    /// output-mode argument, in order; no rows means failure, `Err` a runtime error.
    /// `limit` = 0 collects all solutions; `fuel` = 0 uses the default budget. Running out
    /// of fuel is an error for which [`Error::is_out_of_fuel`] holds.
    pub fn solve_host<F>(&self, query: &str, limit: usize, fuel: u64, host: F) -> Result<HostRun>
    where
        F: FnMut(&str, &[Term]) -> std::result::Result<Vec<Vec<Term>>, String>,
    {
        let q = cstr(query)?;
        let mut host = host;
        let mut f: &mut HostClosure = &mut host;
        let ctx = &mut f as *mut &mut HostClosure as *mut c_void;
        let mut err = std::ptr::null_mut();
        let out = unsafe {
            ffi::leanelpi_solve_host(self.handle, q.as_ptr(), limit as u64, fuel, host_trampoline, ctx, &mut err)
        };
        if out.is_null() {
            return Err(Error(unsafe { take(err) }));
        }
        let a = answer(&unsafe { take(out) })?;
        Ok(HostRun { solutions: a.solutions, exhausted: a.exhausted, fuel_used: a.fuel_used })
    }

    /// All solutions of `query`.
    pub fn solve(&self, query: &str) -> Result<Vec<Solution>> {
        Ok(self.solve_with(query, None, None)?.0)
    }

    /// The first solution of `query`, or `None` when it fails.
    pub fn first(&self, query: &str) -> Result<Option<Solution>> {
        Ok(self.solve_with(query, Some(1), None)?.0.into_iter().next())
    }

    /// Whether `query` has a solution.
    pub fn ask(&self, query: &str) -> Result<bool> {
        Ok(self.first(query)?.is_some())
    }
}

impl Drop for Program {
    fn drop(&mut self) {
        unsafe { ffi::leanelpi_free(self.handle) }
    }
}
