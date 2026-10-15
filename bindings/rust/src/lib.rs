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
//! Bindings come back as the strings ELPI prints. A [`Program`] is an immutable value:
//! [`Program::assert_clause`] returns a new one. Programs may be shared across threads.

use std::collections::BTreeMap;
use std::ffi::{c_char, CStr, CString};
use std::fmt;
use std::sync::Once;

use serde::Deserialize;

mod ffi {
    use std::ffi::c_char;
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
        pub fn leanelpi_free_string(s: *mut c_char);
    }
}

const INVALID: u64 = u64::MAX;

/// A parse, type or runtime error reported by the engine, or a bad argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(pub String);

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

/// One answer: the query variables' values, as printed by ELPI, and suspended constraints.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Solution {
    pub bindings: BTreeMap<String, String>,
    pub constraints: Vec<String>,
}

#[derive(Deserialize)]
struct Answer {
    solutions: Vec<Solution>,
    exhausted: bool,
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
        let json = unsafe { take(out) };
        let a: Answer = serde_json::from_str(&json).map_err(|e| Error(format!("bad answer: {e}")))?;
        Ok((a.solutions, a.exhausted))
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
