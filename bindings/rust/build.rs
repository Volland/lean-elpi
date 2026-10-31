//! Links `libleanelpi`, built by `scripts/build-ffi.sh`. Set `LEANELPI_DIST` to the
//! directory holding it; the default is `dist/` of the repository this crate sits in.
use std::{env, path::PathBuf};

fn main() {
    // docs.rs has no library to link, and documentation does not need one.
    if env::var_os("DOCS_RS").is_some() {
        return;
    }
    println!("cargo:rerun-if-env-changed=LEANELPI_DIST");
    let dist = env::var_os("LEANELPI_DIST").map(PathBuf::from).unwrap_or_else(|| {
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("../../dist")
    });
    let dist = dist.canonicalize().unwrap_or_else(|_| {
        panic!("{} not found: run scripts/build-ffi.sh or set LEANELPI_DIST", dist.display())
    });
    // A copy in OUT_DIR: cargo puts search paths inside the target directory on
    // the loader path of `cargo test` and `cargo run`, so dependent crates'
    // tests and binaries find the library without an rpath of their own.
    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    for entry in std::fs::read_dir(&dist).into_iter().flatten().flatten() {
        let name = entry.file_name();
        let n = name.to_string_lossy();
        if n.starts_with("libleanelpi.") || n.starts_with("libleanshared") {
            println!("cargo:rerun-if-changed={}", entry.path().display());
            let _ = std::fs::copy(entry.path(), out.join(&name));
        }
    }
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-search=native={}", dist.display());
    println!("cargo:rustc-link-lib=dylib=leanelpi");
    // The loader must find libleanelpi when a binary built here runs.
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dist.display());
}
