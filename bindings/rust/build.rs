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
    println!("cargo:rustc-link-search=native={}", dist.display());
    println!("cargo:rustc-link-lib=dylib=leanelpi");
    // The loader must find libleanelpi when a binary built here runs.
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dist.display());
}
