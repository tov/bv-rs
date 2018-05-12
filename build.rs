use std::env;
use std::io::Write;
use std::process::{Command, Stdio};

fn main() {
    if probe_type("u128") {
        enable_cfg("int_128");
    }

    if probe_type("::std::ops::RangeInclusive<u64>") {
        enable_cfg("inclusive_range");
    }
}

/// Enables `--cfg feature` for the current build.
fn enable_cfg(feature: &str) {
    println!("cargo:rustc-cfg={}", feature);
}

/// Tests if a type is defined.
fn probe_type(type_string: &str) -> bool {
    probe(&format!("type T = {}; fn main() {{ }}", type_string))
}

/// Tests if a program can be compiled.
///
/// From
/// [the `num-traits` crate](https://github.com/rust-num/num-traits/commit/51f6c57c4b2f6e3483164af7cad32690e4013b06#diff-a7b0a2dee0126cddf994326e705a91ea).
fn probe(code: &str) -> bool {
    let rustc = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let out_dir = env::var_os("OUT_DIR").expect("environment variable OUT_DIR");

    let mut child = Command::new(rustc)
        .arg("--out-dir")
        .arg(out_dir)
        .arg("--emit=obj")
        .arg("-")
        .stdin(Stdio::piped())
        .spawn()
        .expect("rustc probe");

    child
        .stdin
        .as_mut()
        .expect("rustc stdin")
        .write_all(code.as_bytes())
        .expect("write rustc stdin");

    child.wait().expect("rustc probe").success()
}