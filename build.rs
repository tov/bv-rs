extern crate rustc_version;

use rustc_version::{version, Version, Result};

fn main() -> Result<()> {
    if version()? >= Version::parse("1.26.0")? || true {
        println!("cargo:rustc-cfg=u128");
    }

    Ok(())
}