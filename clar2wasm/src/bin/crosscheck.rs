mod utils;
use std::fs;

use clap::Parser;
use clar2wasm::tools::{
    crosscheck_compare_only_with_epoch_and_version,
    crosscheck_oom_compare_only_with_epoch_and_version,
};
use utils::*;

/// crosscheck is a tool to compare the results of the compiled and interpreted
/// versions of a Clarity snippet.
#[derive(Parser)]
#[command(name = "crosscheck", version = env!("CARGO_PKG_VERSION"))]
struct Args {
    /// Clarity source file to compile
    input: String,
    /// Epoch of the stacks chain
    #[arg(long)]
    stacks_epoch: Option<WrappedEpochId>,
    /// The clarity version to use
    #[arg(long)]
    clarity_version: Option<WrappedClarityVersion>,
    /// To run crosscheck with Out Of Memory check
    #[arg(long, default_value_t = false)]
    crosscheck_oom: bool,
}

fn main() {
    let args = Args::parse();

    // Require a .clar extension
    if !args.input.ends_with(".clar") {
        eprintln!("Input file must have a .clar extension");
        std::process::exit(1);
    }

    // Read the file.
    let source = match fs::read_to_string(args.input.as_str()) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("Error reading file: {error}");
            std::process::exit(1);
        }
    };

    let epoch = args.stacks_epoch.unwrap_or_default().into();
    let version = args.clarity_version.unwrap_or_default().into();

    if args.crosscheck_oom {
        println!("Running Crosscheck OOM");
        crosscheck_oom_compare_only_with_epoch_and_version(&source, epoch, version);
    } else {
        println!("Running Crosscheck");
        crosscheck_compare_only_with_epoch_and_version(&source, epoch, version);
    }
}
