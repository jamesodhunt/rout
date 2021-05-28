// Copyright (c) 2021 James O. D. Hunt.
//
// SPDX-License-Identifier: Apache-2.0
//

use anyhow::Result;
use std::process::exit;

#[macro_use]
#[cfg(test)]
extern crate lazy_static;

mod args;
mod command;
mod parser;
mod values;

fn real_main() -> Result<()> {
    args::parse_args()
}

fn main() {
    if let Err(e) = real_main() {
        eprintln!("ERROR: {}", e);
        exit(1);
    };
}
