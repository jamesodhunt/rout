// Copyright (c) 2021 James O. D. Hunt.
//
// SPDX-License-Identifier: Apache-2.0
//

// Range of legal UTF-8 character values.
//
// See: https://tools.ietf.org/html/rfc3629
pub const UTF8_MIN_VALUE: char = '\u{000000}';
pub const UTF8_MAX_VALUE: char = '\u{10FFFF}';

// Escape values that rust doesn't itself support natively.
// See:
//
// - https://static.rust-lang.org/doc/master/reference.html#byte-escapes
// - ascii(7) for details of the hex values.
pub const ESCAPE_A: char = 0x07 as char;
pub const ESCAPE_B: char = 0x08 as char;
pub const ESCAPE_E: char = 0x1b as char;
pub const ESCAPE_F: char = 0x0c as char;
pub const ESCAPE_V: char = 0x0b as char;

// 16 bit max value
pub const UTF8_MAX_2_BYTE_VALUE: char = '\u{10000}';

pub const UTF_MAX_ALIAS: &str = "max";
pub const UTF_MIN_ALIAS: &str = "min";
pub const UTF_START_ALIAS: &str = "start";
pub const UTF_END_ALIAS: &str = "end";
