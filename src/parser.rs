// Copyright (c) 2021 James O. D. Hunt.
//
// SPDX-License-Identifier: Apache-2.0
//

use crate::values::*;
use anyhow::{anyhow, Result};
use std::char;

use crate::command::{Command, CommandList, Output, Range};

type PResult<T> = std::result::Result<T, Error<Rule>>;

type Node<'i> = pest_consume::Node<'i, Rule, ()>;

use pest_consume::{match_nodes, Error, Parser};

#[derive(Parser)]
#[grammar = "rout.pest"]
struct ROUTParser;

// Convert the specified value in the specified base into a number, but only if it has the
// expected one character prefix and len digits.
//
// Note: the checks performed are arguably "pointless" since they are enforced
// by the grammar. But grammars can change...
fn base_str_to_int(prefix: char, len: usize, value: &str, base: u32) -> Result<usize> {
    if prefix == '0' || prefix == '\0' {
        return Err(anyhow!("prefix cannot be blank"));
    }

    if len == 0 {
        return Err(anyhow!("length cannot be zero"));
    }

    if value.is_empty() {
        return Err(anyhow!("value cannot be blank"));
    }

    if !value.starts_with(prefix) {
        return Err(anyhow!(
            "value {:?} does not have {:?} prefix",
            value,
            prefix
        ));
    }

    let numeric_part = &value[1..];

    let actual_len = numeric_part.len();

    if actual_len != len {
        return Err(anyhow!(
            "incorrect length of numeric: expected {}, got {}",
            len,
            value.len()
        ));
    }

    let numeric = usize::from_str_radix(numeric_part, base)?;

    Ok(numeric)
}

#[pest_consume::parser]
impl ROUTParser {
    fn EOI(_input: Node) -> PResult<()> {
        Ok(())
    }

    fn escaped_hex_value<'a>(input: Node) -> PResult<Command> {
        match_nodes!(input.into_children();
            [hex_value(v)] => Ok(Command::LiteralChar(v)),
        )
    }

    fn escaped_octal_value<'a>(input: Node) -> PResult<Command> {
        match_nodes!(input.into_children();
            [octal_value(v)] => Ok(Command::LiteralChar(v)),
        )
    }

    fn escaped_unicode_value<'a>(input: Node) -> PResult<Command> {
        match_nodes!(input.into_children();
            [escaped_short_unicode_value(v)] => Ok(Command::LiteralChar(v)),
            [escaped_long_unicode_value(v)] => Ok(Command::LiteralChar(v)),
        )
    }

    fn escaped_short_unicode_value(input: Node) -> PResult<char> {
        match_nodes!(
            input.into_children();
            [short_unicode_value(v)] => Ok(v),
        )
    }

    fn escaped_long_unicode_value(input: Node) -> PResult<char> {
        match_nodes!(
            input.into_children();
            [long_unicode_value(v)] => Ok(v),
        )
    }

    fn escaped_printf_value<'a>(input: Node) -> PResult<Command> {
        let value = input.as_str();

        let expected_len = 2;

        if value.len() != expected_len {
            return Err(input.error(anyhow!(
                "expected length {:?}, got {:?}",
                expected_len,
                value.len()
            )));
        }

        let mut chars = value.chars();

        let prefix = '\\';

        let first_char = chars.next().unwrap();
        if first_char != prefix {
            return Err(input.error(anyhow!("expected {:?}, got {:?}", prefix, first_char)));
        }

        // Unwrap is safe as we've checked the length
        let escaped_char = chars.next().unwrap();

        let cmd = match escaped_char {
            '0' => Command::Escaped('\0'),
            'a' => Command::Escaped(ESCAPE_A),
            'b' => Command::Escaped(ESCAPE_B),
            'c' => Command::Output(Output::Discard),
            '"' => Command::Escaped('"'),
            '\\' => Command::Escaped('\\'),
            'e' => Command::Escaped(ESCAPE_E),
            'f' => Command::Escaped(ESCAPE_F),
            'g' => Command::Random,
            'n' => Command::Escaped('\n'),
            'r' => Command::Escaped('\r'),
            't' => Command::Escaped('\t'),
            'v' => Command::Escaped(ESCAPE_V),

            // XXX: This is an impossible situation since the grammar enforces
            // the permitted syntax. However, by leaving this hear, we have
            // protection in case the grammar changes at some future stage.
            _ => return Err(input.error(anyhow!("invalid escaped character: {:?}", escaped_char))),
        };

        Ok(cmd)
    }

    fn unescaped_char<'a>(input: Node) -> PResult<Command> {
        let lit = input.as_str().to_string().chars().next().unwrap();

        Ok(Command::LiteralChar(lit))
    }

    fn unescaped_chars<'a>(input: Node) -> PResult<CommandList> {
        let value: &String = &input.as_str().to_owned();

        if value.len() > 1 {
            // Represent a "run" of characters
            // (more efficient than 'n' LiteralChar's!)
            Ok(Command::LiteralString(value.to_string()).into())
        } else {
            Ok(Command::LiteralChar(value.chars().next().unwrap()).into())
        }
    }

    fn hex_range(input: Node) -> PResult<Range> {
        match_nodes!(
            input.into_children();
            [hex_value(a),hex_value(b)] => Ok(Range(a, b))
        )
    }

    fn short_unicode_range(input: Node) -> PResult<Range> {
        match_nodes!(
                input.into_children();
                [short_unicode_value(a),short_unicode_value(b)] => Ok(Range(a, b)))
    }

    fn long_unicode_range(input: Node) -> PResult<Range> {
        match_nodes!(
                input.into_children();
                [long_unicode_value(a),long_unicode_value(b)] => Ok(Range(a, b)))
    }

    fn hex_value(input: Node) -> PResult<char> {
        let value = base_str_to_int('x', 2, input.as_str(), 16).map_err(|e| input.error(e))?;

        let ch = value as u8 as char;

        Ok(ch)
    }

    fn octal_value(input: Node) -> PResult<char> {
        let value = base_str_to_int('o', 3, input.as_str(), 8).map_err(|e| input.error(e))?;

        let ch = value as u8 as char;

        Ok(ch)
    }

    fn short_unicode_hex_value(input: Node) -> PResult<char> {
        let value = base_str_to_int('u', 4, input.as_str(), 16).map_err(|e| input.error(e))?;

        let ch = char::from_u32(value as u32)
            .ok_or("failed to handle short unicode character")
            .map_err(|e| input.error(e))?;

        Ok(ch)
    }

    fn short_unicode_value(input: Node) -> PResult<char> {
        match_nodes!(
            input.into_children();
            [short_unicode_hex_value(r)] => Ok(r),
            [short_unicode_end_marker(r)] => Ok(r),
        )
    }

    fn long_unicode_hex_value(input: Node) -> PResult<char> {
        let value = base_str_to_int('U', 8, input.as_str(), 16).map_err(|e| input.error(e))?;

        let ch = char::from_u32(value as u32)
            .ok_or(format!(
                "failed to handle long unicode character (range is U{:08x}-U{:08x})",
                UTF8_MIN_VALUE as usize, UTF8_MAX_VALUE as usize,
            ))
            .map_err(|e| input.error(e))?;

        Ok(ch)
    }

    fn long_unicode_end_marker(input: Node) -> PResult<char> {
        let value = input.as_str().to_string();

        let prefix = 'U';

        let min_values = vec![
            format!("{}{}", prefix, UTF_MIN_ALIAS),
            format!("{}{}", prefix, UTF_START_ALIAS),
        ];

        let max_values = vec![
            format!("{}{}", prefix, UTF_MAX_ALIAS),
            format!("{}{}", prefix, UTF_END_ALIAS),
        ];

        let result = if min_values.contains(&value) {
            UTF8_MIN_VALUE
        } else if max_values.contains(&value) {
            UTF8_MAX_VALUE
        } else {
            return Err(input.error(anyhow!("impossible lon unicode marker")));
        };

        Ok(result)
    }

    fn short_unicode_end_marker(input: Node) -> PResult<char> {
        let value = input.as_str().to_string();

        let prefix = 'u';

        let min_values = vec![
            format!("{}{}", prefix, UTF_MIN_ALIAS),
            format!("{}{}", prefix, UTF_START_ALIAS),
        ];

        let max_values = vec![
            format!("{}{}", prefix, UTF_MAX_ALIAS),
            format!("{}{}", prefix, UTF_END_ALIAS),
        ];

        let result = if min_values.contains(&value) {
            UTF8_MIN_VALUE
        } else if max_values.contains(&value) {
            UTF8_MAX_2_BYTE_VALUE
        } else {
            return Err(input.error(anyhow!("impossible short unicode marker")));
        };

        Ok(result)
    }

    fn long_unicode_value(input: Node) -> PResult<char> {
        match_nodes!(
            input.into_children();
            [long_unicode_hex_value(r)] => Ok(r),
            [long_unicode_end_marker(r)] => Ok(r),
        )
    }

    fn unicode_range(input: Node) -> PResult<Range> {
        match_nodes!(
            input.into_children();
            [short_unicode_range(r)] => Ok(r),
            [long_unicode_range(r)] => Ok(r),
        )
    }

    fn octal_range(input: Node) -> PResult<Range> {
        match_nodes!(
            input.into_children();
            [octal_value(a),octal_value(b)] => Ok(Range(a, b))
        )
    }

    fn non_whitespace_char(input: Node) -> PResult<char> {
        let value = input.as_str().to_string();

        let ch = value
            .chars()
            .next()
            .ok_or("failed to handle non-whitespace character")
            .map_err(|e| input.error(e))?;

        Ok(ch)
    }

    fn single_glyph_range(input: Node) -> PResult<Range> {
        match_nodes!(input.into_children();
        [non_whitespace_char(a),non_whitespace_char(b)] => Ok(Range(a, b))
        )
    }

    fn range_escaped_value(input: Node) -> PResult<Range> {
        match_nodes!(input.into_children();
            [single_glyph_range(r)] => Ok(r),
            [hex_range(r)] => Ok(r),
            [octal_range(r)] => Ok(r),
            [unicode_range(r)] => Ok(r),
        )
    }

    fn simple_escaped_value<'a>(input: Node) -> PResult<Command> {
        match_nodes!(input.into_children();
            [escaped_printf_value(v)] => Ok(v),
            [escaped_hex_value(v)] => Ok(v),
            [escaped_octal_value(v)] => Ok(v),
            [escaped_unicode_value(v)] => Ok(v),
        )
    }

    fn escaped_value<'a>(input: Node) -> PResult<Command> {
        match_nodes!(input.into_children();
            [simple_escaped_value(s)] => Ok(s),
            [range_escaped_value(r)] => Ok(Command::Range(r)),
        )
    }

    fn escaped_values<'a>(input: Node) -> PResult<CommandList> {
        match_nodes!(input.into_children();
            [escaped_value(v)..] => Ok(v.collect()),
        )
    }

    // We need to return a CommandList to handle multiple escaped values;
    // multiple character values don't strictly need a list due to the
    // LiteralString command
    fn string_chars<'a>(input: Node) -> PResult<CommandList> {
        match_nodes!(input.into_children();
            [escaped_values(v)] => Ok(v),
            [unescaped_chars(v)] => Ok(v),
        )
    }

    fn string_inner<'a>(input: Node) -> PResult<CommandList> {
        match_nodes!(input.into_children();
            [string_chars(values)..] => {
                let mut v = vec![];

                for mut elem in values {
                        v.append(&mut elem);
                }

                Ok(v)
            },
        )
    }

    fn string<'a>(input: Node) -> PResult<CommandList> {
        match_nodes!(input.into_children();
            [string_inner(v)] => Ok(v),
        )
    }

    fn input<'a>(input: Node) -> PResult<CommandList> {
        match_nodes!(input.into_children();
            [string(v), _] => Ok(v),
        )
    }
}

//--------------------------------------------------------------------

/// Parse a string value, returning a list of commands that the string
/// represents. To generate output the commands must be executed by calling
/// the `run()` method.
///
/// # Arguments
///
/// `value` - String to parse
pub fn parse_string<'a>(value: &str) -> Result<CommandList> {
    let inputs = ROUTParser::parse(Rule::input, value)
        .map_err(|e| anyhow!(e).context("failed to parse input"))?;

    let input = inputs.single()?;

    Ok(ROUTParser::input(input)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_string() {
        type ErrorPrefix = String;

        #[derive(Debug)]
        struct TestData<'a> {
            // Use a raw string if you need to include
            // escape characters (to avoid having to use
            // a double backslash)
            str: &'a str,
            result: std::result::Result<CommandList, ErrorPrefix>,
        }

        let tests = &[
            TestData {
                str: "",
                result: Ok(vec![]),
            },
            TestData {
                str: " ",
                result: Ok(vec![Command::LiteralChar(' ')]),
            },
            TestData {
                str: "  ",
                result: Ok(vec![Command::LiteralString("  ".into())]),
            },
            TestData {
                str: "a",
                result: Ok(vec![Command::LiteralChar('a')].into()),
            },
            TestData {
                str: "aa",
                result: Ok(vec![Command::LiteralString("aa".into())].into()),
            },
            TestData {
                str: "floop",
                result: Ok(vec![Command::LiteralString("floop".into())].into()),
            },
            TestData {
                str: r#"hello\n"#,
                result: Ok(vec![
                    Command::LiteralString("hello".into()),
                    Command::Escaped('\n'),
                ]
                .into()),
            },
            TestData {
                str: r#"\0"#,
                result: Ok([Command::Escaped('\0')].to_vec()),
            },
            TestData {
                str: r#"\a"#,
                result: Ok([Command::Escaped(ESCAPE_A)].to_vec()),
            },
            TestData {
                str: r#"\b"#,
                result: Ok([Command::Escaped(ESCAPE_B)].to_vec()),
            },
            TestData {
                str: r#"\c"#,
                result: Ok([Command::Output(Output::Discard)].to_vec()),
            },
            TestData {
                str: r#"\""#,
                result: Ok([Command::Escaped('"')].to_vec()),
            },
            TestData {
                str: r#"\\"#,
                result: Ok([Command::Escaped('\\')].to_vec()),
            },
            TestData {
                str: r#"\e"#,
                result: Ok([Command::Escaped(ESCAPE_E)].to_vec()),
            },
            TestData {
                str: r#"\f"#,
                result: Ok([Command::Escaped(ESCAPE_F)].to_vec()),
            },
            TestData {
                str: r#"\g"#,
                result: Ok([Command::Random].to_vec()),
            },
            TestData {
                str: r#"\n"#,
                result: Ok(vec![Command::Escaped('\n')].into()),
            },
            TestData {
                str: r#"\n\n"#,
                result: Ok(vec![Command::Escaped('\n'), Command::Escaped('\n')].into()),
            },
            TestData {
                str: r#"\r"#,
                result: Ok(vec![Command::Escaped('\r')].into()),
            },
            TestData {
                str: r#"\r\r"#,
                result: Ok(vec![Command::Escaped('\r'), Command::Escaped('\r')].into()),
            },
            TestData {
                str: r#"\t"#,
                result: Ok(vec![Command::Escaped('\t')].into()),
            },
            TestData {
                str: r#"\v"#,
                result: Ok(vec![Command::Escaped(ESCAPE_V)].into()),
            },
            TestData {
                str: r#"\z"#,
                result: Err("failed to parse input".into()),
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            // Create a string containing details of the test
            let msg = format!("test[{}]: {:?}", i, d);

            // Call the function under test
            let result = parse_string(d.str);

            // Update the test details string with the results of the call
            let msg = format!("{}, result: {:?}", msg, result);

            // Perform the checks
            if d.result.is_err() {
                assert!(result.is_err(), "{}", msg);

                let expected_err_prefix = d.result.as_ref().err().unwrap();
                let actual_err_prefix = format!("{}", result.as_ref().err().unwrap());

                assert!(
                    actual_err_prefix.starts_with(expected_err_prefix),
                    "{}",
                    msg
                );

                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            let expected_cmds = d.result.as_ref().unwrap().clone();
            let actual_cmds = result.unwrap();

            assert_eq!(expected_cmds, actual_cmds, "{}", msg);
        }
    }
}
