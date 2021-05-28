// Copyright (c) 2021 James O. D. Hunt.
//
// SPDX-License-Identifier: Apache-2.0
//

use anyhow::{anyhow, Result};
use ap::{App, Arg, Args, Error, Handler, Need, Result as APResult, POSITIONAL_HANDLER_OPT};
use std::time::Duration;

use crate::command::{Command, Commands, Output};
use crate::parser;
use crate::values::*;

#[derive(Clone, Debug, Default)]
struct ArgHandler {
    cmds: Commands,
}

const SECONDS_IN_MINUTE: u64 = 60;
const SECONDS_IN_HOUR: u64 = SECONDS_IN_MINUTE * 60;
const SECONDS_IN_DAY: u64 = SECONDS_IN_HOUR * 24;

// A centi-second is 1/100 second.
const CS_IN_MILLI_SECOND: u64 = 10;

// a deci-second is 1/10 second.
const DS_IN_MILLI_SECOND: u64 = 100;

const REPEAT_FOREVER: isize = -1;

const ERR_NEED_DURATION: &str = "must specify time duration";
const ERR_BAD_DURATION_SUFFIX: &str = "invalid time duration suffix";
const ERR_INTRA_CHAR_LEN: &str = "intra character must be single character";
const ERR_NO_INTRA_CHAR: &str = "missing intra character";
const ERR_MISSING_OPT_VALUE: &str = "missing option value";

// TODO: Add in support for "-1" as Duration::MAX once MAX
// is no longer experimental.
const DURATION_MAX: u32 = 1_000_000_000 - 1;

impl ArgHandler {
    fn handle_flag(&mut self, arg: Arg) -> Result<()> {
        let cmd = match arg.option {
            'e' => Command::Output(Output::Stderr),
            'o' => Command::Output(Output::Stdout),
            't' => Command::Output(Output::Terminal),
            _ => return Err(anyhow!("invalid flag: {:?}", arg.option)),
        };

        cmd.run(&mut self.cmds)
    }

    fn handle_option(&mut self, arg: Arg) -> Result<()> {
        let value = arg
            .value
            .ok_or(ERR_MISSING_OPT_VALUE)
            .map_err(|e| anyhow!(e))?;

        let cmd = match arg.option {
            'a' => handle_cmd_intra_char(&value)?,
            'b' => handle_cmd_intra_pause(&value)?,
            'r' => handle_cmd_repeat(&value)?,
            's' => handle_cmd_sleep(&value)?,
            'u' => handle_cmd_fd(&value)?,
            'x' => handle_cmd_exit(&value)?,
            _ => return Err(anyhow!("invalid option: {:?}", arg.option)),
        };

        match cmd {
            Command::IntraChar(ch) => self.cmds.handle_intra_char(ch),
            Command::IntraPause(duration) => self.cmds.set_intra_pause(duration),
            _ => cmd.run(&mut self.cmds),
        }
    }

    fn handle_positional(&mut self, arg: Arg) -> Result<()> {
        if let Some(value) = arg.value {
            let cmds_list =
                parser::parse_string(&value).map_err(|e| ap::Error::HandlerError(e.to_string()))?;

            let saved_cmds_list = cmds_list.clone();

            for cmd in cmds_list {
                let cmd_copy = cmd.clone();

                cmd.run(&mut self.cmds)
                    .map_err(|e| Error::HandlerError(e.to_string()))?;

                // Handle the intras, but only if we haven't just handled
                // a string (since that handles intras itself).
                match cmd_copy {
                    Command::LiteralString(_) => (),
                    _ => self
                        .cmds
                        .handle_intras()
                        .map_err(|e| Error::HandlerError(e.to_string()))?,
                };
            }

            self.cmds.set_prev_cmdlist(saved_cmds_list);
        };

        Ok(())
    }
}

fn handle_cmd_exit(value: &str) -> Result<Command> {
    let count = value.parse::<i32>()?;

    // See exit(3)
    let exit_value = count & 0xff;

    Ok(Command::Exit(exit_value))
}

fn handle_cmd_repeat(value: &str) -> Result<Command> {
    let mut count = match value {
        "forever" => REPEAT_FOREVER,
        _ => value.parse::<isize>()?,
    };

    // A negative values only makes sense if
    // it's "forever".
    if count < 0 {
        count = REPEAT_FOREVER;
    }

    Ok(Command::Repeat(count))
}

fn handle_cmd_sleep(value: &str) -> Result<Command> {
    let duration = parse_time(value)?;

    Ok(Command::Sleep(duration))
}

fn handle_cmd_fd(value: &str) -> Result<Command> {
    let fd = value.parse::<u32>()?;

    Ok(Command::Output(Output::FileDescriptor(fd)))
}

fn handle_cmd_intra_char(value: &str) -> Result<Command> {
    // This is essential to allow the intra character to be removed after
    // having set it. For example
    //
    //   $ rout -a . hello -a '' " world\n"
    //
    // ... should produce this output:
    //
    //   h.e.l.l.o. world
    //
    if value.is_empty() {
        return Ok(Command::IntraChar('\0'));
    }

    let mut chars = value.chars();

    if chars.clone().count() > 1 {
        return Err(anyhow!(ERR_INTRA_CHAR_LEN));
    }

    let first = chars
        .next()
        .ok_or(ERR_NO_INTRA_CHAR)
        .map_err(|e| anyhow!(e))?;

    Ok(Command::IntraChar(first))
}

fn handle_cmd_intra_pause(value: &str) -> Result<Command> {
    let duration = parse_time(value)?;

    Ok(Command::IntraPause(duration))
}

fn parse_time(value: &str) -> Result<Duration> {
    if value.is_empty() {
        Err(anyhow!(ERR_NEED_DURATION))
    } else if value == "-1" {
        let max = Duration::new(u64::MAX, DURATION_MAX);

        Ok(max)
    } else if let Some(i) = value.find(char::is_alphabetic) {
        let prefix = &value[..i];

        let numeric = prefix.parse::<u64>()?;

        let suffix = &value[i..];

        let duration = match suffix {
            "d" => Duration::from_secs(numeric * SECONDS_IN_DAY),
            "h" => Duration::from_secs(numeric * SECONDS_IN_HOUR),
            "m" => Duration::from_secs(numeric * SECONDS_IN_MINUTE),
            "s" => Duration::from_secs(numeric),
            "cs" => Duration::from_millis(numeric * CS_IN_MILLI_SECOND),
            "ds" => Duration::from_millis(numeric * DS_IN_MILLI_SECOND),
            "ms" => Duration::from_millis(numeric),
            "ns" => Duration::from_nanos(numeric),
            "us" => Duration::from_micros(numeric),

            _ => return Err(anyhow!(ERR_BAD_DURATION_SUFFIX)),
        };

        Ok(duration)
    } else {
        let secs = value.parse::<u64>()?;

        // "bare" numeric value (no suffix)
        Ok(Duration::from_secs(secs))
    }
}

impl Handler for &mut ArgHandler {
    fn handle(&mut self, arg: Arg) -> APResult<()> {
        if arg.option == POSITIONAL_HANDLER_OPT {
            self.handle_positional(arg)
                .map_err(|e| ap::Error::HandlerError(e.to_string()))?;
        } else {
            match arg.needs {
                Need::Nothing => self.handle_flag(arg),
                Need::Argument => self.handle_option(arg),
            }
            .map_err(|e| ap::Error::HandlerError(e.to_string()))?;
        }

        Ok(())
    }
}

pub fn parse_args() -> Result<()> {
    let mut args = Args::default();

    args.add(
        Arg::new('a')
            .needs(Need::Argument)
            .help("Insert specified character (which may be a 1-character escape character) between all output characters."),
    );

    args.add(
        Arg::new('b')
            .needs(Need::Argument)
            .help("Pause between writing each character."),
    );

    args.add(Arg::new('e').help("Write subsequent strings to standard error (file descriptor 2)."));

    args.add(
        Arg::new('o').help("Write subsequent strings to standard output (file descriptor 1)."),
    );

    args.add(
        Arg::new('r')
            .needs(Need::Argument)
            .help("Repeat previous value specified number of times."),
    );

    args.add(
        Arg::new('s')
            .needs(Need::Argument)
            .help("Sleep for specified amount of time."),
    );

    args.add(Arg::new('t').help("Write subsequent strings directly to terminal."));

    args.add(
        Arg::new('u')
            .needs(Need::Argument)
            .help("Write subsequent strings to specified file descriptor."),
    );

    args.add(
        Arg::new('x')
            .needs(Need::Argument)
            .help("Exit with specified value."),
    );

    let posn_help = "\
    Quoted or unquoted string positional arguments are displayed\n\
    verbatim. A variety of escaped values are also supported \
    (see below).";

    args.add(Arg::new(POSITIONAL_HANDLER_OPT).help(posn_help));

    let mut handler = ArgHandler::default();

    let help_text = "
    Strings are displayed as specified. However, \
    certain non-printable characters can be specified\n\
    with escape sequences, like echo(1) and printf(1).

Escape Characters:

  '\\0'         - null byte
  '\\a'         - alert (bell)
  '\\b'         - backspace
  '\\c'         - no further output
  '\\e'         - escape character
  '\\f'         - form feed
  '\\g'         - generate pseudo-random printable character
  '\\n'         - newline
  '\\oNNN'      - 1-byte octal character (1-3 digits)
  '\\r'         - carriage return
  '\\t'         - horizontal tab
  '\\uNNNN'     - 2-byte unicode/UTF-8 character (4 hex digits)
  '\\UNNNNNNNN' - 4-byte unicode/UTF-8 character (8 hex digits)
  '\\v'         - vertical tab
  '\\xNN'       - 1-byte hexadecimal character (1-2 digits)

Ranges:

  '\\{N..N}'                 - Specify a range by two 1-character literal characters.
  '\\{xNN..xNN}'             - Specify a range by two 2-digit hex values.
  '\\{oNNN..oNNN}'           - Specify a range by two 3-digit octal values.
  '\\{uNNNN..uNNNN}'         - Specify a range by two 4-digit unicode values.
  '\\{UNNNNNNNN..UNNNNNNNN}' - Specify a range by two 8-digit unicode values.
    ";

    let notes_text = format!(
        "
- Arguments are processed in order.
- With the exception of '-x', arguments may be repeated any number of times.
- If <repeat> is '-1', repeat forever.
- Replace the 'Z' in the range formats above with the appropriate characters.
- Ranges can be either ascending or descending.
- Unicode ranges can use a short-hand syntax:
  - Initial values can be specified as {:?} or {:?}.
  - Final values can be specified as {:?} or {:?}.
- <delay> can take the following forms where <num> is a positive integer:

    <num>ns : nano-seconds (1/1,000,000,000 second)
    <num>us : micro-seconds (1/1,000,000 second)
    <num>ms : milli-seconds (1/1,000 second)
    <num>cs : centi-seconds (1/100 second)
    <num>ds : deci-seconds (1/10 second)
    <num>s  : seconds
    <num>m  : minutes
    <num>h  : hours
    <num>d  : days
    <num>   : seconds

- Generated printable random characters will not display
  unless you are using an appropriate font.",
        UTF_MIN_ALIAS, UTF_START_ALIAS, UTF_MAX_ALIAS, UTF_END_ALIAS
    );

    let mut app = App::new("rout")
        .args(args)
        .help(help_text)
        .notes(&notes_text)
        .handler(Box::new(&mut handler));

    app.parse()?;

    drop(app);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use nix::fcntl::OFlag;
    use nix::unistd::{close, pipe2};
    use std::fs::File;
    use std::io::Read;
    use std::os::unix::io::FromRawFd;

    #[derive(Debug)]
    struct ParseTimeTestData<'a> {
        value: &'a str,
        result: Result<Duration>,
    }

    lazy_static! {
        static ref PARSE_TIME_TEST_DATA: [ParseTimeTestData<'static>; 18] = [
            ParseTimeTestData {
                value: "",
                result: Err(anyhow!(ERR_NEED_DURATION)),
            },
            ParseTimeTestData {
                value: "1z",
                result: Err(anyhow!(ERR_BAD_DURATION_SUFFIX)),
            },
            ParseTimeTestData {
                value: "17foo",
                result: Err(anyhow!(ERR_BAD_DURATION_SUFFIX)),
            },
            ParseTimeTestData {
                value: "0",
                result: Ok(Duration::from_secs(0)),
            },
            ParseTimeTestData {
                value: "1",
                result: Ok(Duration::from_secs(1)),
            },
            // A valid suffix without a numeric prefix is invalid
            ParseTimeTestData {
                value: "s",
                result: Err(anyhow!(ERR_CANNOT_PARSE_DIGIT)),
            },
            ParseTimeTestData {
                value: "ms",
                result: Err(anyhow!(ERR_CANNOT_PARSE_DIGIT)),
            },
            // Floating point not allowed
            ParseTimeTestData {
                value: "3.7",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            ParseTimeTestData {
                value: "-1",
                result: Ok(Duration::new(u64::MAX, DURATION_MAX)),
            },
            ParseTimeTestData {
                value: "34d",
                result: Ok(Duration::from_secs(34 * SECONDS_IN_DAY)),
            },
            ParseTimeTestData {
                value: "999h",
                result: Ok(Duration::from_secs(999 * SECONDS_IN_HOUR)),
            },
            ParseTimeTestData {
                value: "785m",
                result: Ok(Duration::from_secs(785 * SECONDS_IN_MINUTE)),
            },
            ParseTimeTestData {
                value: "12345s",
                result: Ok(Duration::from_secs(12345)),
            },
            ParseTimeTestData {
                value: "109cs",
                result: Ok(Duration::from_millis(109 * CS_IN_MILLI_SECOND)),
            },
            ParseTimeTestData {
                value: "8761ds",
                result: Ok(Duration::from_millis(8761 * DS_IN_MILLI_SECOND)),
            },
            ParseTimeTestData {
                value: "999ms",
                result: Ok(Duration::from_millis(999)),
            },
            ParseTimeTestData {
                value: "999999us",
                result: Ok(Duration::from_micros(999_999)),
            },
            ParseTimeTestData {
                value: "999999999ns",
                result: Ok(Duration::from_nanos(999_999_999)),
            },
        ];
    }

    //type DurationFp = fn(value: &str) -> Result<Command>;

    // Note: These error messages comes from standard str parse(),
    // so they may need updating one day if the standard changes!
    const ERR_CANNOT_PARSE_DIGIT: &str = "cannot parse integer from empty string";
    const ERR_INVALID_DIGIT: &str = "invalid digit found in string";

    #[test]
    fn test_handle_cmd_exit() {
        #[derive(Debug)]
        struct TestData<'a> {
            value: &'a str,
            result: Result<Command>,
        }

        let tests = &[
            TestData {
                value: "",
                result: Err(anyhow!(ERR_CANNOT_PARSE_DIGIT)),
            },
            TestData {
                value: "foo",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                value: "1 foo",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                value: "foo 1",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                value: "foo bar",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                value: "foo 1 bar",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                value: "0",
                result: Ok(Command::Exit(0)),
            },
            TestData {
                value: "-127",
                result: Ok(Command::Exit(129)),
            },
            TestData {
                value: "-128",
                result: Ok(Command::Exit(128)),
            },
            TestData {
                value: "-2",
                result: Ok(Command::Exit(254)),
            },
            TestData {
                value: "-1",
                result: Ok(Command::Exit(255)),
            },
            TestData {
                value: "1",
                result: Ok(Command::Exit(1)),
            },
            TestData {
                value: "3",
                result: Ok(Command::Exit(3)),
            },
            TestData {
                value: "254",
                result: Ok(Command::Exit(254)),
            },
            TestData {
                value: "255",
                result: Ok(Command::Exit(255)),
            },
            TestData {
                value: "256",
                result: Ok(Command::Exit(0)),
            },
            TestData {
                value: "257",
                result: Ok(Command::Exit(1)),
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let result = handle_cmd_exit(d.value);

            let msg = format!("{}, result: {:?}", msg, result);

            if d.result.is_err() {
                assert!(result.is_err(), "{}", msg);

                let expected_err = format!("{:?}", d.result.as_ref().err());
                let actual_err = format!("{:?}", result.as_ref().err());

                assert_eq!(actual_err, expected_err, "{}", msg);

                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            assert_eq!(
                result.as_ref().unwrap(),
                d.result.as_ref().unwrap(),
                "{}",
                msg
            );
        }
    }

    #[test]
    fn test_handle_cmd_repeat() {
        #[derive(Debug)]
        struct TestData<'a> {
            value: &'a str,
            result: Result<Command>,
        }

        let tests = &[
            TestData {
                value: "",
                result: Err(anyhow!(ERR_CANNOT_PARSE_DIGIT)),
            },
            TestData {
                value: "foo",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                value: "1 foo",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                value: "foo 1",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                value: "foo bar",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                value: "foo 1 bar",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                value: "0",
                result: Ok(Command::Repeat(0)),
            },
            TestData {
                value: "1",
                result: Ok(Command::Repeat(1)),
            },
            TestData {
                value: "-1",
                result: Ok(Command::Repeat(REPEAT_FOREVER)),
            },
            TestData {
                value: "-2",
                result: Ok(Command::Repeat(REPEAT_FOREVER)),
            },
            TestData {
                value: "-9999",
                result: Ok(Command::Repeat(REPEAT_FOREVER)),
            },
            TestData {
                value: "9999",
                result: Ok(Command::Repeat(9999)),
            },
            TestData {
                value: "9223372036854775807",
                result: Ok(Command::Repeat(isize::MAX)),
            },
            TestData {
                // aka isize::MIN
                value: "-9223372036854775808",
                result: Ok(Command::Repeat(-1)),
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let result = handle_cmd_repeat(d.value);

            let msg = format!("{}, result: {:?}", msg, result);

            if d.result.is_err() {
                assert!(result.is_err(), "{}", msg);

                let expected_err = format!("{:?}", d.result.as_ref().err());
                let actual_err = format!("{:?}", result.as_ref().err());

                assert_eq!(actual_err, expected_err, "{}", msg);

                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            assert_eq!(
                result.as_ref().unwrap(),
                d.result.as_ref().unwrap(),
                "{}",
                msg
            );
        }
    }

    #[test]
    fn test_handle_cmd_fd() {
        #[derive(Debug)]
        struct TestData<'a> {
            value: &'a str,
            result: Result<Command>,
        }

        let tests = &[
            TestData {
                value: "",
                result: Err(anyhow!(ERR_CANNOT_PARSE_DIGIT)),
            },
            TestData {
                value: "foo",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                // File descriptors must be positive
                value: "-1",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                // File descriptors must be integers
                value: "9.8",
                result: Err(anyhow!(ERR_INVALID_DIGIT)),
            },
            TestData {
                value: "0",
                result: Ok(Command::Output(Output::FileDescriptor(0))),
            },
            TestData {
                value: "4294967295",
                result: Ok(Command::Output(Output::FileDescriptor(u32::MAX))),
            },
            TestData {
                value: "4294967296",
                result: Err(anyhow!("number too large to fit in target type")),
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let result = handle_cmd_fd(d.value);

            let msg = format!("{}, result: {:?}", msg, result);

            if d.result.is_err() {
                assert!(result.is_err(), "{}", msg);

                let expected_err = format!("{:?}", d.result.as_ref().err());
                let actual_err = format!("{:?}", result.as_ref().err());

                assert_eq!(actual_err, expected_err, "{}", msg);

                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            assert_eq!(
                result.as_ref().unwrap(),
                d.result.as_ref().unwrap(),
                "{}",
                msg
            );
        }
    }

    #[test]
    fn test_handle_cmd_intra_char() {
        #[derive(Debug)]
        struct TestData<'a> {
            value: &'a str,
            result: Result<Command>,
        }

        let tests = &[
            TestData {
                value: "",
                result: Ok(Command::IntraChar('\0')),
            },
            TestData {
                value: "ab",
                result: Err(anyhow!(ERR_INTRA_CHAR_LEN)),
            },
            TestData {
                value: "a",
                result: Ok(Command::IntraChar('a')),
            },
            TestData {
                value: "Z",
                result: Ok(Command::IntraChar('Z')),
            },
            TestData {
                value: "~",
                result: Ok(Command::IntraChar('~')),
            },
            // FIXME: Ideally, we'd allow an escape to be
            // a "single character".
            TestData {
                value: r#"\a"#,
                result: Err(anyhow!(ERR_INTRA_CHAR_LEN)),
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let result = handle_cmd_intra_char(d.value);

            let msg = format!("{}, result: {:?}", msg, result);

            if d.result.is_err() {
                assert!(result.is_err(), "{}", msg);

                let expected_err = format!("{:?}", d.result.as_ref().err());
                let actual_err = format!("{:?}", result.as_ref().err());

                assert_eq!(actual_err, expected_err, "{}", msg);

                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            assert_eq!(
                result.as_ref().unwrap(),
                d.result.as_ref().unwrap(),
                "{}",
                msg
            );
        }
    }

    #[test]
    fn test_parse_time() {
        let tests = &PARSE_TIME_TEST_DATA;

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let result = parse_time(d.value);

            let msg = format!("{}, result: {:?}", msg, result);

            if d.result.is_err() {
                assert!(result.is_err(), "{}", msg);

                let expected_err = format!("{:?}", d.result.as_ref().err());
                let actual_err = format!("{:?}", result.as_ref().err());

                assert_eq!(actual_err, expected_err, "{}", msg);

                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            assert_eq!(
                result.as_ref().unwrap(),
                d.result.as_ref().unwrap(),
                "{}",
                msg
            );
        }
    }

    #[test]
    fn test_handle_cmd_sleep() {
        let tests = &PARSE_TIME_TEST_DATA;

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let result = handle_cmd_sleep(d.value);

            let msg = format!("{}, result: {:?}", msg, result);

            if d.result.is_err() {
                assert!(result.is_err(), "{}", msg);

                let expected_err = format!("{:?}", d.result.as_ref().err());
                let actual_err = format!("{:?}", result.as_ref().err());

                assert_eq!(actual_err, expected_err, "{}", msg);

                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            let actual_cmd = result.as_ref().unwrap();

            assert!(matches!(actual_cmd, Command::Sleep(_)), "{}", msg);

            let expected_duration = d.result.as_ref().unwrap();

            match actual_cmd {
                Command::Sleep(actual_duration) => {
                    assert_eq!(actual_duration, expected_duration, "{}", msg)
                }
                _ => panic!("{:?}: invalid command", msg),
            };
        }
    }

    #[test]
    fn test_handle_cmd_intra_pause() {
        let tests = &PARSE_TIME_TEST_DATA;

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let result = handle_cmd_intra_pause(d.value);

            let msg = format!("{}, result: {:?}", msg, result);

            if d.result.is_err() {
                assert!(result.is_err(), "{}", msg);

                let expected_err = format!("{:?}", d.result.as_ref().err());
                let actual_err = format!("{:?}", result.as_ref().err());

                assert_eq!(actual_err, expected_err, "{}", msg);

                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            let actual_cmd = result.as_ref().unwrap();

            assert!(matches!(actual_cmd, Command::IntraPause(_)), "{}", msg);

            let expected_duration = d.result.as_ref().unwrap();

            match actual_cmd {
                Command::IntraPause(actual_duration) => {
                    assert_eq!(actual_duration, expected_duration, "{}", msg)
                }
                _ => panic!("{:?}: invalid command", msg),
            };
        }
    }

    #[test]
    fn test_arghandler_handle_flag() {
        #[derive(Debug)]
        struct TestData {
            flag: char,
            // None means an error!
            cmd: Option<Command>,
        }

        let tests = &[
            TestData {
                flag: 'a',
                cmd: None,
            },
            TestData {
                flag: 'e',
                cmd: Some(Command::Output(Output::Stderr)),
            },
            TestData {
                flag: 'o',
                cmd: Some(Command::Output(Output::Stdout)),
            },
            TestData {
                flag: 't',
                cmd: Some(Command::Output(Output::Terminal)),
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let mut handler = ArgHandler::default();
            let arg = Arg::new(d.flag);
            let result = handler.handle_flag(arg);

            let msg = format!("{}, result: {:?}", msg, result);

            if d.cmd.is_none() {
                assert!(result.is_err(), "{}", msg);
                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            if let Some(cmd) = d.cmd.clone() {
                if let Command::Output(output) = cmd {
                    assert_eq!(handler.cmds.get_output(), output, "{}", msg)
                }
            };
        }
    }

    #[test]
    fn test_arghandler_handle_option() {
        struct TestData<'a> {
            flag: char,
            value: &'a str,
            result: Result<()>,
            predicate: Option<&'a dyn Fn(Commands) -> bool>,
        }

        // Note we cannot test 'x' (Command::Exit)
        let tests = &[
            TestData {
                flag: 'a',
                value: "xx",
                result: Err(anyhow!(ERR_INTRA_CHAR_LEN)),
                predicate: None,
            },
            TestData {
                flag: 'a',
                value: "x",
                result: Ok(()),
                predicate: Some(&|c: Commands| c.get_intra_char() == Some('x')),
            },
            TestData {
                flag: 'b',
                value: "foo",
                result: Err(anyhow!(ERR_CANNOT_PARSE_DIGIT)),
                predicate: None,
            },
            TestData {
                flag: 'b',
                value: "1s",
                result: Ok(()),
                predicate: Some(&|c: Commands| c.get_intra_pause() == Some(Duration::from_secs(1))),
            },
            TestData {
                flag: 'r',
                value: "1",
                result: Ok(()),
                predicate: None,
            },
            TestData {
                flag: 's',
                value: "1",
                result: Ok(()),
                predicate: None,
            },
            TestData {
                flag: 'u',
                value: "1",
                result: Ok(()),
                predicate: None,
            },
            TestData {
                flag: 'x',
                value: "255",
                result: Err(anyhow!("Error to test exiting with value 255")),
                predicate: None,
            },
        ];

        let mut handler = ArgHandler::default();

        //--------------------

        let arg = Arg::new('a');
        let result = handler.handle_option(arg);
        assert!(result.is_err());

        let err_msg = format!("{:?}", result.as_ref().err().unwrap());
        assert_eq!(err_msg, ERR_MISSING_OPT_VALUE);

        //--------------------

        let mut arg = Arg::new('z');
        arg.value = Some("x".into());
        let result = handler.handle_option(arg);
        assert!(result.is_err());

        let err_msg = format!("{:?}", result.as_ref().err().unwrap());
        assert!(err_msg.starts_with("invalid option"));

        //--------------------

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]", i);

            let mut handler = ArgHandler::default();
            let mut arg = Arg::new(d.flag);
            arg.value = Some(d.value.into());
            let result = handler.handle_option(arg);

            let msg = format!("{}, result: {:?}", msg, result);

            if d.result.is_err() {
                let expected_err = format!("{:?}", d.result.as_ref().err());
                let actual_err = format!("{:?}", result.as_ref().err());

                assert_eq!(actual_err, expected_err, "{}", msg);

                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            if let Some(f) = d.predicate {
                let cmds = handler.cmds;
                assert!(f(cmds), "{}", msg);
            }
        }
    }

    #[test]
    fn test_arghandler_handle_positional() {
        #[derive(Debug)]
        struct TestData<'a> {
            value: &'a str,
            intra_char: Option<char>,
            result: Result<()>,
            output: &'a str,
        }

        let tests = &[
            TestData {
                value: "",
                intra_char: None,
                result: Ok(()),
                output: "",
            },
            TestData {
                value: "x",
                intra_char: None,
                result: Ok(()),
                output: "x",
            },
            TestData {
                value: "xy",
                intra_char: None,
                result: Ok(()),
                output: "xy",
            },
            TestData {
                value: "",
                intra_char: Some('z'),
                result: Ok(()),
                // No output, so no intra char
                output: "",
            },
            TestData {
                value: "x",
                intra_char: Some('z'),
                result: Ok(()),
                output: "xz",
            },
            TestData {
                value: "xy",
                intra_char: Some('z'),
                result: Ok(()),
                output: "xzyz",
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let (rfd, wfd) = pipe2(OFlag::O_CLOEXEC).expect("failed to create pipe");

            let mut handler = ArgHandler::default();

            handler
                .cmds
                .switch_output(Output::FileDescriptor(wfd as u32))
                .expect("switch output");

            if let Some(ch) = d.intra_char {
                handler.cmds.set_intra_char(ch);
            }

            let mut arg = Arg::new(POSITIONAL_HANDLER_OPT);
            arg.value = Some(d.value.into());

            let result = handler.handle_positional(arg);

            let msg = format!("{}, result: {:?}", msg, result);

            if d.result.is_err() {
                assert!(result.is_err());
                continue;
            }

            let mut reader = unsafe { File::from_raw_fd(rfd) };

            // Allow the reader to be read to completion
            drop(handler);
            let _ = close(wfd);

            let mut buffer = String::new();
            reader.read_to_string(&mut buffer).expect("failed to read");

            let msg = format!("{}, buffer: {:?}", msg, buffer);

            assert!(result.is_ok(), "{}", msg);
            assert_eq!(buffer, d.output, "{}", msg);
        }
    }
}
