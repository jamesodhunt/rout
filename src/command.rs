// Copyright (c) 2021 James O. D. Hunt.
//
// SPDX-License-Identifier: Apache-2.0
//

use anyhow::{anyhow, Result};
use nix::unistd::{close, dup};
use rand;
use std::convert::TryInto;
use std::fs::OpenOptions;
use std::io::Write;
use std::os::unix::io::{AsRawFd, RawFd};
use std::thread::sleep;
use std::time::Duration;

const DEV_NULL: &str = "/dev/null";
const DEV_TTY: &str = "/dev/tty";

// Number of attempts to generate a printable random character.
// Arbitrary, but hopefully sufficient to avoid an infinite loop.
const RANDOM_GENERATE_ATTEMPTS: u16 = 1024;

const ERR_INVALID_RANGE: &str = "invalid range";

/// A range is a tuple which represents a "from" and
/// a "to" value for generating ranges of characters.
/// The range is inclusive:
///
///   [from, to]
///
/// The type is char which is 4 bytes wide and able to handle
/// any UTF-8 value (UTF8_MIN_VALUE - UTF8_MAX_VALUE).
///
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
pub struct Range(pub char, pub char);

/// Where to send output
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
pub enum Output {
    /// aka "/dev/null"
    Discard,
    FileDescriptor(u32),
    Stderr,
    Stdout,
    Terminal,
}

impl Default for Output {
    fn default() -> Self {
        Output::Stdout
    }
}

/// All values are represented as commands.
///
/// > **Note:** `Escaped` is technically the same as a `LiteralChar`
/// > (since the escaped character has already been expanded). It is retained
/// as a separate value to allow the caller to detect that the value was
/// originally escaped.
#[derive(Debug, PartialEq, PartialOrd, Eq, Ord, Clone)]
pub enum Command {
    Escaped(char),
    Exit(i32),
    IntraChar(char),
    IntraPause(Duration),
    /// Single character
    LiteralChar(char),
    /// Contiguous run of unescaped characters
    LiteralString(String),
    Output(Output),
    Random,
    Range(Range),
    Repeat(isize),
    Sleep(Duration),
}

pub type CommandList = Vec<Command>;

impl Command {
    /// Evaluate the command.
    ///
    /// # Arguments:
    ///
    /// `Commands` - Reference to the `Commands` object this `Command` is
    /// contained within.
    pub fn run(self, cmds: &mut Commands) -> Result<()> {
        // Note that the intra commands have already been handled
        // (by `Commands::set_intra_*()`).
        match self {
            Self::Escaped(ch) => self.handle_escaped(cmds, ch),
            Self::Exit(value) => self.handle_exit(cmds, value),
            Self::IntraChar(_) => Ok(()),
            Self::IntraPause(_) => Ok(()),
            Self::LiteralChar(ch) => self.handle_literal_char(cmds, ch),
            Self::LiteralString(ref s) => self.handle_literal_string(cmds, s.to_string()),
            Self::Output(output) => self.handle_output(cmds, output),
            Self::Random => self.handle_random(cmds),
            Self::Range(range) => self.handle_range(cmds, range),
            Self::Repeat(count) => self.handle_repeat(cmds, count),
            Self::Sleep(duration) => self.handle_sleep(duration),
        }
    }

    fn handle_escaped(&self, cmds: &Commands, ch: char) -> Result<()> {
        cmds.write_char(ch)
    }

    #[cfg(not(test))]
    fn handle_exit(&self, cmds: &Commands, value: i32) -> ! {
        let _ = cmds.flush_output();

        std::process::exit(value);
    }

    #[cfg(test)]
    fn handle_exit(&self, cmds: &Commands, value: i32) -> Result<()> {
        cmds.flush_output()?;

        Err(anyhow!("Error to test exiting with value {}", value))
    }

    fn handle_literal_char(&self, cmds: &Commands, ch: char) -> Result<()> {
        cmds.write_char(ch)
    }

    fn handle_literal_string(&self, cmds: &Commands, s: String) -> Result<()> {
        cmds.write_string(s)
    }

    fn handle_output(&self, cmds: &mut Commands, output: Output) -> Result<()> {
        cmds.switch_output(output)
    }

    fn handle_random(&self, cmds: &Commands) -> Result<()> {
        let mut random_char: char;

        for _ in 0..RANDOM_GENERATE_ATTEMPTS {
            random_char = rand::random::<char>();

            if !random_char.is_control() {
                return cmds.write_char(random_char);
            }
        }

        Err(anyhow!(
            "failed to generate printable random character after {} attempts",
            RANDOM_GENERATE_ATTEMPTS
        ))
    }

    fn handle_range(&self, cmds: &mut Commands, range: Range) -> Result<()> {
        let first = range.0;
        let second = range.1;

        if first == second {
            return Err(anyhow!(ERR_INVALID_RANGE));
        } else if first < second {
            for ch in first..=second {
                cmds.write_char(ch)?;

                cmds.handle_intras()?;
            }
        } else {
            for ch in (second..=first).rev() {
                cmds.write_char(ch)?;

                cmds.handle_intras()?;
            }
        }

        Ok(())
    }

    fn handle_repeat(&self, cmds: &mut Commands, count: isize) -> Result<()> {
        if count == 0 {
            return Ok(());
        }

        if let Some(cmdlist) = cmds.prev_cmdlist.clone() {
            if count < 0 {
                // Infinite repeat
                loop {
                    let cmdlist = cmdlist.clone();

                    for cmd in cmdlist {
                        let cmd_copy = cmd.clone();

                        cmd.run(cmds)?;

                        match cmd_copy {
                            Command::LiteralString(_) => (),
                            _ => cmds.handle_intras()?,
                        };
                    }
                }
            } else {
                for _ in 0..count {
                    let cmdlist = cmdlist.clone();

                    for cmd in cmdlist {
                        let cmd_copy = cmd.clone();

                        cmd.run(cmds)?;

                        match cmd_copy {
                            Command::LiteralString(_) => (),
                            _ => cmds.handle_intras()?,
                        };
                    }
                }
            }
        }

        Ok(())
    }

    fn handle_sleep(&self, duration: Duration) -> Result<()> {
        sleep(duration);

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Commands {
    // Last set of cmds that was accessed
    // (used for Command::Repeat)
    prev_cmdlist: Option<CommandList>,

    // Where to send output
    output: Output,

    //// Output file descriptor
    fd: RawFd,

    // Character to display between each character to be output.
    intra_char: Option<char>,

    // Pause between each character output.
    intra_pause: Option<Duration>,

    tty_fd: RawFd,
    discard_fd: RawFd,
}

// XXX: We can't derive default due to needing to ensure
// XXX: 'fd' is not zero (aka stdin!) and output is not 0
// XXX: (Output::Discard!)
impl Default for Commands {
    fn default() -> Self {
        Commands {
            prev_cmdlist: None,
            output: Output::default(),
            fd: std::io::stdout().as_raw_fd(),
            intra_char: None,
            intra_pause: None,
            tty_fd: -1,
            discard_fd: -1,
        }
    }
}

impl Commands {
    pub fn set_prev_cmdlist(&mut self, cmds: CommandList) {
        self.prev_cmdlist = Some(cmds);
    }

    #[cfg(test)]
    pub fn set_intra_char(&mut self, ch: char) {
        self.intra_char = Some(ch);
    }

    #[cfg(test)]
    pub fn get_output(&self) -> Output {
        self.output
    }

    #[cfg(test)]
    pub fn get_intra_char(&self) -> Option<char> {
        self.intra_char
    }

    #[cfg(test)]
    pub fn get_intra_pause(&self) -> Option<Duration> {
        self.intra_pause
    }

    pub fn flush_output(&self) -> Result<()> {
        match self.output {
            Output::Discard => (),
            Output::FileDescriptor(_) => (),
            Output::Stderr => std::io::stderr().flush()?,
            Output::Stdout => std::io::stdout().flush()?,
            Output::Terminal => (),
        }

        Ok(())
    }

    // Flushes existing output and changes to the new specified output.
    pub fn switch_output(&mut self, output: Output) -> Result<()> {
        if output == self.output {
            // No change
            return Ok(());
        }

        self.flush_output()?;

        // Close existing fd (if not a standard stream or the terminal).
        match self.output {
            Output::FileDescriptor(_) => close(self.fd),
            _ => Ok(()),
        }?;

        // Open new fd
        let fd: RawFd = match output {
            Output::Discard => {
                if self.discard_fd < 0 {
                    let f = OpenOptions::new().write(true).open(DEV_NULL)?;

                    let new_fd = f.as_raw_fd();

                    self.discard_fd = dup(new_fd)?;
                }

                self.discard_fd
            }
            Output::FileDescriptor(fd) => fd.try_into()?,
            Output::Stderr => std::io::stderr().as_raw_fd(),
            Output::Stdout => std::io::stdout().as_raw_fd(),

            Output::Terminal => {
                if self.tty_fd < 0 {
                    let f = OpenOptions::new().write(true).open(DEV_TTY)?;

                    let new_fd = f.as_raw_fd();

                    self.tty_fd = dup(new_fd)?;
                }

                self.tty_fd
            }
        };

        self.output = output;
        self.fd = fd;

        Ok(())
    }

    pub fn handle_intras(&self) -> Result<()> {
        if let Some(intra_char) = self.intra_char {
            self.write_char(intra_char)?;
        }

        if let Some(duration) = self.intra_pause {
            sleep(duration);
        }

        Ok(())
    }

    // Write the (potentially multi-byte) character value to
    // the output file descriptor.
    pub fn write_char(&self, ch: char) -> Result<()> {
        // Need up to 4 bytes to encode a 32-bit unicode character.
        let mut buf = [0; 4];

        let result = ch.encode_utf8(&mut buf);

        let _ = nix::unistd::write(self.fd, &result.as_bytes())?;

        Ok(())
    }

    pub fn write_string(&self, s: String) -> Result<()> {
        if let Some(intra_char) = self.intra_char {
            for ch in s.chars() {
                // Write requested character in string
                self.write_char(ch as char)?;

                // followed by the intra character
                self.write_char(intra_char)?;

                if let Some(duration) = self.intra_pause {
                    sleep(duration);
                }
            }
        } else if let Some(duration) = self.intra_pause {
            for ch in s.chars() {
                self.write_char(ch as char)?;
                sleep(duration);
            }
        } else {
            let _ = nix::unistd::write(self.fd, s.as_bytes())?;
        }

        Ok(())
    }

    // A null byte means "unset". Any other value sets.
    pub fn handle_intra_char(&mut self, ch: char) -> Result<()> {
        match ch {
            '\0' => self.intra_char = None,
            _ => self.intra_char = Some(ch),
        };

        Ok(())
    }

    pub fn set_intra_pause(&mut self, duration: Duration) -> Result<()> {
        self.intra_pause = Some(duration);

        Ok(())
    }
}

impl Into<CommandList> for Command {
    fn into(self) -> CommandList {
        vec![self]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::values::*;
    use nix::fcntl::OFlag;
    use nix::unistd::{close, pipe2};
    use std::collections::HashMap;
    use std::fs::File;
    use std::io::Read;
    use std::os::unix::io::FromRawFd;

    // "cargo test" runs tests in parallel using threads. Normally, this is
    // fine, but it isn't fine when we use pipe()/pipe2() since each thread
    // gets copies of the file descriptors so the tests using pipes fail with
    // random EPIPE's or in other weirder ways.
    use serial_test::serial;

    fn check_run_command(cmd: Command, output: Option<&str>) -> Result<()> {
        let mut cmds = Commands::default();

        if let Some(output) = output {
            let (rfd, wfd) = pipe2(OFlag::O_CLOEXEC)?;

            cmds.switch_output(Output::FileDescriptor(wfd as u32))?;

            cmd.run(&mut cmds)?;

            let mut reader = unsafe { File::from_raw_fd(rfd) };

            // Allow the reader to be read to completion
            drop(cmds);
            let _ = close(wfd);

            let mut buffer = String::new();
            reader.read_to_string(&mut buffer)?;

            if buffer.as_str() != output {
                return Err(anyhow!("expected output {:?}, got {:?}", output, buffer));
            }
        } else {
            cmd.run(&mut cmds)?;
        }

        Ok(())
    }

    #[test]
    fn test_commands_default() {
        let cmds = Commands::default();

        let expected_cmds = Commands {
            prev_cmdlist: None,
            output: Output::default(),
            fd: std::io::stdout().as_raw_fd(),
            intra_char: None,
            intra_pause: None,
            tty_fd: -1,
            discard_fd: -1,
        };

        assert_eq!(cmds, expected_cmds);
    }

    #[test]
    fn test_output() {
        let output = Output::default();

        assert_eq!(output, Output::Stdout);
    }

    #[test]
    fn test_commands_set_prev_cmdlist() {
        let mut cmds = Commands::default();

        assert_eq!(cmds.prev_cmdlist, None);

        let cmdlist = vec![Command::LiteralString("foo".into()), Command::Exit(7)];
        cmds.set_prev_cmdlist(cmdlist.clone());

        assert_eq!(cmds.prev_cmdlist, Some(cmdlist));
    }

    #[test]
    fn test_commands_handle_intra_char() {
        let mut cmds = Commands::default();

        // Check initial value
        assert_eq!(cmds.intra_char, None);

        let ch_non_null = '~';
        let ch_null = '\0';

        // Check set to null value
        cmds.handle_intra_char(ch_null).unwrap();
        assert_eq!(cmds.intra_char, None);

        // Check set to non-null value
        cmds.handle_intra_char(ch_non_null).unwrap();
        assert_eq!(cmds.intra_char, Some(ch_non_null));

        // Check reset to null value
        cmds.handle_intra_char(ch_null).unwrap();
        assert_eq!(cmds.intra_char, None);
    }

    #[test]
    #[serial]
    fn test_commands_write_char() {
        // Test a few characters.
        let test_chars = ['\0', 'a', '~', std::char::MAX];

        for (i, ch) in test_chars.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, ch);

            let (rfd, wfd) = pipe2(OFlag::O_CLOEXEC).expect("failed to create pipe");

            let mut cmds = Commands::default();
            cmds.switch_output(Output::FileDescriptor(wfd as u32))
                .expect("switch output");

            let result = cmds.write_char(*ch);

            assert!(result.is_ok(), "{}", msg);

            let mut reader = unsafe { File::from_raw_fd(rfd) };

            // Allow the reader to be read to completion
            drop(cmds);
            let _ = close(wfd);

            let mut buffer = String::new();
            reader.read_to_string(&mut buffer).expect("failed to read");

            let mut chars = buffer.chars();
            let len = chars.clone().count();

            assert_eq!(len, 1, "{}", msg);

            let first = chars.next().unwrap();
            assert_eq!(first, *ch, "{}", msg);
        }
    }

    #[test]
    #[serial]
    fn test_commands_write_string() {
        #[derive(Debug)]
        struct TestData<'a> {
            value: &'a str,
            intra_char: Option<char>,
            result: &'a str,
        }

        let tests = &[
            TestData {
                value: "",
                intra_char: None,
                result: "",
            },
            TestData {
                value: "",
                intra_char: Some('a'),
                result: "",
            },
            TestData {
                value: "a",
                intra_char: None,
                result: "a",
            },
            TestData {
                value: "a",
                intra_char: Some('_'),
                result: "a_",
            },
            TestData {
                value: "foo",
                intra_char: None,
                result: "foo",
            },
            TestData {
                value: "foo",
                intra_char: Some('.'),
                result: "f.o.o.",
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let (rfd, wfd) = pipe2(OFlag::O_CLOEXEC).expect("failed to create pipe");

            let mut cmds = Commands::default();
            cmds.switch_output(Output::FileDescriptor(wfd as u32))
                .expect("switch output");

            if let Some(ch) = d.intra_char {
                let _ = cmds.handle_intra_char(ch);
            }

            let s = d.value.to_string();

            let result = cmds.write_string(s.clone());
            assert!(result.is_ok(), "{}", msg);

            let mut reader = unsafe { File::from_raw_fd(rfd) };

            // Allow the reader to be read to completion
            drop(cmds);
            let _ = close(wfd);

            let mut buffer = String::new();
            reader.read_to_string(&mut buffer).expect("failed to read");

            let _ = close(rfd);

            let expected = d.result.to_string();
            assert_eq!(buffer, expected, "{}", msg);
        }
    }

    #[test]
    fn test_command_handle_exit() {
        let value = 255;
        let cmd = Command::Exit(value);
        let cmds = Commands::default();

        let result = cmd.handle_exit(&cmds, value);

        let expected_err = "Error to test exiting with value 255";

        let actual_err = format!("{:?}", result.err().unwrap());

        assert_eq!(actual_err, expected_err);
    }

    #[test]
    fn test_command_run() {
        #[derive(Debug)]
        struct TestData<'a> {
            cmd: Command,
            result: Result<()>,
            output: Option<&'a str>,
        }

        let tests = &[
            TestData {
                cmd: Command::Escaped(ESCAPE_A),
                result: Ok(()),
                output: None,
            },
            TestData {
                cmd: Command::Exit(255),
                result: Err(anyhow!("Error to test exiting with value 255")),
                output: None,
            },
            TestData {
                cmd: Command::IntraChar('x'),
                result: Ok(()),
                output: None,
            },
            TestData {
                cmd: Command::IntraPause(Duration::from_secs(0)),
                result: Ok(()),
                output: None,
            },
            TestData {
                cmd: Command::LiteralChar('x'),
                result: Ok(()),
                output: Some("x"),
            },
            TestData {
                cmd: Command::LiteralString("hello world\n".into()),
                result: Ok(()),
                output: Some("hello world\n"),
            },
            TestData {
                cmd: Command::Sleep(Duration::from_secs(0)),
                result: Ok(()),
                output: None,
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let result = check_run_command(d.cmd.clone(), d.output);

            if d.result.is_err() {
                assert!(result.is_err(), "{}", msg);

                let expected_err = format!("{:?}", d.result.as_ref().err().unwrap());
                let actual_err = format!("{:?}", result.err().unwrap());

                assert_eq!(actual_err, expected_err, "{}", msg);

                continue;
            }

            assert!(result.is_ok(), "{}", msg);
        }
    }

    #[test]
    fn test_commands_set_intra_pause() {
        let mut cmds = Commands::default();

        assert_eq!(cmds.intra_pause, None);

        let duration = Duration::from_secs(1234567);

        cmds.set_intra_pause(duration).unwrap();

        assert_eq!(cmds.intra_pause, Some(duration));
    }

    #[test]
    #[serial]
    fn test_command_handle_escaped() {
        #[derive(Debug)]
        struct TestData {
            value: char,
        }

        let tests = &[
            TestData { value: '\0' },
            TestData { value: '\\' },
            TestData { value: '\n' },
            TestData { value: '\r' },
            TestData { value: '\t' },
            TestData { value: ESCAPE_A },
            TestData { value: ESCAPE_B },
            TestData { value: ESCAPE_E },
            TestData { value: ESCAPE_F },
            TestData { value: ESCAPE_V },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let mut cmds = Commands::default();
            let cmd = Command::Escaped(d.value);

            let (rfd, wfd) = pipe2(OFlag::O_CLOEXEC).unwrap();

            cmds.switch_output(Output::FileDescriptor(wfd as u32))
                .expect(&msg);

            let mut reader = unsafe { File::from_raw_fd(rfd) };

            cmd.handle_escaped(&mut cmds, d.value).expect(&msg);

            // Allow the reader to be read to completion
            drop(cmds);
            let _ = close(wfd);

            let mut buffer = String::new();
            reader.read_to_string(&mut buffer).expect(&msg);
            assert_eq!(buffer.chars().next().unwrap(), d.value, "{}", msg);
        }
    }

    #[test]
    #[serial]
    fn test_command_handle_literal_char() {
        #[derive(Debug)]
        struct TestData {
            value: char,
        }

        let tests = &[
            TestData { value: ' ' },
            TestData { value: '!' },
            TestData { value: 'a' },
            TestData { value: '~' },
            TestData {
                value: std::char::MAX,
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let mut cmds = Commands::default();
            let cmd = Command::LiteralChar(d.value);

            let (rfd, wfd) = pipe2(OFlag::O_CLOEXEC).unwrap();

            cmds.switch_output(Output::FileDescriptor(wfd as u32))
                .expect(&msg);

            let mut reader = unsafe { File::from_raw_fd(rfd) };

            cmd.handle_escaped(&mut cmds, d.value).expect(&msg);

            // Allow the reader to be read to completion
            drop(cmds);
            let _ = close(wfd);

            let mut buffer = String::new();
            reader.read_to_string(&mut buffer).expect(&msg);
            assert_eq!(buffer.chars().next().unwrap(), d.value, "{}", msg);
        }
    }

    #[test]
    #[serial]
    fn test_command_handle_random() {
        let mut random_chars = HashMap::new();

        let count = 1024;

        for i in 0..count {
            let msg = format!("test[{}]", i);

            let mut cmds = Commands::default();
            let cmd = Command::Random;

            let (rfd, wfd) = pipe2(OFlag::O_CLOEXEC).unwrap();

            cmds.switch_output(Output::FileDescriptor(wfd as u32))
                .expect(&msg);

            let mut reader = unsafe { File::from_raw_fd(rfd) };

            cmd.handle_random(&mut cmds).expect(&msg);

            // Allow the reader to be read to completion
            drop(cmds);
            let _ = close(wfd);

            let mut buffer = String::new();
            reader.read_to_string(&mut buffer).expect(&msg);

            let random_char = buffer.chars().next().unwrap();
            random_chars.insert(String::from(random_char), 1);
        }

        let len = random_chars.len();

        assert!(len > 0);
        assert!(len <= count);

        // Expect atleast 50% of the generated characters to be unique:
        // Considering the range of char, this seems a safe assertion!
        assert!(len >= (count / 2));
    }

    #[test]
    #[serial]
    fn test_command_handle_range() {
        #[derive(Debug)]
        struct TestData<'a> {
            range: Range,
            result: Result<&'a str>,
        }

        let tests = &[
            TestData {
                range: Range('\0', '\0'),
                result: Err(anyhow!(ERR_INVALID_RANGE)),
            },
            TestData {
                range: Range(std::char::MAX, std::char::MAX),
                result: Err(anyhow!(ERR_INVALID_RANGE)),
            },
            TestData {
                range: Range('a', 'a'),
                result: Err(anyhow!(ERR_INVALID_RANGE)),
            },
            TestData {
                range: Range('X', 'X'),
                result: Err(anyhow!(ERR_INVALID_RANGE)),
            },
            TestData {
                range: Range('a', 'f'),
                result: Ok("abcdef"),
            },
            TestData {
                range: Range('F', 'A'),
                result: Ok("FEDCBA"),
            },
            TestData {
                range: Range('0', '9'),
                result: Ok("0123456789"),
            },
            TestData {
                range: Range('9', '0'),
                result: Ok("9876543210"),
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let mut cmds = Commands::default();
            let cmd = Command::Range(d.range);

            let (rfd, wfd) = pipe2(OFlag::O_CLOEXEC).expect(&msg);

            cmds.switch_output(Output::FileDescriptor(wfd as u32))
                .expect(&msg);

            let mut reader = unsafe { File::from_raw_fd(rfd) };
            let result = cmd.handle_range(&mut cmds, d.range);

            if d.result.is_err() {
                assert!(result.is_err(), "{}", msg);

                let expected_err = format!("{:?}", d.result.as_ref().err().unwrap());
                let actual_err = format!("{:?}", result.err().unwrap());
                assert_eq!(actual_err, expected_err, "{}", msg);

                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            //let expected_output = d.result.as_ref().ok().unwrap();
            let expected_output = d.result.as_ref().ok().unwrap();

            // Allow the reader to be read to completion
            drop(cmds);
            let _ = close(wfd);

            let mut buffer = String::new();
            reader.read_to_string(&mut buffer).expect(&msg);

            assert!(result.is_ok(), "{}", msg);
            assert_eq!(buffer, **expected_output, "{}", msg);
        }
    }

    #[test]
    #[serial]
    fn test_command_handle_repeat() {
        #[derive(Debug)]
        struct TestData<'a> {
            prev_cmdlist: Option<CommandList>,
            intra_char: Option<char>,
            // Note: Cannot test infinite repeat
            count: isize,
            result: Result<&'a str>,
        }

        let tests = &[
            TestData {
                prev_cmdlist: None,
                intra_char: None,
                count: 0,
                result: Ok(""),
            },
            TestData {
                prev_cmdlist: None,
                intra_char: None,
                count: 3,
                result: Ok(""),
            },
            TestData {
                prev_cmdlist: Some(vec![Command::LiteralString("foo".into())]),
                intra_char: None,
                count: 0,
                result: Ok(""),
            },
            TestData {
                prev_cmdlist: Some(vec![Command::LiteralChar('a')]),
                intra_char: None,
                count: 1,
                result: Ok("a"),
            },
            TestData {
                prev_cmdlist: Some(vec![Command::LiteralChar('a')]),
                intra_char: None,
                count: 2,
                result: Ok("aa"),
            },
            TestData {
                prev_cmdlist: Some(vec![Command::LiteralString("foo".into())]),
                intra_char: None,
                count: 3,
                result: Ok("foofoofoo"),
            },
            TestData {
                prev_cmdlist: Some(vec![Command::LiteralChar('a')]),
                intra_char: Some('.'),
                count: 1,
                result: Ok("a."),
            },
            TestData {
                prev_cmdlist: Some(vec![Command::LiteralChar('a')]),
                intra_char: Some('.'),
                count: 2,
                result: Ok("a.a."),
            },
            TestData {
                prev_cmdlist: Some(vec![Command::LiteralString("foo".into())]),
                intra_char: Some('.'),
                count: 1,
                result: Ok("f.o.o."),
            },
            TestData {
                prev_cmdlist: Some(vec![Command::LiteralString("foo".into())]),
                intra_char: Some('.'),
                count: 2,
                result: Ok("f.o.o.f.o.o."),
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let mut cmds = Commands::default();

            if let Some(cmdlist) = &d.prev_cmdlist {
                cmds.set_prev_cmdlist(cmdlist.to_vec());
            }

            if let Some(ch) = &d.intra_char {
                cmds.set_intra_char(*ch);
            }

            let cmd = Command::Repeat(d.count);

            let (rfd, wfd) = pipe2(OFlag::O_CLOEXEC).expect(&msg);

            cmds.switch_output(Output::FileDescriptor(wfd as u32))
                .expect(&msg);

            let mut reader = unsafe { File::from_raw_fd(rfd) };
            let result = cmd.handle_repeat(&mut cmds, d.count);

            if d.result.is_err() {
                assert!(result.is_err(), "{}", msg);

                let expected_err = format!("{:?}", d.result.as_ref().err().unwrap());
                let actual_err = format!("{:?}", result.err().unwrap());

                assert_eq!(actual_err, expected_err, "{}", msg);

                continue;
            }

            assert!(result.is_ok(), "{}", msg);

            let expected_output = d.result.as_ref().ok().unwrap();

            // Ensure handle_repeat() didn't modify/remove the prev_cmdlist.
            assert_eq!(cmds.prev_cmdlist, d.prev_cmdlist, "{}", msg);

            // Allow the reader to be read to completion
            drop(cmds);
            let _ = close(wfd);

            let mut buffer = String::new();
            reader.read_to_string(&mut buffer).expect(&msg);

            assert!(result.is_ok(), "{}", msg);
            assert_eq!(buffer, **expected_output, "{}", msg);
        }
    }

    #[test]
    fn test_switch_output() {
        #[derive(Debug)]
        // a RawFd of -2 means "replace with a valid fd please" ;)
        struct TestData {
            initial: (Output, RawFd),
            new: (Output, RawFd),
        }

        let tests = &[
            TestData {
                initial: (Output::Stdout, std::io::stdout().as_raw_fd()),
                new: (Output::Stdout, std::io::stdout().as_raw_fd()),
            },
            TestData {
                initial: (Output::Stdout, std::io::stdout().as_raw_fd()),
                new: (Output::Stderr, std::io::stderr().as_raw_fd()),
            },
            TestData {
                initial: (Output::Stderr, std::io::stderr().as_raw_fd()),
                new: (Output::Stdout, std::io::stdout().as_raw_fd()),
            },
            TestData {
                initial: (Output::Discard, -2),
                new: (Output::Stdout, std::io::stdout().as_raw_fd()),
            },
            TestData {
                initial: (Output::Terminal, -2),
                new: (Output::Stderr, std::io::stderr().as_raw_fd()),
            },
        ];

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let (rfd, wfd) = pipe2(OFlag::O_CLOEXEC).expect(&msg);

            let mut cmds = Commands {
                output: d.initial.0,
                ..Default::default()
            };

            if d.initial.1 < -1 {
                cmds.fd = wfd;
            }

            cmds.switch_output(d.new.0).expect(&msg);

            assert_eq!(cmds.output, d.new.0, "{}", msg);
            assert_eq!(cmds.fd, d.new.1, "{}", msg);

            let _ = close(rfd);
            let _ = close(wfd);
        }

        let msg = "test Output::FileDescriptor";

        let mut cmds = Commands::default();

        let (_rfd, wfd) = pipe2(OFlag::O_CLOEXEC).expect(&msg);

        let output = Output::FileDescriptor(wfd as u32);

        cmds.switch_output(output).expect(&msg);

        assert_eq!(cmds.output, output, "{}", msg);
        assert_eq!(cmds.fd, wfd, "{}", msg);

        cmds.switch_output(Output::Stdout).expect(&msg);

        assert_eq!(cmds.output, Output::Stdout, "{}", msg);
        assert_eq!(cmds.fd, std::io::stdout().as_raw_fd(), "{}", msg);
    }
}
