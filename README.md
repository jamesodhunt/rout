# Rout

> Rout _v. i._ - To roar; to bellow.

## Overview

> _So what is it?_

`rout` is a simple command-line utility that produces output. As you might
guess from the name, it's written in rust.

> _So what is it?_

`rout` does everything that tools like `echo(1)` and `printf(1)` provide, but
`rout` also allows you to do interesting things such as:

- Redirect output without using the shell redirection operators (you can even
  output to arbitrary file descriptors or the terminal).
- Repeat ranges of commands.
- Pause for specific amounts of time.

> _So what is it?_

It's a tool that can be used to generate a stream of bytes.

> _So what is it?_

It's a thing that displays stuff!

> _Oh, well why didn't you say?!_

> Dialog very loosely based on and inspired by the trialogue initiated by
> "Cat" in the "Red Dwarf" TV series episode "Stasis Leak" (series/season 2,
> episode 4). If you've never seen this series, make it your life's mission to
> do so!

## Install

```bash
$ cargo install rout
```

## Examples

```bash
# Print "foofoofoo" to stdout, followed by "barbar" to stderr.
$ rout "foo" -r 2 -e "bar" -r 1

# Write 50 nul bytes direct to the terminal.
$ rout -t "\0" -r 49

# Write continuous stream of nul bytes direct to the terminal,
# 1 per second.
$ rout -b 1s -t '\0' -r -1

# Display a greeting slowly (as a human might type)
$ rout -b 20cs "Hello, $USER.\n"

# Display a "spinner" that loops 4 times.
$ rout -b 20cs "\r|\r/\r-\r\\\\" -r 3

# Display all digits between zero and nine with a trailing
# newline.
$ rout "\{0..9}\n"

# Display slowly the lower-case letters of the alphabet,
# backwards without a newline.
$ rout -b 1ds "\{z..a}"

# Display upper-case 'ABC' with newline.
$ rout '\u0041\u0042\u0043\n'

# Display 'foo' with newline.
$ rout '\o146\u006f\x6F\n'

# Clear the screen.
$ rout '\n' -r $LINES

# Write hello to stdout, stderr and the terminal.
$ rout 'hello' -t -r 1 -e -r 1

# Display upper-case letters of the alphabet using octal
# notation, plus a newline.
$ rout "\{\o101..\o132}"

# Display 'h.e.l.l.o.' followed by a newline.
$ rout -a . "hello" -a '' "\n"

# Display "S.O.S. Please!"
$ rout -a . "SOS" -a '' " Please\!\n"

# Display upper-case and lower-case letters of the alphabet
# including the characters in-between, with a trailing newline.
$ rout "\{A..z}\n"

# Display lower-case alphabet followed by reversed lower-case alphabet
# with the digits zero to nine, then nine to zero on the next line.
$ rout "\{a..z}\{z..a}\n\{0..9}\{9..0}\n"

# Display lower-case Greek letters of the alphabet.
$ rout "\{α..ω}"

# Display Cyrillic characters.
$ rout "\{Ѐ..ӿ}"

# Display all printable ASCII characters using hex range:
$ rout "\{x21..x7e}"

# Display all printable ASCII characters using 2-byte UTF-8 range:
$ rout "\{u0021..u007e}"

# Display the entire 2-byte range of UTF-8 characters using aliases:
$ rout "\{umin..umax}"

# Display all printable ASCII characters using 4-byte UTF-8 range:
$ rout "\{U00000021..U0000007e}"

# As above, but use more memorable aliases (and less typing ;)
$ rout "\{Umin..Umax}"

# Display all braille characters.
$ rout "\{u2800..u28FF}"

# Display 'WARNING' in white on red background.
$ rout '\e[37;41mWARNING\e[0m\n'

# Generate 10 random characters.
$ rout '\g' -r 9
```

## History 

This is a rust port of the original C implementation, [`utfout`][utfout].

## FAQ

- Can't my shell do most of this stuff?

  Yes, in some instances. However, `rout` generally does it more succinctly.

  You may want to ask yourself *why* your shell provides those extra features
  though (the UNIX philosophy suggests that maybe it shouldn't (think "do one job
  and do it well" + "creeping featurism").

## Appendices

### Comparison with utfout

`rout` is very similar to [`utfout`][utfout], but not identical. Here are the
major differences:

- `rout` is written in rust.

- `rout` uses a proper parser (using [`pest`][pest] and
  [`pest_consume`][pest_consume]) to handle the embedded escape characters,
  commands and ranges that can be specified in the string arguments.

- `rout` has a comprehensive set of unit tests.

- Command-line handling

  Although `utfout` provides both short and long option names, `rout` only
  provides short option names. The reason being that `rout` uses a simple
  command-line parsing crate that I wrote as there wasn't an appropriate
  existing command-line parser. For further details, see this
  [blog post][blog].

- `rout` does not provide a `-p` flag to allow the escape character prefix to
  be changed.

  Although simple for `utfout`, this isn't available with `rout` because as it
  uses a proper parser, which needs to know the prefix character.

- `utfout ""` would display a null byte whereas with `rout` this is a NOP (no
  output). To display null bytes with `rout`, be explicit: `rout "\0"`.

- `rout` simplifies `utfout` ranges slightly by not requiring a backslash
  for each value inside the range braces:

  | Range | `rout` | `utfout` |
  |-|-|-|
  | hex | `"\{x21..x7e}"` | `"\{\x21..\x7e}"` |
  | utf8 | `"\{U00000021..U0000007e}"` | `"\{\U00000021..\U0000007e}"` |

[blog]: https://ifdeflinux.blogspot.com/2021/05/can-you-handle-argument.html
[pest_consume]: https://github.com/Nadrieril/pest_consume
[pest]: https://github.com/pest-parser/pest
[utfout]: https://github.com/jamesodhunt/utfout
