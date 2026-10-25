# Forth Language

A small stack-based Forth interpreter written in C, with turtle graphics
drawn right in the terminal.

## Files

- `forth.c` — the interpreter: compiles Forth source to a small instruction
  set and runs it on a tiny virtual machine. Colored REPL with a live stack
  display, `help`, `help <word>`, `words`, and clean error messages.
- `example.fs` — definitions, recursion, FizzBuzz, variables.
- `turtle.fs` — turtle graphics demo (flower, star, spiral).

## Build & run

```bash
gcc -Wall -Wextra -std=c11 -o forth forth.c
./forth                 # interactive REPL
./forth < example.fs    # run a script
./forth < turtle.fs     # see the graphics demo
rlwrap ./forth          # REPL with command history (optional)
```

No external dependencies.

## Turtle graphics

Pictures are drawn with Unicode braille characters (8 dots per terminal
cell), in color, directly in the terminal.

```forth
cs yellow color 5 0 do 80 fd 144 rt loop    \ a yellow star
```

Words: `fd bk rt lt pu pd home setxy seth xy heading color cs show`
(long forms: `forward back right left penup pendown`).
Colors: `black red green yellow blue magenta cyan white`.
In the REPL the canvas appears automatically; in scripts call `show`.

## Implemented

- Arithmetic: `+ - * / mod /mod negate abs min max 1+ 1- random`
- Comparison and logic: `= <> < > 0= 0< and or xor invert` (true = -1)
- Stack: `dup drop swap over rot nip tuck 2dup 2drop ?dup depth reset empty?`
- Definitions: `: name ... ;` with recursion, `recurse`, `exit`
- Control flow (nestable): `if else then`, `do loop +loop i j`,
  `begin until`, `begin again`, `begin while repeat`
- Data: `variable`, `constant`, `! @ +! ?`
- Output: `. .s emit cr space spaces ." text"`
- Comments: `\ to end of line` and `( inline )`

## Not implemented

Strings beyond `."`, `leave`/`?do`, `create`/`does>`, floating point, file I/O.

## License

GPL-3.0 — see LICENSE.
