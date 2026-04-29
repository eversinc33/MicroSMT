# MicroSMT

MicroSMT is an IDA Pro Plugin that aims at generic solving of opaque predicates.

It works by backwards slicing from `jcc`/`setcc` instructions and lifting relevant Hex-Ray microcode slices to z3 expressions. These expressions can then be solved via SMT and the instructions can be patched accordingly.

MicroSMT is currently in *pre-alpha* state - working with microcode has some pitfalls and I do not expect it to work everywhere. Also, not all instruction are currently implemented in the lifter.

Nevertheless, MicroSMT can already autonomously solve opaque predicates in several families (see Examples below).

There are some limitations regarding opaque predicates that can be solved - notable exceptions:
* Predicates that rely on memory access
* Predicates that rely on external API calls and their results
* Predicates that go over several basic blocks

For these types, I recommend full symbolic execution.

### Usage

Point the cursor over a `jcc` or `setcc` instruction, press `Alt+p` and MicroSMT will decide if the condition is an opaque predicate, and if yes, solve it. If you tick the box to patch in the plugin settings menu, MicroSMT will additionally patch accordingly (e.g. `nop` or `jmp` a `jcc` or replace a `setcc` with an assignment to 0 or 1).

### Examples

```
Lumma Stealer
00f1a9c6185b346f8fdf03e7928facfc44fc63e6a847eb21fa0ecd7fb94bb7e3
```

![/img/lumma.gif](/img/lumma.gif)

```
ANELLOADER (Apt10)
362b0959b639ab720b007110a1032320970dd252aa07fc8825bb48e8fdd14332 
```

![/img/apt10.gif](/img/apt10.gif)

### Motivation

While implementing an IR lifter for a bin2bin obfuscator I worked on, I had the idea to lift microcode to z3 for deobfuscation. Since I have never really used SMTs in reverse engineering before, but usually relied on dynamic analysis / tracing, I wanted to try it out. Also, I like generic/automated solutions to problems and MicroSMT fills a gap in tooling I needed.
