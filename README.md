# LTLCheck - Linear Temporal Logic model checker written in Lean 4

## Build

1. Install Lean 4 as described [there](https://leanprover.github.io/lean4/doc/quickstart.html) or [there](https://leanprover.github.io/lean4/doc/setup.html).
Optionally, install the Lean 4 VSCode plugin for interactive editing.

2. Run `lake build`

Resulting binary can be accessed at `./build/bin/ltlcheck`.

## Project structure

`Main.lean` — main executable code (just running the tests).

`Ltlcheck.lean` — placeholder file, imports everything in `Ltlcheck/`.

`Ltlcheck/Util.lean` — utility definitions and functions.

`Ltlcheck/Automata.lean` — definitions of transition systems, Buchi automata,
conversions between them, handshake and interleaving products.

`Ltlcheck/Ltl.lean` — definition of LTL formulas, LTL-to-Buchi translation,
property checking for transition systems.

`Ltlcheck/Syntax.lean` — syntax extension for LTL.

`Ltlcheck/Tests.lean` — illustrated test cases.
