# Contributing and independent review

The most valuable contribution is a precise independent audit of the proof.

Before opening an issue or proposing a change, read `AUDIT.md`,
`docs/proof-ledger.md`, and `docs/pitfalls.md`. Every mathematical statement
must be labeled `PROVED`, `COMPUTATIONALLY VERIFIED`, `CONJECTURE`,
`DISPROVED`, or `UNVERIFIED LEAD`.

For a mathematical objection, give the exact document, section, assumptions,
and failing inference or counterexample. For a computational result, include
the Git revision, platform, full command, exact parameters, and output.

Changes to mathematics should include the proof and any relevant regression
test in the same commit. Do not infer the infinite theorem from a finite
cutoff, treat bounded `UNKNOWN` as `DRAW`, or assume arbitrary terminating
play is the same as optimal winning play.

Lean contributions must compile with the pinned toolchain, contain no `sorry`,
`admit`, or new axioms, and update `formal/COVERAGE.md` without overstating
coverage.
