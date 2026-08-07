# Lean coverage

This table is part of the audit record.  It deliberately distinguishes the
human proof from the part already checked by the Lean kernel.

| Claim | Human source | Lean status |
|---|---|---|
| Original positions are positive odd integers | `docs/problem.md` | **PROVED** in `Game.lean` |
| Exact signed move relation (`3n±1`, then remove powers of two) | `docs/problem.md` | **FORMALIZED DEFINITION** in `Game.lean` |
| Expanding normal-form branch `A(q)=⌈3q/2⌉` | `docs/normal-form.md` | **PROVED** in `Game.lean`, including parity formulas and strict expansion |
| Alternating-suffix branch `B(q)=R(A(q))` | `docs/normal-form.md` | **NOT YET FORMALIZED** |
| Multiset ordinal rank and strict descent of proof obligations | `docs/verified-results.md`, Sections 129–137 | **NOT YET FORMALIZED** |
| Optimal play always reaches `1` | `docs/verified-results.md`, Section 138 | **PROVED in the human proof; NOT YET LEAN-CHECKED** |

No Lean file in this directory uses `axiom`, `admit`, or `sorry`.  A successful
`lake build` therefore verifies exactly the rows marked as Lean-proved, and no
more.

Build record: **COMPUTATIONALLY VERIFIED** on 7 August 2026 with Lean 4.32.1;
`lake build` completed successfully. The project has no third-party Lean
dependencies.
