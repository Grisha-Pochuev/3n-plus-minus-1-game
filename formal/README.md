# Lean formalization

This directory is a pinned Lean 4 project for kernel-checking the proof in
stages.

## Build

Install Lean through `elan`, then run:

```bash
cd formal
lake update
lake build
```

Lean is pinned to `v4.32.1`. The project intentionally has no mathlib or other
third-party dependency.

## Scope

Read [`COVERAGE.md`](COVERAGE.md). Lean formalizes the exact original move
relation, the conjugated expanding branch, and its elementary arithmetic
properties. It now also kernel-checks the general certificate metatheorem in
[`ThreeNPlusMinusOne/Certificate.lean`](ThreeNPlusMinusOne/Certificate.lean):
a lexicographically ranked relation is well-founded and therefore has no
infinite descending route.

Lean still does **not** kernel-check the alternating-suffix branch, the
concrete marked multiset rank, the JSON-to-game refinement, or the global
no-`DRAW` theorem. A successful build validates the metatheorem used by the
certificate; it does not discharge the certificate's four human proof
obligations.

This partial status is intentional and explicit: a compiling foundation is
more auditable than a file that states the desired theorem through axioms or
unfinished placeholders.

## Acceptance rules

- no `sorry`, `admit`, or problem-specific axioms;
- every new theorem must identify its source section in the human proof;
- every coverage change must be made in the same commit as the Lean proof;
- `lake build` must succeed from a clean checkout;
- executable examples are welcome, but are not substitutes for universal
  theorems.

## Planned order

1. Define and prove uniqueness of alternating-suffix deletion `R`.
2. Prove the exact normal form and `B(q)<q`.
3. Formalize `WIN`, `LOSS`, `DRAW`, and canonical finite proof height.
4. Formalize token multisets and the Section 129 ordinal descent.
5. Refine the abstract Section 132 metatheorem to the concrete outer/inner
   multiset ranks.
6. Encode and prove the finite routing cases from Sections 130–137.
7. State and prove Section 138 without adding axioms.
