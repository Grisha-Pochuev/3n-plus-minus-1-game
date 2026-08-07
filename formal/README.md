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
third-party dependency, so the initial foundation stays small and easy to
audit.

## Scope

Read [`COVERAGE.md`](COVERAGE.md). At present, Lean formalizes the exact
original move relation, the conjugated expanding branch, and its elementary
arithmetic properties. It does **not** yet kernel-check the alternating-suffix
branch, the marked ordinal rank, or the global no-`DRAW` theorem.

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
5. Formalize the Section 132 fibre lemma.
6. Encode the finite routing cases from Sections 130–137.
7. State and prove Section 138 without adding axioms.
