# Independent audit guide

This document tells a third party exactly what is claimed, what can be
checked mechanically, and where human mathematical review is still required.

## 1. Claim under review

**PROVED (human proof).** Every odd positive starting value in the two-player
`3n±1` game has finite remoteness. Equivalently, the conjugated game has no
`DRAW` positions, and optimal play reaches `1` in finitely many moves.

This is not yet a claim of independent acceptance or of a fully
machine-checked theorem.

## 2. Trust boundary

An audit has three separate layers.

| Layer | What it establishes | What it does not establish |
|---|---|---|
| Human proof | The infinite theorem, if every lemma and dependency is correct | Kernel verification or independent acceptance |
| Python checks | Exact implementation agreement and stated finite ranges | The theorem for all integers |
| Lean build | Only the rows marked Lean-proved in `formal/COVERAGE.md` | The global no-`DRAW` theorem |
| Finite certificate | One stated `WIN`/`LOSS` root, checked independently of its generator | All starts or absence of an unbounded `DRAW` set |

No bounded `UNKNOWN` position is called a draw. No finite cutoff is used as a
substitute for well-foundedness.

## 3. Fast reproducibility check

From a clean checkout, record the exact revision:

```bash
git rev-parse HEAD
git status --short
python --version
```

Then run:

```bash
python audit.py
```

This command also generates a finite proof DAG and validates it with the
independent checker. The stages may be run separately as shown in `README.md`.
The packaging baseline is recorded verbatim in
[`docs/audit-run-2026-08-07.md`](docs/audit-run-2026-08-07.md). A mismatch is
not automatically a mathematical counterexample; first record the platform,
Python version, revision, command, and full output.

For the formalized subset:

```bash
cd formal
lake update
lake build
```

The Lean toolchain is pinned to `v4.32.1`; the current project has no
third-party Lean dependency. Read
[`formal/COVERAGE.md`](formal/COVERAGE.md) before reporting the scope of a
successful build.

## 4. Human proof audit

Read the proof in this order:

1. Confirm the game semantics and the `WIN`/`LOSS`/`DRAW` trichotomy in
   [`docs/problem.md`](docs/problem.md).
2. Verify the binary normal form in [`docs/normal-form.md`](docs/normal-form.md),
   especially the unbounded alternating-suffix operation.
3. Read the short assembly in [`docs/global-proof.md`](docs/global-proof.md).
4. Use [`docs/proof-map.md`](docs/proof-map.md) to expand every cited dependency.
5. Check Sections 129–138 of
   [`docs/verified-results.md`](docs/verified-results.md) line by line, then
   follow their backward citations.
6. Compare every dependency and status with
   [`docs/proof-ledger.md`](docs/proof-ledger.md).
7. Check the proposed reasoning against every failure mode in
   [`docs/pitfalls.md`](docs/pitfalls.md).

The decisive obligations are:

- every possible `DRAW` continuation enters the marked transition system;
- the source/proof-token projection never increases;
- every token-changing edge strictly decreases the multiset ordinal rank;
- each equal-projection normalizer fibre is well-founded;
- cross-transitions between terminating subsystems cannot alternate forever;
- the terminal `q=0` statement is correctly transported back to every odd
  original state, including values divisible by three.

## 5. How to report a problem

A useful report should identify the smallest precise failing item:

- document and section;
- exact statement being challenged;
- assumptions available at that point;
- a counterexample, failed inference, or missing case;
- whether the issue affects a local lemma, the dependency map, or the global
  theorem.

Arithmetic counterexamples should include a minimal input and a short script
or calculation. Proof gaps should distinguish an omitted explanation from a
false statement.

## 6. Current audit status

- Human proof assembled: **PROVED within this repository**.
- Python regression suite: **COMPUTATIONALLY VERIFIED**, 101 tests on 7 August
  2026.
- Finite identity run through 100000: **COMPUTATIONALLY VERIFIED** on 7 August
  2026.
- Lean foundations: **COMPUTATIONALLY VERIFIED BUILD** with Lean 4.32.1 on
  7 August 2026; exact theorem coverage remains limited to
  `formal/COVERAGE.md`.
- Independent external review: **PENDING**.
