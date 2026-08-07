# Start here

This page is for a reader opening the repository for the first time.

## I only want to check that the code runs

Install Python 3.10 or newer, clone the repository, open a terminal in its
root, and run:

```bash
python audit.py
```

On a typical laptop this takes about one or two minutes. The final banner
should be:

```text
=== AUDIT PASSED ===
All machine-checkable local stages passed ...
Next: review the four declared global-certificate trust obligations ...
```

This one command verifies:

- all unit and regression tests;
- the stated finite range of arithmetic identities;
- the committed symbolic global-routing assembly;
- a committed finite outcome proof DAG;
- a newly generated finite proof DAG with an independent checker.

The global routing success is deliberately printed as
`CONDITIONAL_MACHINE_CHECK`. It proves that the declared universal case
inventory has no missing declared case, obeys its lexicographic rank, and has
no equal-rank control cycle. Four links from those schemas to the original
game remain human proof obligations; see
[`certificates/global-routing-certificate.md`](certificates/global-routing-certificate.md).

If your Python command is named `python3`, use `python3 audit.py`.

## I want the shortest direct certificate check

Run:

```bash
python scripts/verify_global_certificate.py
```

Expected summary at the current revision:

```text
GLOBAL ROUTING ASSEMBLY CERTIFICATE ACCEPTED
status: CONDITIONAL_MACHINE_CHECK
inventory: 15 states, 46 transitions, 12 total guard partitions
rank check: 29 strict transitions; 17 equal-rank transitions form a DAG
```

Read the checker scope before citing this as evidence. It is stronger than a
finite numerical search but weaker than a complete formalization of the game.

## I want to understand the claimed solution

Read these three files:

1. [`docs/problem.md`](docs/problem.md) — rules and outcome terminology;
2. [`docs/normal-form.md`](docs/normal-form.md) — the exact binary reduction;
3. [`docs/global-proof.md`](docs/global-proof.md) — the global argument.

Then open [`docs/proof-map.md`](docs/proof-map.md) to see where every part is
proved in the full supplement.

## I want to audit the mathematics

Follow [`AUDIT.md`](AUDIT.md). Do not start by reading all 138 sections
linearly. First inspect the four explicit certificate trust obligations, then
read the final dependency chain in Sections 129–138 and follow only the cited
earlier lemmas.

Expected time is hours or days, not minutes. The proof is long because it
keeps exact source provenance and finite outcome witnesses through all routing
cases.

## I want to inspect finite outcome certificates

Read [`certificates/README.md`](certificates/README.md), then run:

```bash
python scripts/verify_outcome_certificate.py certificates/examples/q10.json
```

This proves the outcome of one finite root. It is separate from the symbolic
global assembly.

## I want to inspect or extend the code

- [`src/README.md`](src/README.md) explains the library modules.
- [`scripts/README.md`](scripts/README.md) lists every supported command.
- [`tests/README.md`](tests/README.md) explains what the tests guarantee.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) gives proof and reporting standards.

## I want the article

The repository-only working manuscript is [`paper/main.tex`](paper/main.tex).
It is not submitted automatically. Its detailed proof supplement is
[`docs/verified-results.md`](docs/verified-results.md).

## I want the Lean check

Lean is optional and is not needed for `python audit.py`:

```bash
cd formal
lake update
lake build
```

Read [`formal/COVERAGE.md`](formal/COVERAGE.md) first. Lean kernel-checks the
general well-founded-certificate metatheorem, but not yet the concrete
JSON-to-game refinement or the global no-`DRAW` theorem.
