# Start here

This page is for a reader opening the repository for the first time.

## I only want to check that the code runs

Install Python 3.10 or newer, clone the repository, open a terminal in its
root, and run:

```bash
python audit.py
```

On a typical laptop this takes about one or two minutes. The last lines should
be:

```text
=== AUDIT PASSED ===
All machine-checkable local stages passed ...
Next: perform the human proof audit in AUDIT.md Sections 4–5.
```

This means:

- all regression tests passed;
- the exact arithmetic identities passed up to the printed finite limit;
- a finite proof DAG was generated;
- a separate checker accepted every edge and rank decrease in that DAG.

It does **not** mean that the computer checked the infinite no-`DRAW` theorem.
That theorem is presently a human proof.

If your Python command is named `python3`, use `python3 audit.py` instead.

## I want to understand the claimed solution

Read these three files:

1. [`docs/problem.md`](docs/problem.md) — rules and outcome terminology;
2. [`docs/normal-form.md`](docs/normal-form.md) — the exact binary reduction;
3. [`docs/global-proof.md`](docs/global-proof.md) — the global argument.

Then open [`docs/proof-map.md`](docs/proof-map.md) to see where every part is
proved in the full supplement.

## I want to audit the mathematics

Follow [`AUDIT.md`](AUDIT.md). Do not start by reading all 138 sections
linearly. First understand the final dependency chain in Sections 129–138,
then follow only the cited earlier lemmas. Record any objection using the
template in the audit guide.

Expected time is hours or days, not minutes. The proof is long because it
keeps exact source provenance and finite outcome witnesses through all routing
cases.

## I want to inspect machine certificates

Read [`certificates/README.md`](certificates/README.md), then run:

```bash
python scripts/verify_outcome_certificate.py certificates/examples/q10.json
```

The generator and checker are separate. The checker does not import the game
implementation used by the generator.

## I want to inspect or extend the code

- [`src/README.md`](src/README.md) explains the library modules.
- [`scripts/README.md`](scripts/README.md) lists every supported command.
- [`tests/README.md`](tests/README.md) explains what the tests guarantee.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) gives proof and reporting standards.

## I want the article

The repository-only working manuscript is [`paper/main.tex`](paper/main.tex).
It is not submitted automatically. Its detailed proof supplement is
[`docs/verified-results.md`](docs/verified-results.md).

## I want the Lean files

Lean is optional and is not needed for `python audit.py`. Read
[`formal/COVERAGE.md`](formal/COVERAGE.md) first: the current Lean project is
only a partial foundation and does not yet check the global theorem.
