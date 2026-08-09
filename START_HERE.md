# Start here

This page is for a reader opening the repository after the external audit of
the global proof.

## First: understand the current status

The target theorem is still that optimal play from every odd positive start
reaches `1`.  **The global theorem is currently OPEN in this manuscript.**

An external audit found a real gap in old Section 137.  Corrected Sections
136--138 now remove the false source-descent inference and prove a universal
two-level arithmetic normalization for the previously omitted factorful
exponent-one family.  One provenance/rank attachment lemma remains open.

Read [`AUDIT.md`](AUDIT.md) before interpreting any machine output.

## I only want to check that the code runs

Install Python 3.10 or newer and run:

```bash
python audit.py
```

This checks:

- unit and regression tests;
- the stated finite range of arithmetic identities;
- finite outcome proof DAGs;
- the declared symbolic typed-routing assembly.

The symbolic stage may print `CONDITIONAL_MACHINE_CHECK`.  This is **not** a
proof of the global theorem.  It checks the declared finite control/rank
assembly conditional on the human semantic-refinement obligations; corrected
Section 137 identifies one of those obligations as still open for the
arbitrary factorful exponent-one entry.

## I want the shortest direct certificate check

Run:

```bash
python scripts/verify_global_certificate.py
```

A successful result says that the **declared typed assembly** satisfies its
machine-checked guard/rank conditions.  It does not establish that every
actual game continuation reaches one of those typed entries.

## I want to understand the mathematical repair

Read in this order:

1. [`docs/problem.md`](docs/problem.md) — exact game semantics;
2. [`docs/normal-form.md`](docs/normal-form.md) — binary conjugation;
3. Sections 14--17 of [`docs/verified-results.md`](docs/verified-results.md) — constant-tail coordinates and the exponent-one obstruction;
4. Sections 79--81 — universal consecutive-factor coupling;
5. Sections 87--90 — note the typed hypothesis of the first-factor hidden parent;
6. Sections 91--135 — marked obligation/factor normalizer;
7. corrected Sections 136--138 — the repaired audit and exact remaining attachment lemma;
8. [`docs/global-proof.md`](docs/global-proof.md) — concise status.

The key new statement is the **arbitrary exponent-one attachment lemma** in
Section 137.  It is the current blocking lemma for the global theorem.

## I want to audit the mathematics

Follow [`AUDIT.md`](AUDIT.md).  In particular try to falsify:

- the two-level normalization of `Q_1^epsilon(3^k J(s))`;
- the distinction between a retained source anchor and a temporary routing
  source;
- any use of Section 89 outside the congruence conditions proved by its
  constructor;
- any claimed token replacement that lacks an actual proof-height
  comparison.

## I want to inspect finite outcome certificates

Read [`certificates/README.md`](certificates/README.md), then run for example:

```bash
python scripts/verify_outcome_certificate.py certificates/examples/q10.json
```

This proves the outcome of one finite root.  It is separate from the global
open question.

## I want the article

The repository working manuscript is [`paper/main.tex`](paper/main.tex).
The published Zenodo version predates this external audit.  The repair branch
should therefore be treated as an erratum/work-in-progress rather than as a
new completed proof.

## I want the Lean check

Lean is optional:

```bash
cd formal
lake update
lake build
```

Read [`formal/COVERAGE.md`](formal/COVERAGE.md) first.  Lean does not currently
check the global no-`DRAW` theorem.
