# Start here

This page is for a reader opening the repository after the external Althöfer
audit and the subsequent closure repair.

## First: understand the current status

The target theorem is that optimal play from every odd positive start reaches
`1`.

**Current repair-branch status: HUMAN-PROOF CLAIM RESTORED; INDEPENDENT RE-AUDIT PENDING.**

The sequence matters:

1. the published/old proof claimed the theorem;
2. Althöfer's audit found a genuine Section 137 gap;
3. corrected Sections 136--138 conservatively withdrew the theorem and
   isolated the missing attachment lemma;
4. [`docs/althoefer-audit-closure.md`](docs/althoefer-audit-closure.md) now
   supplies that attachment and supersedes the `OPEN` conclusion at the end
   of those corrected sections on this branch.

The closure does **not** restore the invalid shortcuts. It uses a one-shot
entry component to distinguish first initialization of an inner source from a
later forbidden reset.

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

The symbolic stage may print `CONDITIONAL_MACHINE_CHECK`. This is **not** an
end-to-end machine proof of the global theorem. The new one-shot attachment is
a human-proof bridge and is not encoded by the current JSON certificate.

## I want the shortest direct certificate check

Run:

```bash
python scripts/verify_global_certificate.py
```

A successful result says that the **declared typed assembly** satisfies its
machine-checked guard/rank conditions. Read the closure addendum separately
for the semantic entry from the audited exponent-one family.

## I want to understand the mathematical repair

Read in this order:

1. [`docs/problem.md`](docs/problem.md) — exact game semantics;
2. [`docs/normal-form.md`](docs/normal-form.md) — binary conjugation;
3. Sections 14--17 of [`docs/verified-results.md`](docs/verified-results.md) — constant-tail coordinates and the exponent-one obstruction;
4. Sections 79--81 — universal consecutive-factor coupling;
5. Sections 87--90 — typed first-factor gates and the additional hypothesis of Section 89;
6. Sections 91--135 — marked obligation/factor normalizer;
7. corrected Sections 136--138 — conservative repair that still ended `OPEN`;
8. [`docs/althoefer-audit-closure.md`](docs/althoefer-audit-closure.md) — factor-free base split plus one-shot attachment;
9. [`docs/global-proof.md`](docs/global-proof.md) — restored final assembly.

The key new facts in the closure are:

- B-selecting factor-free exponent-two entry gives next factor valuation
  exactly one;
- A-selecting entry gives valuation at least two, with `v>=4` a strict source
  return and `v=2` an exact obligation;
- at `v=3`, the constructor itself proves the congruence required by Section
  89;
- a returned inner source may be larger on the unique `eta:1->0` entry, but
  cannot be reinitialized in the same outer source/token fibre.

## I want to audit the mathematics

Follow [`AUDIT.md`](AUDIT.md). In particular try to falsify:

- the B-phase `v=1` derivation;
- the exceptional raw B-child source estimate;
- the A-phase `v>=4 => b<x` inequality;
- the `v=3` Section 89 congruence;
- the rule that the entry bit cannot reset from `0` to `1` without an earlier
  strict outer source/token edge;
- every claimed finite-token replacement.

## I want to inspect finite outcome certificates

Read [`certificates/README.md`](certificates/README.md), then run for example:

```bash
python scripts/verify_outcome_certificate.py certificates/examples/q10.json
```

This proves the outcome of one finite root. It is separate from the infinite
human proof.

## I want the article

The published Zenodo version predates the external audit. The current repair
branch is the authoritative proof-repair record. The article under `paper/`
should be rebuilt and independently reviewed before a new public proof release.

## I want the Lean check

Lean is optional:

```bash
cd formal
lake update
lake build
```

Read [`formal/COVERAGE.md`](formal/COVERAGE.md) first. Lean does not currently
check the global no-`DRAW` theorem.
