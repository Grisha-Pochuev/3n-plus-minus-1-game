# Certificates and their trust boundary

The repository uses "certificate" in the standard proof-audit sense: a
generator may be complicated, but it emits a finite witness that a smaller,
independent checker can validate without trusting the generator.

## Finite outcome proof DAGs

`scripts/extract_proof.py` generates a JSON proof that one conjugated position
is `WIN` or `LOSS`. `scripts/verify_outcome_certificate.py` independently
checks the actual two moves, recursive WIN/LOSS witnesses, reachability, and a
strictly decreasing finite proof rank.

Example:

```bash
python scripts/extract_proof.py 100 --limit 200000 --output proof-100.json
python scripts/verify_outcome_certificate.py proof-100.json
```

A valid finite certificate is a genuine proof of its particular root outcome.
It says nothing by itself about unbounded roots or the absence of a global
DRAW kernel.

## Conditional typed global-routing assembly

The repository also commits a finite symbolic inventory checked by

```bash
python scripts/verify_global_certificate.py
```

The checker validates the **declared typed routing system**: guard partitions,
one rule per declared case, lexicographic reset discipline, proof-source
integrity, and acyclicity of the equal-rank control graph.

The Althöfer audit identified a missing semantic entry into this typed system.
Corrected Section 137 repaired the arithmetic/predecessor part, and
`docs/althoefer-audit-closure.md` now supplies the remaining human one-shot
attachment. The global theorem is therefore again claimed as a human proof,
pending independent re-audit.

The JSON itself has **not** been promoted to an end-to-end proof. In
particular, its current rank schema does not explicitly encode the new entry
bit `eta`; the addendum proves that bridge outside the checker.

Read [`global-routing-certificate.md`](global-routing-certificate.md) for the
precise trust boundary.

## Why the one-shot bridge matters

The audited family is

\[
Q_1^\epsilon(3^kJ(s)),\qquad k>0.
\]

The returned factor-free source can exceed the retained outer source. The
closure does not call this a descent. Instead a strict one-shot component
`eta:1->0` initializes the typed inner task once. Same-fibre reinitialization
is then forbidden; a fresh raw reset requires an earlier strict outer
source/proof-token edge.

This is a human order-theoretic statement layered above the existing JSON.

## One-command audit

An independent reader can run

```bash
python audit.py
```

This executes regression tests, finite identity checks, certificate
generation, finite-certificate verification, and the conditional typed-routing
checker. A final machine-audit success means those **machine-checkable stages**
passed. It does not kernel- or machine-check the human closure addendum.

For the exact global human-proof status and hostile audit checklist, read
`AUDIT.md`, `docs/althoefer-audit-closure.md`, and `docs/global-proof.md`.
