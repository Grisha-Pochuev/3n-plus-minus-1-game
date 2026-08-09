# Machine-checkable certificates

The repository uses "certificate" in the standard proof-audit sense: a
generator may be complicated, but it emits a finite witness that a smaller,
independent checker can validate without trusting the generator.

## Finite outcome proof DAGs

`scripts/extract_proof.py` generates a JSON proof that one conjugated position
is `WIN` or `LOSS`. `scripts/verify_outcome_certificate.py` independently
checks the actual two moves, the recursive WIN/LOSS witnesses, reachability,
and a strictly decreasing finite proof rank.

Example:

```bash
python scripts/verify_outcome_certificate.py certificates/examples/q10.json
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

After the external Althöfer audit, this must not be described as a machine
check of the complete no-DRAW proof.  Corrected Section 137 proves an exact
arithmetic normalization for the previously omitted arbitrary factorful
exponent-one family, but the provenance/rank attachment of that family to the
typed global relation remains open.

Read [`global-routing-certificate.md`](global-routing-certificate.md) for the
precise trust boundary.

## Why the global theorem is still open

The missing family is

\[
Q_1^\epsilon(3^kJ(s)),\qquad k>0.
\]

Sections 79--81 normalize it within two consecutive factor levels, but the
returned arithmetic source can be larger than the old retained source.  A
future completion must prove the **arbitrary exponent-one attachment lemma**
of corrected Section 137: the normalized DRAW continuation must strictly
lower the retained source, strictly lower a carried proof token, or enter the
typed Section 136 normalizer while preserving the old retained projection.

The checker cannot prove this semantic attachment merely by checking that the
already-declared JSON cases are internally total.

## One-command audit

An independent reader can run

```bash
python audit.py
```

This executes regression tests, finite identity checks, certificate
generation, finite-certificate verification, and the conditional typed-routing
checker.  A final `AUDIT PASSED` means those **machine-checkable stages**
passed.  It does not mean the global no-DRAW theorem has been proved; see
`AUDIT.md` and corrected Sections 136--138.
