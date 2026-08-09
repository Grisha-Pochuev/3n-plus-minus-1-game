# Global routing assembly certificate

Status: **IMPLEMENTED CONDITIONAL MACHINE CHECK FOR THE DECLARED TYPED ASSEMBLY**.

The committed certificate is [`global-routing.json`](global-routing.json), and
the independent standard-library checker is
[`../scripts/verify_global_certificate.py`](../scripts/verify_global_certificate.py).

Run from the repository root:

```bash
python scripts/verify_global_certificate.py
```

The success banner includes:

```text
GLOBAL ROUTING ASSEMBLY CERTIFICATE ACCEPTED
status: CONDITIONAL_MACHINE_CHECK
```

After the external audit of old Section 137, this success must be interpreted
narrowly.  It verifies the **declared typed control/rank assembly**.  It does
not prove that every actual game continuation, in particular an arbitrary
factorful exponent-one DRAW, has a provenance-preserving entry into that
assembly.

## Audit correction

The old global proof used a false implication from decrease of the canonical
odd coefficient to decrease of its coefficient source.  It also failed to
cover arbitrary

\[
Q_1^\epsilon(3^kJ(s)),\qquad k>0,
\]

because the reverse-factor lemma starts at exponent at least two.

Corrected Section 137 now proves a universal two-level arithmetic
normalization of this missing family from Sections 79--81.  The returned
source can nevertheless be larger than the old retained source.  The
remaining **arbitrary exponent-one attachment lemma** must show that this
normalized continuation either strictly lowers the retained source, strictly
replaces a carried finite proof token, or enters the typed Section 136
normalizer while preserving the old retained projection.

That lemma is currently open.  Consequently certificate acceptance is **not
evidence that the global no-DRAW theorem has been proved**.

## What is encoded

The JSON gives a finite symbolic inventory containing:

- four lexicographic rank components: outer source, outer proof-token
  multiset, inner source, and inner proof-token multiset;
- 15 named control states for the declared upstream entries, A/B obligation
  normalizer, factor forks, high returns, marked tails, and terminal macros;
- 12 semantic guard partitions, including unbounded valuation/tail intervals;
- 46 transition schemas with declared rank effects and proof-section
  references.

The certificate stores schemas, not enumerated game positions.  Its
`minimum_source_entry` state represents an **asserted typed entry class**.  The
checker can prove that the declared cases are total within that class; it
cannot prove that the corrected arbitrary exponent-one family always belongs
to it.

## What the checker proves

The checker verifies:

1. proof-source integrity and presence of cited sections;
2. disjointness and declared coverage of finite and interval guard partitions;
3. one transition for every declared guard case;
4. lexicographically valid reset discipline;
5. acyclicity of the equal-rank control graph after strict transitions are
   removed;
6. structural consistency of the declared typed routing inventory.

These are genuine finite checks.  They do not establish the missing semantic
attachment from the original game to the typed entry relation.

## Explicit trust boundary after the audit

| Obligation | Current status |
|---|---|
| Universal arithmetic and coordinate identities behind each macro | **HUMAN PROOF**, with finite regression support |
| Declared semantic guards refine every legal game case | **OPEN FOR THE GLOBAL THEOREM** because corrected Section 137 isolates the unproved arbitrary exponent-one attachment |
| Outcome-compatible DRAW continuation carries the stated finite tokens | **OPEN FOR THAT SAME ENTRY FAMILY**; proved only for the typed cases cited by the individual lemmas |
| Each declared normalization macro is finite | **HUMAN PROOF** for the typed macros |

Thus the correct reading is:

> If an actual continuation has first been given a provenance-preserving
> typed entry of the kind assumed by corrected Section 136, then the
> certificate checks the declared finite size-change/control assembly for
> that typed relation.

The stronger old reading—"the certificate plus the cited sections proves
that every hypothetical DRAW enters this relation"—is withdrawn.

## Lean connection

[`../formal/ThreeNPlusMinusOne/Certificate.lean`](../formal/ThreeNPlusMinusOne/Certificate.lean)
kernel-checks general well-founded-certificate metatheory.  It does not parse
the JSON, prove the arbitrary exponent-one attachment lemma, or prove the
global no-DRAW theorem.  The exact formalization boundary is in
[`../formal/COVERAGE.md`](../formal/COVERAGE.md).

## Negative tests

[`../tests/test_global_certificate.py`](../tests/test_global_certificate.py)
checks malformed declared assemblies such as missing declared cases, invalid
resets, equal-rank cycles, overlapping intervals, and proof-source digest
mismatch.  These tests protect the finite checker; they cannot detect an
arithmetic/game case that was never validly attached to the declared guard
system.
