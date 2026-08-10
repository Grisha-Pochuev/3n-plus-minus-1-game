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

The word `CONDITIONAL` remains essential after the 10 August closure. The
human proof now supplies the semantic entry that Althöfer's audit found
missing, but the current JSON file does **not** encode that new one-shot entry
component. It still checks only the declared typed control/rank assembly.

## Audit history and closure

The old proof used a false implication from decrease of the canonical odd
coefficient to decrease of its coefficient source. It also failed to cover
arbitrary

\[
Q_1^\epsilon(3^kJ(s)),\qquad k>0,
\]

because the reverse-factor lemma starts at exponent at least two.

Corrected Section 137 withdrew both shortcuts and proved the universal
factor/predecessor normalization, but conservatively left the attachment to
the typed normalizer open.

The missing human bridge is now supplied by
[`../docs/althoefer-audit-closure.md`](../docs/althoefer-audit-closure.md).
It proves:

- the exact B-selecting base row (`v=1` plus an ordinary raw child);
- the A-selecting split (`v>=4` source descent, `v=2` obligation, `v=3`
  constructor satisfying Section 89);
- the order-theoretic distinction between one-shot initialization and later
  reset via an entry bit `eta`.

Thus the repository again claims the global theorem as a **human proof**,
pending independent re-audit. Certificate acceptance is supporting evidence
for the typed assembly, not a machine proof of the closure addendum.

## What is encoded

The JSON gives a finite symbolic inventory containing:

- four lexicographic rank components: outer source, outer proof-token
  multiset, inner source, and inner proof-token multiset;
- 15 named control states for the declared upstream entries, A/B obligation
  normalizer, factor forks, high returns, marked tails, and terminal macros;
- 12 semantic guard partitions, including unbounded valuation/tail intervals;
- 46 transition schemas with declared rank effects and proof-section
  references.

The certificate predates the new explicit entry bit. Its `minimum_source_entry`
control should therefore be read as a declared typed interface, not as a
machine derivation of the one-shot bridge from the original game relation.

## What the checker proves

The checker verifies:

1. proof-source integrity and presence of cited sections;
2. disjointness and declared coverage of finite and interval guard partitions;
3. one transition for every declared guard case;
4. lexicographically valid reset discipline inside the encoded rank;
5. acyclicity of the equal-rank control graph after strict transitions are
   removed;
6. structural consistency of the declared typed routing inventory.

These are genuine finite checks. They do not establish the new semantic
statement `eta:1->0` from the original game; that statement is proved in the
closure addendum.

## Explicit trust boundary after closure

| Obligation | Current status |
|---|---|
| Universal arithmetic and coordinate identities behind each encoded macro | **HUMAN PROOF**, with finite regression support |
| Declared typed guards/refinements used after entry | **HUMAN PROOF + CONDITIONAL MACHINE ASSEMBLY** |
| Althöfer one-shot entry/attachment bridge | **HUMAN PROOF IN `docs/althoefer-audit-closure.md`; NOT ENCODED IN THIS JSON** |
| Outcome-compatible DRAW continuation and carried finite tokens | **HUMAN PROOF** for the cited local/closure lemmas |
| Each encoded normalization macro is finite | **HUMAN PROOF + structural machine checks** |
| Global theorem | **HUMAN-PROOF CLAIM RESTORED; independent re-audit pending** |

The correct reading is therefore:

> The closure addendum supplies a provenance-preserving entry into the typed
> relation. Conditional on the cited human arithmetic/outcome refinements,
> this certificate verifies the finite size-change/control assembly of that
> typed relation.

It would still be incorrect to call the combined repository an end-to-end
machine-checked proof.

## Lean connection

[`../formal/ThreeNPlusMinusOne/Certificate.lean`](../formal/ThreeNPlusMinusOne/Certificate.lean)
kernel-checks general well-founded-certificate metatheory. It does not parse
the JSON, prove the new one-shot attachment lemma, or prove the global
no-`DRAW` theorem. The exact formalization boundary is in
[`../formal/COVERAGE.md`](../formal/COVERAGE.md).

## Negative tests

[`../tests/test_global_certificate.py`](../tests/test_global_certificate.py)
checks malformed declared assemblies such as missing declared cases, invalid
resets, equal-rank cycles, overlapping intervals, and proof-source digest
mismatch. These tests protect the finite checker; they cannot detect an error
in a human semantic bridge that is outside the JSON schema.
