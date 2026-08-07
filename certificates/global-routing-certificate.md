# Global routing assembly certificate

Status: **IMPLEMENTED CONDITIONAL MACHINE CHECK**.

The committed certificate is [`global-routing.json`](global-routing.json).
The independent standard-library checker is
[`../scripts/verify_global_certificate.py`](../scripts/verify_global_certificate.py).

Run from the repository root:

```bash
python scripts/verify_global_certificate.py
```

The success banner is:

```text
GLOBAL ROUTING ASSEMBLY CERTIFICATE ACCEPTED
status: CONDITIONAL_MACHINE_CHECK
```

The word `CONDITIONAL` is essential. The file machine-checks the final
well-foundedness assembly, not every arithmetic and game-semantic lemma that
feeds that assembly.

## What is encoded

The JSON file gives a finite symbolic inventory of the macro system in
Sections 129–138 of `docs/verified-results.md`:

- four lexicographic rank components: outer source, outer proof-token
  multiset, inner source, and inner proof-token multiset;
- 15 named control states for upstream entry, the A/B obligation normalizer,
  factor forks, high returns, marked tails, and terminal macros;
- 12 semantic guard partitions, including unbounded interval partitions for
  B-valuations and high-return valuations;
- 46 transition schemas with their rank effect and exact proof-section
  references.

The certificate stores schemas, not enumerated game positions. For example,
the marked-tail partition covers `D=1`, `D=2`, and the whole unbounded range
`D>=3`; the high-return partition covers `v=5,6` and every `v>=7`.

## Traceability to the proof

| Proof block | Certificate controls | Role |
|---|---|---|
| Sections 14–27 | `minimum_source_entry` | source drop, outer-token drop, or generic normalizer entry |
| Sections 69–90 | `height_one_entry` | complete height-one/resonance entry audit |
| Sections 91–96 | `a_obligation`, `a_test_*`, `b_select`, `b2_*`, `factor_fork` | generic fixed-fibre normalizer |
| Sections 97–103 | `factor_fork`, `high_return`, `marked_tail` | adjacent high return and strict carried-token replacement |
| Sections 104–131 | `marked_tail`, `short_exact_lift` | all long tails and their three short endpoints |
| Sections 121–133 | `terminal_macro` | exponent-two/three terminal entries after strict token replacement |
| Sections 129 and 132 | `rank_components` plus checker reset rule | multiset descent and well-founded fibre composition |
| Sections 134–135 | `marked_tail_result` | exhaustive `D=1`, `D=2`, and `D>=3` split |
| Section 136 | complete equal-rank control DAG | fixed-fibre well-foundedness and subsystem composition |
| Section 137 | both upstream entry states | completeness of all entries |
| Section 138 | whole inventory | exclusion of an infinite marked `DRAW` route |

Every transition also carries its own `proof_sections` list. A reviewer can
therefore start from one JSON rule and jump directly to the human lemma that
justifies it.

## What the checker proves

The checker independently verifies all of the following.

1. The detailed proof file has the exact committed SHA-256 digest after
   platform-independent UTF-8/LF normalization, and every cited section
   exists.
2. Every finite enumeration has distinct cases. Every integer-interval
   partition is disjoint and covers its complete declared domain, including
   an unbounded final interval when required.
3. Every control state has exactly one transition for every declared guard
   case—no missing case and no duplicate dispatch.
4. A `reset` is permitted only after an earlier lexicographic component has
   strictly decreased. Hence a strict schema really decreases the displayed
   lexicographic rank.
5. After all strict schemas are removed, the remaining equal-rank control
   graph is acyclic. Thus a route cannot remain forever at equal outer and
   inner ranks merely by alternating between control subsystems.
6. The inventory cites all decisive assembly Sections 129, 132, 136, 137,
   and 138.

The committed inventory currently contains 29 strict transitions and 17
equal-rank transitions. The latter form a finite DAG.

## Explicit trust boundary

Four obligations remain part of the human proof and are required fields of
the certificate. The checker refuses a file that hides or relabels them:

| Obligation | Current status |
|---|---|
| Universal arithmetic and coordinate identities behind each macro | **HUMAN PROOF**, with finite regression support |
| Refinement: the declared semantic guards cover every legal game case | **HUMAN PROOF** |
| Outcome compatibility: every macro follows an actual `DRAW` continuation while carrying finite tokens separately | **HUMAN PROOF** |
| Productivity: each macro normalization consumes finitely many outcome diamonds | **HUMAN PROOF** |

Therefore acceptance means:

> If the cited local lemmas refine the game exactly as proved in Sections
> 14–137, then the declared global routing system is well-founded and the
> Section 138 infinite `DRAW` route is impossible.

It does not mean that Python has proved those four local obligations from the
original `3n±1` move definition. Calling this a fully machine-checked proof
would be incorrect.

## Lean connection

[`../formal/ThreeNPlusMinusOne/Certificate.lean`](../formal/ThreeNPlusMinusOne/Certificate.lean)
kernel-checks the general metatheory used here:

- a lexicographic product of well-founded relations is well-founded;
- a concrete step relation that maps every step to such a decrease is
  well-founded;
- a well-founded certified relation has no infinite descending path.

The Lean file contains no `axiom`, `admit`, or `sorry`. It does not parse the
JSON or prove the four refinement obligations. The exact boundary is listed
in [`../formal/COVERAGE.md`](../formal/COVERAGE.md).

## Negative tests

[`../tests/test_global_certificate.py`](../tests/test_global_certificate.py)
checks that the verifier rejects:

- a missing declared case;
- a reset before any strict decrease;
- an equal-rank control cycle;
- overlapping integer intervals;
- a mismatched proof-source digest.

These tests protect the checker against accepting the most important malformed
assemblies; they do not enlarge its mathematical trust boundary.
