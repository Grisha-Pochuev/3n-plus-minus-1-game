# Proof dependency map

This map reflects the proof status after the Althöfer audit and the 10 August
closure addendum.

```text
exact game semantics
        |
        v
binary normal form A(q), B(q), B(q)<q
        |
        v
constant-tail/source analysis (Sections 14--17)
        |
        +-----------------------------+
        |                             |
        v                             v
factor-level coupling            height-one analysis
(Sections 79--81)                (Sections 69--90)
        |                             |
        +--------------+--------------+
                       v
          typed obligation/factor system
                (Sections 91--135)
                       |
          +------------+------------+
          |                         |
          v                         v
proof-token multiset rank     fibre lemma
   (Section 129)             (Section 132)
          |                         |
          +------------+------------+
                       v
 corrected typed normalizer (Section 136)
                       ^
                       |
 corrected predecessor + exact base anchor
              (Section 137)
                       ^
                       |
     one-shot entry + base phase/valuation split
       (docs/althoefer-audit-closure.md)
                       |
                       v
           complete entry attachment
                       |
                       v
             no DRAW theorem
```

## Current dependency/status table

| Component | Status | Precise role |
|---|---|---|
| Binary normal form | **PROVED** | Gives the exact conjugated `A/B` game and strict contraction `B(q)<q`. |
| Sections 14--17 | **PROVED with the old exponent-one warning retained historically** | Constant-tail coordinates and source embedding. |
| Sections 79--81 | **PROVED** | Universal coupling of consecutive factor levels and exact signed/raw exit normalization. |
| Sections 69--90 | **PROVED with stated hypotheses** | Height-one and typed factor-frame normalization; Section 89 has a constructor-dependent congruence hypothesis. |
| Sections 91--135 | **PROVED for their typed inputs** | Marked obligation/factor routing and finite proof-token provenance. |
| Section 129 | **PROVED** | Well-founded multiset order on certified proof heights. |
| Section 132 | **PROVED** | Well-founded-fibre/reset lemma. |
| Corrected Section 136 | **PROVED FOR TYPED ENTRIES** | Separates retained anchors from temporary routing cursors and proves typed fixed-fibre well-foundedness. |
| Corrected Section 137 arithmetic normalization | **PROVED** | Handles arbitrary `Q_1^epsilon(3^k J(s))`, `k>0`, without claiming returned source `<s`. |
| Corrected Section 137 predecessor reduction | **PROVED** | Removes the unbounded factor-level obstruction and attaches finite token provenance to the gate rows. |
| Corrected Section 137 base-boundary identity | **PROVED** | Gives `9J(x)+1-2e=2^vJ(b)` at the factor-free exponent-two base. |
| Closure addendum: B-selecting base row | **PROVED** | Gives `v=1`, exact ordinary raw child, and source/token/obligation exits. |
| Closure addendum: A-selecting base row | **PROVED** | Gives `v>=2`; `v>=4` is strict source descent, `v=2` is an obligation, and `v=3` automatically satisfies Section 89. |
| Closure addendum: one-shot entry | **PROVED ORDER-THEORETICALLY** | Allows arbitrary first inner source initialization via `eta:1->0`, but forbids same-fibre reinitialization without an earlier source/token decrease. |
| Arbitrary exponent-one attachment lemma | **PROVED IN CLOSURE ADDENDUM** | Joins corrected Section 137 to the typed Section 136 relation. |
| Global no-DRAW theorem | **HUMAN-PROOF CLAIM RESTORED** | Follows from Sections 129, 132, 136 plus the closure addendum; independent re-audit pending. |

## What an auditor should try to falsify first

1. The exact B-selecting assertion `v=1` and the identification of the raw
   exit as an actual ordinary child of `b`.
2. The exceptional B-child estimate `rho(C)<x` in the B-selecting base row.
3. The A-selecting inequality `v>=4 => b<x`.
4. The modulo-three derivation that the `v=3` constructor satisfies precisely
   the additional hypothesis of Section 89.
5. The one-shot reset rule: `eta` must never go `0->1` in an unchanged outer
   source/token fibre.
6. Every token-changing edge must replace an actual carried finite token by
   certified lower descendants.
7. No temporary returned source may be promoted to the *outer* retained
   source merely because it is the current routing cursor.

## Formalization boundary

This is a human-proof dependency map. It is not a Lean dependency graph.
See `formal/COVERAGE.md` for the exact Lean scope.

The symbolic file `certificates/global-routing.json` still mirrors only the
declared typed routing assembly. Its current checker does not encode the new
one-shot entry bit, so acceptance of that JSON remains narrower than the
human closure argument.
