# Proof dependency map

This map reflects the proof status after the external audit of old Sections
136--138.

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
        ARBITRARY EXPONENT-ONE ATTACHMENT
             LEMMA — CURRENTLY OPEN
                  (Section 137)
                       |
                       v
        global no-DRAW theorem — OPEN
                  (Section 138)
```

## Current dependency/status table

| Component | Status | Precise role |
|---|---|---|
| Binary normal form | **PROVED** | Gives the exact conjugated `A/B` game and strict contraction `B(q)<q`. |
| Sections 14--17 | **PROVED with explicit open warning in old §17** | Constant-tail coordinates and source embedding; identifies the factorful exponent-one obstruction. |
| Sections 79--81 | **PROVED** | Universal coupling of consecutive factor levels and exact signed/raw exit normalization. |
| Sections 69--90 | **PROVED with stated hypotheses** | Height-one and typed factor-frame normalization; Section 89 has a constructor-dependent congruence hypothesis. |
| Sections 91--135 | **PROVED for their typed inputs** | Marked obligation/factor routing and finite proof-token provenance. |
| Section 129 | **PROVED** | Well-founded multiset order on certified proof heights. |
| Section 132 | **PROVED** | Well-founded-fibre lemma. |
| Corrected Section 136 | **PROVED FOR TYPED ENTRIES** | Separates retained anchors from temporary routing cursors and states the scope of the typed normalizer. |
| Corrected Section 137 arithmetic normalization | **PROVED** | Handles arbitrary `Q_1^epsilon(3^k J(s))`, `k>0`, through Sections 79--81 without claiming `t<s`. |
| Section 137 attachment lemma | **OPEN** | Must attach the returned lift/frame to the old retained source/token projection without an unranked reset. |
| Section 138 global theorem | **OPEN** | Follows only after the attachment lemma is proved. |

## What an auditor should try to falsify first

1. The exact two-level normalization in corrected Section 137.
2. Any hidden use of `smaller coefficient => smaller source`.
3. Any promotion of a temporary returned source to the retained source
   anchor without a proved strict comparison.
4. Any use of Section 89 without its congruence hypothesis.
5. Any token-changing edge that does not replace an actual carried token by
   certified lower descendants.
6. A future proof of the arbitrary exponent-one attachment lemma.

## Formalization boundary

This is a human-proof dependency map.  It is not a Lean dependency graph.
See `formal/COVERAGE.md` for the exact Lean scope.

The symbolic file `certificates/global-routing.json` mirrors the declared
typed routing assembly.  Its checker cannot prove the still-open semantic
attachment from an arbitrary factorful exponent-one DRAW to those typed
states.
