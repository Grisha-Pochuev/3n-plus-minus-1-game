# Proof dependency map

This map is a navigation aid, not a replacement for the proofs in
`verified-results.md`.

```text
exact game semantics
        |
        v
binary normal form A(q), B(q) and B(q) < q
        |
        v
minimum-source and constant-tail analysis (Sections 14–27)
        |                         |
        |                         v
        |                 height-one analysis (Sections 69–90)
        |                         |
        +------------+------------+
                     v
        canonical finite proof tokens
                     |
         +-----------+-----------+
         |                       |
         v                       v
multiset ordinal rank       marked factor attachment
   (Section 129)              (Sections 130–135)
         |                       |
         +-----------+-----------+
                     v
       well-founded fibre lemma (Section 132)
                     |
                     v
 fixed-fibre marked/obligation normalizer (Section 136)
                     |
                     v
         exhaustive entry audit (Section 137)
                     |
                     v
             no DRAW (Section 138)
                     |
                     v
      optimal play reaches original state 1
```

## Final dependency chain

| Component | Status | Precise role |
|---|---|---|
| Binary normal form | **PROVED** | Replaces the signed odd-integer game by `A(q)=F(q)` and `B(q)=R(F(q))`, with terminal state `0` and `B(q)<q`. |
| Minimum-source frames, Sections 14–27 | **PROVED** | Classify constant-tail exits under a least-source `DRAW` assumption. |
| Height-one analysis, Sections 69–90 | **PROVED** | Handles the boundary case that cannot be closed by the generic long-tail recurrence. |
| Canonical proof heights | **PROVED** | Assign finite heights to certified `WIN`/`LOSS` witnesses so descendant replacement is well-founded. |
| Section 129 | **PROVED** | Ranks a finite multiset of proof heights by the natural sum of powers of `ω`; replacing a token by lower descendants is strict. |
| Sections 130–135 | **PROVED** | Preserve exact source provenance and force every marked factor tail to retain or lower the incoming token; Sections 133–134 close short exponents. |
| Section 132 | **PROVED** | Lifts a nonincreasing ordinal projection plus well-founded equal-projection fibres to global well-foundedness. |
| Section 136 | **PROVED** | Shows the complete marked/factor/obligation normalizer is well-founded inside each fixed outer fibre, including cross-transition control. |
| Section 137 | **PROVED** | Audits all upstream entries: source descent, token descent, or entry into the Section 136 normalizer. |
| Section 138 | **PROVED** | Converts any hypothetical `DRAW` continuation into an impossible infinite path in the well-founded marked relation. |

## What an auditor should try to falsify first

1. Exhaustiveness of the Section 137 entry trichotomy.
2. Preservation of the actual token multiset on equal-rank transitions.
3. Strict token replacement in Section 135 for every exponent `D≥3`.
4. The `D=1,2` short-row treatment in Sections 133–134.
5. The cross-transition argument in Section 136; termination of two
   subsystems separately would not suffice.
6. The passage from absence of a `DRAW` continuation to finite canonical
   proof height and then to optimal termination.

Each of these checks corresponds to a known class of failed shortcuts in
`pitfalls.md`.

## Formalization boundary

The diagram above describes the human proof. It must not be read as a Lean
dependency graph. The current Lean coverage is listed independently in
`formal/COVERAGE.md`.

The finite overlay in `certificates/global-routing.json` mirrors the final
source/token/normalizer inventory. Its checker machine-validates declared
case coverage, rank effects, and the equal-rank DAG; it does not prove that
the semantic cases exhaust the original game relation. The exact four-part
trust boundary is in `certificates/global-routing-certificate.md`.
