# Hostile audit of `audit_ready_reduction.tex`

Date: 12 August 2026

## Verdict

**PASS AS A RIGOROUS REDUCTION AND GAP REPORT.**

**FAIL AS AN UNCONDITIONAL PROOF OF OPTIMAL TERMINATION.**

The manuscript is acceptable only with its present title, scope notice,
claim ledger, conditional theorem, and open conclusion.  Removing those
qualifications or advertising the paper as a proof that every game terminates
would make it false.

## Audit question

The adversarial question used throughout was not “does the argument look
plausible?” but:

> Does every displayed conclusion follow from proved premises, and does the
> paper ever promote a finite check, an abstract certificate, or an uncarried
> witness into a theorem about the original infinite game?

## Claim-by-claim result

| Claim | Evidence inspected | Verdict |
|---|---|---|
| Finite `WIN`/`LOSS` layers are disjoint | Minimal-sum derivation argument in Lemma 2.2 | PASS |
| Exact outcome recursion and draw-child lemma | Direct finite-proof-tree construction in Proposition 2.4 | PASS |
| `DRAW` means neither player can force a win | Strategy-stealing/preservation argument in Proposition 2.5 | PASS after revision |
| Exact `m`-space normal form | Four parity cases plus explicit `a=0` boundary in Theorem 3.1 | PASS after revision |
| Exact conjugated moves `A,B` | Injectivity and image of `F`, followed by substitution | PASS |
| `B(q)<q` | Global inequality plus direct `q=1` check | PASS |
| `B(B(A(q)))<q` | Affine bound for `q>=5`; direct values `(0,0,1,1)` for `q=1..4` | PASS after revision |
| Valuation formula for `R` | Alternating-bit geometric-sum proof, including whole-word case | PASS after revision |
| No fixed modulus determines `R` | Explicit same-suffix/different-boundary construction | PASS after revision |
| Gray-code deletion formula | Bitwise proof including the all-ones boundary | PASS |
| Eight-state transducer | Explicit state, transition, initialization and acceptance equations | PASS after revision |
| Token replacement rank | `2*3^(h-1)<3^h` for at most two lower children | PASS |
| Lexicographic macro relation is well-founded | Five successive well-founded natural-number coordinates | PASS |
| Complete semantic refinement implies no draws | Minimal bad configuration contradiction, then conjugacy | PASS, CONDITIONAL |
| Repository certificate constructs the semantic refinement | `formal/ThreeNPlusMinusOne/Refinement.lean`, `formal/COVERAGE.md`, `AUDIT.md`, and checker output | FAIL / OPEN |
| Current high-return step decreases an actually carried token multiset | Sections 100, 103, 129 and 136 of `docs/verified-results.md` | FAIL / OPEN |
| Optimal play terminates from every odd start | Depends on the two preceding open rows | NOT PROVED |
| Shortest marked return ($D=1$) pays its retained LOSS token | Direct factorization in Lemma 6.7; regression test | PASS after revision |

## Defects found during this audit and repaired in the manuscript

1. The first draft stated the direct values of `B(B(A(q)))` for
   `q=1,2,3,4` as `(0,0,0,0)`.  The correct values are `(0,0,1,1)`.
   The strict inequality remains true.  The manuscript was corrected.
2. The induction proof of the normal form invoked the induction hypothesis at
   `a=0`, although the nonterminal statement was formulated for positive
   inputs.  The `a=0` case is now handled directly.
3. The valuation identity and the eight-state transducer were originally
   asserted with proof sketches too short for an adversarial article.  Full
   symbolic proofs were added.
4. The original outcome proposition did not explicitly prove that a `DRAW`
   is game-theoretically non-winning for both players.  The draw-preservation
   strategy is now included.
5. The first audit draft described the v6.3 loss-sibling defect as if the same
   named router remained in the current repository.  The paper now separates
   the current high-return defect from the historical v6.3 defects.
6. The formally possible valuation-one branch of the shortest marked return
   was still listed in the inherited trichotomy.  Direct substitution gives an
   additional factor of two in both phases; the paper now proves that the row
   always returns through an actual child of the retained LOSS token.

## Unresolved red defect in the current human assembly

Sections 100 and 103 prove finite outcomes and height inequalities for

`u,c -> p,b`.

Section 129 then lists this as a token replacement, and Section 136 calls
`u,c` “the carried pair”.  The missing premise is a transition proving that
the particular occurrences `h(u),h(c)` are already members of the current
outer or inner token multiset before the replacement.  Finiteness of the
states does not install them as tokens.  No earlier section supplies a legal
seed or a lower-parent replacement that installs both.  Therefore the claimed
decrease of `Phi` or `Psi` is not available.

This is a gap, not a counterexample.  It blocks the current unconditional
theorem.

## Machine checks rerun

The following checks passed:

```text
python -m unittest discover -s tests -v
112 tests passed

python scripts/verify_claims.py --limit 100000
normal form, B(q)<q, and finite descent identities passed

python scripts/verify_global_certificate.py
status: CONDITIONAL_MACHINE_CHECK
15 states, 45 transitions, 12 guard partitions
4 local refinement/outcome obligations remain

python audit.py --limit 100000
AUDIT PASSED within its declared conditional scope

cd formal && lake build
Build completed successfully (30 jobs)

v6.3 structural and arithmetic regression scripts
passed within their declared arithmetic/control-only scope
```

These checks do not prove the missing token membership or the concrete
draw-to-macro refinement.

## PDF audit

- Tectonic compilation succeeded.
- The final PDF has 17 A4 pages.
- Every page was rendered to PNG and inspected in a contact sheet.
- No page is blank, clipped, or visibly corrupted.
- PDF text extraction produced 38k+ characters.  The standard TeX font
  ligatures are represented as ligature code points by the extractor; visual
  inspection confirms their correct rendering.
- The scope notice, conditional theorem, both audit-defect headings, and open
  claim are present in extracted text.
- The final TeX log has no warnings, undefined references, underfull boxes, or
  overfull boxes.
- Final SHA-256:
  - PDF: `353387c7bfb2dc47ac56f10f98e5ba4a45aa4ca0790d3597ba1344b0171ac273`
  - TeX: `4b052e58da1c0e93a2f87a6b7cd222b5dd20529085876f64427caaec278f8e47`

## Conditions for a future unconditional PASS

An unconditional version must, at minimum:

1. construct a concrete `DrawMacroRefinement` (or an equivalent paper-level
   object) rather than assume it;
2. trace exact token identities across every high return, including legal
   installation of `u,c` or a different prepaid rank;
3. prove outcome-compatible coverage and finite productivity for every macro
   guard and reset;
4. rerun this claim-by-claim audit against the revised source and rendered PDF;
5. preferably kernel-check the concrete refinement, not only the abstract
   lexicographic rank.

Until then, the correct publication claim is “rigorous reduction with an
explicit open refinement obligation,” not “proof of the game.”
