# Adversarial self-audit — v3.0

## Scope

This audit treats `3n_plus_minus_1_game_v3_0.pdf` as the mathematical object to be checked. It does not use a previous manuscript to repair missing logical steps. The Python and JSON files are used only as supporting checks of identities and the finite control graph.

## Issues specifically attacked

1. **Canonical coefficient versus coefficient source.** The proof never infers source descent merely from a smaller coefficient when factors of three can be present. Source comparisons are proved through `J`, the universal state-source bound, or an exact factor-free constructor.
2. **Factorful exponent one.** All four boundary combinations `r=1,2` and factor exponent `k=0,>0` are separated explicitly. The exponent-one predecessor and fixed-tail factor-removal diamond cover the previously dangerous case.
3. **Untyped return from factor removal.** The article defines boundary and loss-sibling entry constructors. The fixed-tail finite branch records the exact incidence rather than calling an arbitrary finite state a ranked token.
4. **Exceptional side return.** The article now proves an alternating-lift identity and an explicit exceptional-side attachment lemma. The two children of the exceptional DRAW state are shown to be an adjacent factor-free frame over the actual LOSS witness.
5. **Source-zero branch.** It is proved in the article. The exact valuation table for `3^n+1-2e` is included; the entry bit is not spent until the finite source-zero normalization reaches a typed entry.
6. **Seeding proof tokens.** The rank orders the entry bit before the outer token multiset. Thus the single `eta:1->0` transition may install the initial finite token data. After entry, outer tokens can change only by certified strict descendant replacement. A second one-shot bit `zeta` handles the first inner token when the entry itself has none; after `zeta=0`, inner tokens also change only by strict descendant replacement.
7. **Temporary source growth.** Routing cursors are distinct from retained source anchors. A numerical value is promoted to the ranked source only under a proved comparison compatible with the currently retained tokens.
8. **B-selecting source comparison.** The B-transfer carries a retained anchor `p` and a cursor `y <= (3p+1)/2`; valuation at least three gives the explicit strict estimate `B(y) <= (27p+7)/48 < p`. Thus the proof does not mistake `B(y)<y` for descent relative to the retained anchor.
9. **No “acyclic therefore well-founded” shortcut.** The article uses the explicit lexicographic rank `(s, eta, Phi(M), zeta, Psi(N), a, c(v), tau)`. Equal-rank control changes decrease the finite control height `c(v)`; same-control tail/factor recurrences decrease `tau`.
10. **Return to arbitrary original odd starts.** The final proof separately handles an original state `n=2m+1`: its children are represented by conjugated states `m` and `R(m)`, so the no-DRAW result for the conjugated game implies finite remoteness of the original state.

## Finite checks reproduced for this package

`verify_v3_0.py` was run successfully after the final LaTeX edit. It checks, on the stated finite ranges in the script:

- source-boundary identities and valuations;
- coefficient pullback identities;
- constant-tail and boundary coefficient bounds;
- the A-side diamond;
- the B-transfer diamond;
- long-tail and fixed-tail identities;
- ordinary/exceptional side arithmetic;
- base-entry valuations, source inequalities and the valuation-three congruence;
- source-zero valuation identities;
- the alternating-lift and exceptional-side attachment formulas;
- the hidden-parent identity;
- acyclicity and longest-path heights of the finite equal-rank control graph.

The final run printed:

```text
v3.0 supporting checks passed
maximum equal-rank control height: 9
```

## PDF/LaTeX checks

The final LaTeX source compiles with no unresolved references and no reported overfull boxes. The PDF has 18 A4 pages, opens normally, and was rendered page-by-page for visual inspection. No clipping, overlap, or broken mathematical glyphs was observed in that render.

## Remaining verification boundary

No explicit arithmetic counterexample or concrete missing boundary case was found in this final pass. The least mechanized part remains the **human semantic case split in the factor/high-return/marked-tail routing lemma**: the finite JSON certificate checks the declared control graph, but it does not independently derive each semantic guard from the game relation. The article supplies the mathematical incidence/token arguments and an exhaustive routing inventory, but this layer is not end-to-end kernel-checked.

Accordingly the appropriate status is: **human proof with extensive adversarial and finite regression checks; not an end-to-end Lean proof and still appropriate for independent external mathematical audit.**
