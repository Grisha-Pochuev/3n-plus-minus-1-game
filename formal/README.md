# Lean formalization

This directory is a pinned Lean 4 project for kernel-checking the proof in
stages.

## Build

Install Lean through `elan`, then run:

```bash
cd formal
lake update
lake build
```

Lean is pinned to `v4.32.1`. The project intentionally has no mathlib or other
third-party dependency.

## Scope

Start with [`PROOF_MAP.md`](PROOF_MAP.md), then consult
[`COVERAGE.md`](COVERAGE.md). Lean now formalizes the exact original move
relation, uniqueness of odd-part reduction, the unbounded alternating-suffix
operation, both conjugated branches, and their exact conjugacy with the
original signed game. It also formalizes finite `WIN`/`LOSS` trees, the
`DRAW`-successor lemma, the bounded token-split rank used by the inventory,
and the four-component macro rank with its finite control DAG. The arithmetic
front now includes canonical constant-tail/source coordinates, the exact
minimum-source boundary phase, arbitrary removal of coefficient factors of
three, the two lifted-return source identities, the phase rows through
Section 19, the complete phase-mismatch exclusion of Section 20, and the
complete phase-match long-suffix exclusion of Section 21. It also proves
the surviving Section 22 length-three diamonds and their exact two-level
decrease for every concrete finite winning proof tree, all eight exact
suffix-length-two frames and outcome forks of Section 23, and the universal
A-selecting side-child descent of Section 24. Section 25's universal
B-selecting large diamond and both permitted DRAW-entry transfers are also
kernel-checked. The main Section 26 filter is checked as well: source
survival, valuation two, and the eight residue classes modulo 256 are proved
equivalent, and their next phases are split exhaustively into the stated
sixteen classes modulo 512. Section 27's exact DRAW obligation is preserved
by valuation-two B transfers, higher valuations strictly drop the source,
and three further surviving B transfers are impossible. Section 28 then
splits every A-selecting obligation into its canonical continuation or one
of three fully marked bounded factor frames. Sections 29--31 prove the
opposite-tail switch, its exact common-child recurrence, and the complete
exponent-one source return with its signed valuation bounds. Section 32 then
bounds all three signed continuations after the exponent-two/three switches.

Section 33 is now kernel-checked through the full arithmetic return bridge:
the high-valuation source drop, the scaled signed relation, the even tail
product, the exact lower-exponent `Q_{v-1}` coordinate, and its A-selecting
phase. Sections 34--35 are now kernel-checked: they contain the returned-state
diamonds, the local two-level height payment, and the opening phase and
DRAW-obligation calculations, including the exceptional `v=5` phase. The
exact signed valuations also produce the returned and contracting-side
constant-tail certificates. Every positive high-return coordinate now has
the exact B-selecting valuation-two transition, and an explicitly supplied
DRAW at its return lift yields the returned-side obligation. For `v≥6`, the
common side is linked to the forced LOSS sibling, producing the explicit
lower-height DRAW-to-WIN boundary directly when the actual carriers are
supplied. The
single-worker Lean verification completed successfully. `TokenProvenance.lean` carries exact
finite proof-tree occurrences and proves strict rank payment for replacements
by lower occurrences.
`OccurrenceCertificates.lean` additionally keeps the finite WIN/LOSS branch
choices in `Type`: common grandchildren and legal child certificates are
extracted from already stored data, and a certified forest has a strict
replacement rank whose one-way erasure agrees with the existing logical
occurrence rank. No bare `Winning` or `Losing` proposition is converted into
such a certificate after a route is known.
`CertifiedOccurrenceRefinement.lean` lifts that carrier to the macro boundary
and erases every data-level step into the existing occurrence relation.
`CertifiedHighReturnProvenance.lean` realizes the retained `v≥7` pair payment
as two such data-level macro steps, and
`CertifiedProofPathProvenance.lean` gives the corresponding data-level
first-exit alternative for an arbitrary legal path.
`OccurrenceRefinement.lean` makes the remaining no-reseed condition explicit:
an occurrence forest may change at equal macro rank only by such a certified
replacement, while a fresh forest is permitted only after a strict macro step.

Lean still does **not** kernel-check the concrete refinement from every legal
outcome-compatible game continuation to one of the declared macro cases. The
remaining boundary is represented explicitly by `DrawMacroRefinement`: if
that structure is constructed, Lean proves that every conjugated state is
resolved. A successful build does not construct it and therefore does not yet
prove the unconditional global no-`DRAW` theorem.

This partial status is intentional and explicit: a compiling foundation is
more auditable than a file that states the desired theorem through axioms or
unfinished placeholders.

## Acceptance rules

- no `sorry`, `admit`, or problem-specific axioms;
- every new theorem must identify its source section in the human proof;
- every coverage change must be made in the same commit as the Lean proof;
- `lake build` must succeed from a clean checkout;
- executable examples are welcome, but are not substitutes for universal
  theorems.

## Progress and remaining order

Completed foundation:

1. alternating-suffix deletion `R`, its unique recursive specification, and
   `B(q)<q`;
2. exact original/conjugated move equivalence;
3. finite `WIN`, `LOSS`, `DRAW`, and the no-closed-well-founded-kernel lemma;
4. the one-to-at-most-two token rank used by the concrete inventory;
5. the nested outer/inner rank and equal-rank control DAG;
6. a conditional Section 138 theorem with an explicit refinement parameter.

The latest fresh kernel-checked arithmetic front reaches Sections 34--35:
the local high-valuation diamond, the returned-side selection calculation,
the `v≥6` parity guard, the exceptional `v=5` equality, the transported
constant-tail certificates, and the long common-side height descent. A first exponent-three
valuation at least four forces a strict source drop, and the two concrete
signed valuation equations force the returned `Q_{v-1}` coordinate and its
A-selecting phase. The returned coordinate's B-selecting valuation-two
transition and its conditional DRAW-lift-to-obligation bridge are now checked.
For the long `v≥7` row, a pair of already retained exact WIN occurrences is
now replaced by its two lower common-grandchild occurrences with a strict
forest-rank payment, and that replacement is now embedded as two legal
equal-base occurrence-level forest steps. The remaining obligations are to
preserve the semantic DRAW/`Bad` invariant across those steps, route the
occurrences from the actual DRAW continuation, and construct the global
`DrawMacroRefinement`.

The current occurrence work also has a checked first-exit lemma: a legal path
from a retained finite WIN tree is either covered by that tree or exposes a
strictly lower selected LOSS witness, which can be paid immediately in the
outer forest. A separately checked construction realizes any finite
alternating route with finite outcome witnesses by a compatible proof tree.
That construction may be taller than the already retained tree, so it cannot
be used to install a replacement token after the route has been chosen. The
still-open task is a finite *preinstalled* forest that covers all relevant
zero-rank routes without such reseeding.
The data-level certificate forest now supplies a sound carrier for that task:
its individual branch choices survive across certified descendants, but the
data-level first-exit and safe long-return replacements are now checked. The
concrete preinstallation, universal route coverage, and semantic `Bad`
invariant have not yet been constructed.
The four long-suffix rows are impossible; each surviving length-three row
installs a winning proof tree at least two levels lower; all eight
suffix-length-two rows have their exact outcome fork; and the A-selecting
half of the final switch has its strict height descent; and every remaining
B-selecting fork transfers to the adjacent frame over its selected source.
The later marked normalizer and its outcome-compatible lifecycle remain to be
translated before the refinement parameter can be constructed.

Remaining work is to construct the occurrence-level refinement by formalizing
the universal arithmetic guards, preserving an actual `DRAW` carrier, and
proving productivity for every outcome-compatible case through Section 137.
The new occurrence layer states exactly what must be supplied, but does not
replace that semantic construction with an axiom or with a translation of the
JSON labels.
