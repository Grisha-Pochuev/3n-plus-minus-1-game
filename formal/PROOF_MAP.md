# Lean proof map

This is the shortest route through the kernel-checked development. Read the
files in the order below; each row states exactly what becomes available and
what it does not yet prove.

| Order | File | Kernel-checked result | Still not supplied there |
|---:|---|---|---|
| 1 | [`Game.lean`](ThreeNPlusMinusOne/Game.lean) | Original positive odd states, signed raw moves, relational removal of powers of two, and the expanding map `A` | Executable alternating-suffix deletion |
| 2 | [`NormalForm.lean`](ThreeNPlusMinusOne/NormalForm.lean) | Unbounded recursive `R`, its unique relational specification, `B(q)=R(A(q))`, and `B(q)<q` | Connection back to `3n±1` |
| 3 | [`OriginalNormalForm.lean`](ThreeNPlusMinusOne/OriginalNormalForm.lean) | Uniqueness of odd-part reduction and exact equivalence of original legal children with `A` and `B` | Game-theoretic outcomes |
| 4 | [`ConstantTail.lean`](ThreeNPlusMinusOne/ConstantTail.lean), [`ConstantTailBounds.lean`](ThreeNPlusMinusOne/ConstantTailBounds.lean), [`ConstantTailCoordinates.lean`](ThreeNPlusMinusOne/ConstantTailCoordinates.lean) | Universal long-tail recurrence, boundary bounds, and unique canonical `Q` coordinates | Coefficient source factorization |
| 5 | [`Source.lean`](ThreeNPlusMinusOne/Source.lean), [`MinimumSource.lean`](ThreeNPlusMinusOne/MinimumSource.lean) | Unique `3^k J(s)` factorization and a rigorous global minimum-source choice | Exact source-boundary dynamics |
| 6 | [`SourceBoundary.lean`](ThreeNPlusMinusOne/SourceBoundary.lean), [`ReverseFrame.lean`](ThreeNPlusMinusOne/ReverseFrame.lean) | Exact selected/nonselected phase, minimum-source outcome consequences, and removal of every factor three | Later marked-return normalizer |
| 7 | [`LiftedReturn.lean`](ThreeNPlusMinusOne/LiftedReturn.lean), [`ReturnRows.lean`](ThreeNPlusMinusOne/ReturnRows.lean) | Section 18 source identities, Section 19 rows, all four mismatch adjacent frames, and their strict returned-source bounds | Phase-match long-suffix analysis |
| 8 | [`LargeDiamond.lean`](ThreeNPlusMinusOne/LargeDiamond.lean) | Forced mismatch outcome fingerprint, every valuation case of the Section 20 identity, and exclusion of `5,15,16,26 (mod 32)` | Phase-match analysis |
| 9 | [`PhaseMatch.lean`](ThreeNPlusMinusOne/PhaseMatch.lean) | Exact adjacent frames, strict common-child source bound, unbounded long-suffix child identity, and exclusion of `21,63,64,106 (mod 128)` | Suffix-length-three height descent |
| 10 | [`HeightDescent.lean`](ThreeNPlusMinusOne/HeightDescent.lean) | Section 22 common-grandchild diamonds for `0,42,85,127 (mod 128)` and a two-level decrease for every concrete WIN proof tree | Section 23's eight suffix-length-two rows |
| 11 | [`LengthTwo.lean`](ThreeNPlusMinusOne/LengthTwo.lean) | Section 23 exact frames for all eight length-two rows, returned-child orientation, strict source drop, and the complete forced outcome fork | A-selecting side-child descent |
| 12 | [`SelectingLift.lean`](ThreeNPlusMinusOne/SelectingLift.lean) | Section 24 universal A-selecting side-child identity and a two-level decrease for its concrete WIN proof tree | The Section 25 transfer for the remaining B-selecting forks |
| 13 | [`BSelectingTransfer.lean`](ThreeNPlusMinusOne/BSelectingTransfer.lean) | Section 25 universal B-selecting large diamond and complete transfer of either permitted DRAW entry to the adjacent frame over `B(source)` | Section 26 valuation-two survival filter |
| 14 | [`ValuationTwoFilter.lean`](ThreeNPlusMinusOne/ValuationTwoFilter.lean) | Complete Section 26: exact sixteen-row arithmetic, equivalence between source survival, valuation two, and eight classes modulo 256, plus the exhaustive next-phase split modulo 512 | Section 27 terminal obstruction |
| 15 | [`TransferBound.lean`](ThreeNPlusMinusOne/TransferBound.lean) | Complete Section 27 obligation preservation, high-valuation source drop, and exclusion of three further surviving B transfers | Section 28 A-selecting factor escape |
| 16 | [`ASelectingFactor.lean`](ThreeNPlusMinusOne/ASelectingFactor.lean) | Complete Section 28 source drop, canonical continuation, marked outcome fingerprint, universal factor frame, and exponent bound `1..3` | Section 29 opposite-tail twin switch |
| 17 | [`OppositeTail.lean`](ThreeNPlusMinusOne/OppositeTail.lean) | Complete Section 29 opposite-tail identity and its forced local WIN/non-LOSS outcomes for all three bounded factor exponents | Section 30 common-child twin recurrence |
| 18 | [`TwinRecurrence.lean`](ThreeNPlusMinusOne/TwinRecurrence.lean) | Complete Section 30 common-child recurrence, non-losing common outcome, and forced opposite-tail LOSS alternative | Section 31 signed-boundary source return |
| 19 | [`SignedBoundary.lean`](ThreeNPlusMinusOne/SignedBoundary.lean) | Complete Section 31 exponent-one source identity, strict A-selecting return, exact B-source, and valuation trichotomy | Section 32 exponent-two/three signed bounds |
| 20 | [`LongSwitchBounds.lean`](ThreeNPlusMinusOne/LongSwitchBounds.lean) | Complete Section 32 factor-source estimates, shared-source outcome lemma, and valuation bounds `≤4`, `≤3`, and `≤4` for the three actual switch cases | Section 33 high-valuation exponent-three return |
| 21 | [`HighValuationReturn.lean`](ThreeNPlusMinusOne/HighValuationReturn.lean) | Section 33 opening contradiction: exponent-three first valuation `≥4` forces a strict drop below the minimum-DRAW source | Outcome routing from the returned frame |
| 22 | [`HighValuationReturn.lean`](ThreeNPlusMinusOne/HighValuationReturn.lean) | Exact Section 33 arithmetic: the two signed valuation equations imply the scaled relation, even tail product, returned `Q_{v-1}` coordinate, and its A-selecting phase | Outcome routing from the returned frame |
| 23 | [`HighValuationHeight.lean`](ThreeNPlusMinusOne/HighValuationHeight.lean) | Section 34 returned-child coordinates, boundary/long common-child identities, and a concrete two-level WIN-tree descent when the returned side is WIN | Exposure of that lower occurrence by the actual DRAW continuation |
| 24 | [`HighValuationTransfer.lean`](ThreeNPlusMinusOne/HighValuationTransfer.lean) | Section 35 phase calculation, concrete high-return B-selecting valuation two, exact DRAW-obligation packaging from a return-lift carrier, and a direct `v≥6` DRAW-to-lower-WIN boundary from that carrier plus explicit Section 34 WIN inputs; also the A-selecting shared-child transfer, `v≥6` parity guard, `v=5` exceptional phase, transported constant-tail certificates, and `v=6`/`v≥7` common-side identities | Derivation of the actual Section 33--34 DRAW/WIN carriers |
| 25 | [`Outcome.lean`](ThreeNPlusMinusOne/Outcome.lean) | Finite `Winning`/`Losing` proof trees, `Draw`, a legal `DRAW` child from every `DRAW`, and the generic common-grandchild height lemma | A well-founded relation containing all DRAW continuations |
| 26 | [`TokenRank.lean`](ThreeNPlusMinusOne/TokenRank.lean) | Strict well-founded rank for every inventory split of one token into at most two lower tokens | Proof that every human token change has this form |
| 27 | [`Certificate.lean`](ThreeNPlusMinusOne/Certificate.lean) | General lexicographic well-foundedness and exclusion of infinite descending routes | Concrete game arithmetic |
| 28 | [`MacroCertificate.lean`](ThreeNPlusMinusOne/MacroCertificate.lean) | Four-component abstract rank and all 16 equal-rank control transitions as a finite DAG | Semantic coverage of real game continuations by the macro states |
| 29 | [`TokenProvenance.lean`](ThreeNPlusMinusOne/TokenProvenance.lean) | Exact occurrence-tagged proof tokens, selected-loss/common-grandchild descendants, and strict one- or two-token forest replacement | Semantic proof that every game branch carries one of these occurrences |
| 30 | [`HighReturnProvenance.lean`](ThreeNPlusMinusOne/HighReturnProvenance.lean) | The safe retained-pair case of the long `v≥7` return: exact retained `u,c` WIN tokens become exact lower `p,b` descendants with a strict forest-rank payment, embedded as two legal equal-base outer-forest occurrence steps | Entry, carry, no-reseed, and semantic `Bad` preservation proof that every high-return visit has that retained pair |
| 31 | [`ProofPathProvenance.lean`](ThreeNPlusMinusOne/ProofPathProvenance.lean) | First-exit proof-tree provenance: a legal path is covered by a retained WIN tree or reveals a lower selected LOSS token, and the latter becomes an immediate outer-forest step; finite alternating paths admit compatible (not necessarily rank-compatible) trees | A finite preinstalled forest covering all zero-rank routes, and no-reseed transport across it |
| 32 | [`OccurrenceRefinement.lean`](ThreeNPlusMinusOne/OccurrenceRefinement.lean) | Equal-rank no-reseed boundary and a conditional no-DRAW theorem over occurrence-carrying configurations | Concrete semantic `lift` and `progress` fields |
| 33 | [`Refinement.lean`](ThreeNPlusMinusOne/Refinement.lean) | `DrawMacroRefinement -> no Draw` and hence finite resolution | A value of `DrawMacroRefinement` |
| 34 | [`Termination.lean`](ThreeNPlusMinusOne/Termination.lean) | Transport of resolution and finite optimal proof steps back to the original odd-state game | Unconditional termination until the refinement exists |

The decisive open declaration is therefore not a hidden `sorry`: it is the
absence of a constructed occurrence-level refinement (and, as a corollary, of
a constructed `DrawMacroRefinement`). Its fields expose the remaining
obligations:

1. `lift`: every actual `DRAW` initializes a marked macro configuration;
2. `progress`: every marked configuration containing an actual `DRAW` reaches
   another such configuration by a certified macro step or an exact lower
   occurrence replacement at fixed macro rank.

These fields must formalize all universal arithmetic guards, preservation of an
actual `DRAW` member, exact occurrence alignment, and finite productivity of
the normalizers. The Python JSON checker validates the declared inventory, but
it is not a proof of this semantic field.

For a claim-by-claim status table, read [`COVERAGE.md`](COVERAGE.md). For the
human-to-Lean correspondence, use Sections 14–32 and 129–138 of
[`../docs/verified-results.md`](../docs/verified-results.md) and the transition
identifiers in [`../certificates/global-routing.json`](../certificates/global-routing.json).
