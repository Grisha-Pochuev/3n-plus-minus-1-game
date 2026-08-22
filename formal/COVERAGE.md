# Lean coverage

This table is part of the audit record. It deliberately distinguishes the
human proof, the JSON assembly check, and the part checked by the Lean kernel.

| Claim | Human source | Lean status |
|---|---|---|
| Original positions are positive odd integers | `docs/problem.md` | **PROVED** in `Game.lean` |
| Exact signed move relation (`3n±1`, then remove powers of two) | `docs/problem.md` | **PROVED** in `Game.lean` and `OriginalNormalForm.lean`, including uniqueness of the odd result |
| Expanding normal-form branch `A(q)=ceil(3q/2)` | `docs/normal-form.md` | **PROVED** in `Game.lean`, including parity formulas and strict expansion |
| Maximal alternating-suffix remainder `R` | `docs/normal-form.md` | **PROVED** in `NormalForm.lean` by an unbounded recursive bit scan with a unique relational specification |
| Alternating-suffix branch `B(q)=R(A(q))` and `B(q)<q` | `docs/normal-form.md` | **PROVED** in `NormalForm.lean` |
| Exact conjugacy of original moves with `A` and `B` | `docs/normal-form.md` | **PROVED** in `OriginalNormalForm.lean` |
| Finite `WIN`/`LOSS`, `DRAW`, and existence of a `DRAW` child | `docs/problem.md`, Sections 9 and 138 | **PROVED** in `Outcome.lean` without a finite boundary |
| Canonical constant-tail coordinates `Q_r^e(a)` for every positive state | Sections 14–15 | **PROVED** in `ConstantTail.lean`, `ConstantTailBounds.lean`, and `ConstantTailCoordinates.lean` |
| Unique factorization of every positive odd coefficient as `3^k J(s)` | Section 17 | **PROVED** in `Source.lean` |
| Globally minimum source exists for every nonempty `DRAW` set | Sections 17 and 137 | **PROVED** in `MinimumSource.lean` |
| Exact exponent-one source phase, forced phase at a minimum `DRAW`, and exponent-two factor lift | Section 17 | **PROVED** in `SourceBoundary.lean` |
| A DRAW coefficient `3^k a` at exponent at least two pulls back to coefficient `a` | Section 16 | **PROVED** in `ReverseFrame.lean`, including arbitrary `k` |
| Canonical sources of `3w` and `3w-1` for positive odd `w` | Section 18 | **PROVED** in `LiftedReturn.lean` |
| Four nondecreasing return rows and their eight phase match/mismatch subclasses | Section 19 | **PROVED** in `ReturnRows.lean` |
| Exclusion of all four minimum-source phase-mismatch classes `5,15,16,26 (mod 32)`, including adjacent frames, source drop, forced outcome fingerprint, and every valuation case of the large diamond | Sections 19–20 | **PROVED** in `ReturnRows.lean` and `LargeDiamond.lean` |
| High phase-match state has an exact adjacent pair `Q_{r+1}^{1-e}(J(c)), Q_r^{1-e}(J(c))` with `r>=1` | Section 21 | **PROVED** in `PhaseMatch.lean` |
| The common child's canonical source is below the minimum and all four long-suffix classes `21,63,64,106 (mod 128)` are impossible | Section 21 | **PROVED** in `PhaseMatch.lean` for arbitrary residue parameters, including both outcome orientations |
| Every surviving suffix-length-three phase match has a common grandchild through both branches and lowers every concrete WIN proof-tree height by at least two | Section 22 | **PROVED** in `HeightDescent.lean` for `0,42,85,127 (mod 128)` |
| The eight suffix-length-two classes have the exact lifted frame, returned-child orientation, strict source drop, and forced WIN/LOSS outcome fork | Section 23 | **PROVED** in `LengthTwo.lean` for `10,31,32,53,74,95,96,117 (mod 128)` |
| The side child of every A-selecting source lift is an ordinary child of `A(source)` and carries a WIN proof tree at least two levels lower under the Section 24 outcome hypotheses | Section 24 | **PROVED** in `SelectingLift.lean` |
| Every B-selecting source lift has the universal large-diamond frame, and either permitted Section 25 DRAW entry transfers to its lower adjacent frame over source `B(source)` | Section 25 | **PROVED** in `BSelectingTransfer.lean`, without residue assumptions or bounded suffix arguments |
| In the sixteen subclasses of the eight length-two rows, `transferred source >= minimum source` iff the B-selecting valuation is exactly two iff the source lies in `10,31,53,95,160,202,224,245 (mod 256)` | Section 26 | **PROVED** in `ValuationTwoFilter.lean` |
| The valuation-two survivors split exhaustively modulo 512, with matching next phase exactly in `10,31,160,202,309,351,480,501` and opposite phase in the complementary eight classes | Section 26 | **PROVED** in `ValuationTwoFilter.lean`, including the parity split from every modulo-256 survivor |
| The two DRAW entry forms make one exact obligation `O(x,e)`; an exponent-two B-selecting transfer preserves it with flipped phase, while every higher valuation from `x<2s` drops below `s` | Section 27 | **PROVED** in `TransferBound.lean` |
| Every Section 26 survivor lies below `2s`, and three further B transfers fall strictly below `s`; hence at most two further B-selecting obligation transfers survive | Section 27 | **PROVED** in `TransferBound.lean` by a universal affine iterate bound and all eight exact initial rows |
| The side child of every A-selecting obligation at `x<2s` has canonical source below the minimum; a DRAW lower member therefore continues as `O(A(x),1-e)` | Section 28 | **PROVED** in `ASelectingFactor.lean` |
| In the adjacent-pair alternative, the exact `WIN/DRAW/WIN/LOSS/DRAW` fingerprint produces a factor frame over the retained side source, and every surviving lower exponent is one of `1,2,3` | Section 28 | **PROVED** in `ASelectingFactor.lean`, including one assembled exhaustive case theorem |
| The retained LOSS state in every bounded Section 28 factor escape has as its expanding child the exact opposite-tail twin of the lower factor-frame member; that twin is WIN, while the lower frame member is non-losing | Section 29 | **PROVED** in `OppositeTail.lean` for both tail orientations and every surviving exponent `1,2,3` |
| The two members of the final factor frame share the exact Section 30 child; that child is non-losing and hence WIN or DRAW, while the opposite-tail WIN has a forced LOSS child | Section 30 | **PROVED** in `TwinRecurrence.lean`, including the signed exponent-one case and the explicit exponent-two/three recurrences |
| At lower factor exponent one, the frame source is exactly `A (A source)`; an A-selecting common child has strictly smaller canonical source, while a B-selecting child has source `B(side)` and the exact valuation `2`, `3`, or `≥4` bounds | Section 31 | **PROVED** in `SignedBoundary.lean` |
| After a lower exponent-two switch the surviving signed valuation is at most four; after exponent three the contracting and expanding continuations have valuations at most three and four | Section 32 | **PROVED** in `LongSwitchBounds.lean`, including exact factor-source bounds, common-source survival, and all three assembled DRAW cases |
| A first valuation at least four in the exponent-three branch forces the returned source below the minimum-DRAW boundary | Section 33 | **PROVED** in `HighValuationReturn.lean`, together with the phase split |
| The two concrete exponent-three signed valuation equations imply the scaled relation, even tail product, exact lower-exponent `Q` coordinate, and its A-selecting phase | Section 33 | **PROVED** in `HighValuationReturn.lean`; outcome routing remains open |
| At the Section 34 returned coordinate, the contracting and expanding children have the exact boundary/long common-child diamonds; if the returned coordinate has a concrete WIN tree and its contracting side is WIN, that common child has a concrete WIN tree at least two levels lower | Section 34 | **PROVED** in `HighValuationHeight.lean`; connecting this occurrence to the actual DRAW continuation remains open |
| The returned contracting side selects the Section 34 lower child through `B` at `v=4` and through `A` at `v≥5`; exact Section 33 signed valuations now produce constant-tail certificates for both the returned state and this contracting side. Every positive high-return coordinate has the exact B-selecting valuation-two transition. A concrete DRAW at its Section 33 return lift packages into the returned side's `DrawObligation`, retaining that DRAW carrier. For `v≥6`, this carrier together with the two explicit Section 34 WIN inputs produces a DRAW-to-WIN boundary at a concrete common-side WIN tree at least two levels lower. The common side is a child of the forced LOSS sibling, with separate `v=6` and `v≥7` identities. The odd-coefficient `v=5` case is formally shown to be the complementary exceptional phase | Section 35 | **PROVED** in `HighValuationTransfer.lean`; deriving the actual Section 33--34 DRAW/WIN carriers remains open |
| Lexicographic product of two well-founded relations is well-founded | `docs/verified-results.md`, Section 132 | **PROVED** in `Certificate.lean` |
| A step relation ranked by that product is well-founded and has no infinite descending path | `docs/verified-results.md`, Sections 132 and 138 | **PROVED** in `Certificate.lean` |
| One token replaced by at most two lower proof-height descendants strictly decreases a well-founded rank | `docs/verified-results.md`, Section 129 | **PROVED** in `TokenRank.lean` using the dependency-free weight `3^h` |
| Exact finite WIN/LOSS proof occurrences can be carried as occurrence-tagged tokens; selected LOSS children and common WIN grandchildren are strict descendants; one or two named retained tokens can be replaced by lower exact descendants with a strict forest-rank payment | Sections 22, 57–64, 129, 135A | **PROVED** in `TokenProvenance.lean`; this does not install a fresh occurrence |
| In the long high-return row `v≥7`, if the incoming forest already retains exact WIN occurrences at the returned state and its contracting child, the two exact common-grandchild occurrences replace them with both heights and the forest rank strictly lower | Sections 100–103, 129, 136 | **PROVED CONDITIONALLY** in `HighReturnProvenance.lean`; the entry, carry, and no-reseed conditions needed to establish that incoming pair remain open |
| Four-component outer/inner rank and equal-rank finite control DAG | `docs/verified-results.md`, Sections 132 and 136; `certificates/global-routing.json` | **PROVED AS AN ABSTRACT MACRO RELATION** in `MacroCertificate.lean` |
| Occurrence-level macro rank: equal macro rank permits only exact lower-forest replacement, while strict macro edges may rebuild the forest | Sections 129, 132, 136 | **PROVED AS A REFINEMENT BOUNDARY** in `OccurrenceRefinement.lean`; semantic lift/progress is not constructed |
| JSON transition inventory refines every legal game continuation | `certificates/global-routing.json` and Sections 91–137 | **NOT YET FORMALIZED**; explicit certificate trust boundary |
| Complete refinement implies no conjugated `DRAW` state | `docs/verified-results.md`, Section 138 | **PROVED CONDITIONALLY** in `Refinement.lean`; the premise is the explicit `DrawMacroRefinement` structure |
| Optimal play always reaches `1` | `docs/verified-results.md`, Section 138 | **OPEN**; Section 138 is conditional on a concrete high-return/refinement premise, which is not constructed in Lean or proved in the current human manuscript |

No Lean file in this directory uses `axiom`, `admit`, or `sorry`. A successful
`lake build` therefore verifies exactly the rows marked Lean-proved, and no
more.

Build record: **COMPUTATIONALLY VERIFIED** on 22 August 2026 with Lean 4.32.1;
`lake build --wfail` and bundled `leanchecker` completed successfully in the
one-worker GitHub Actions run #16. The active pull-request workflow has exactly
one Lean job. The project has no third-party Lean dependencies, and the
warning-free kernel build rejects `sorry`.
