# Formalization work log

## 2026-08-22 — Section 34 local high-valuation height drop

- Imported the complete prior-agent branch at commit `c518f8c` into the active
  local branch `agent/lean-section29`.  Its work is now present under this
  `formal/` directory, including Sections 29--33 and the occurrence-refinement
  layer.
- Added `ThreeNPlusMinusOne/HighValuationHeight.lean` and the corresponding
  root import.  Its source theorems cover the Section 34 child coordinates,
  the `v=4` and `v≥5` common-child identities, and the local two-level
  WIN-tree descent from explicitly supplied `C` and `Z` WIN evidence.
- Added `ThreeNPlusMinusOne/HighValuationTransfer.lean` and its root import.
  It formalizes the opening Section 35 phase calculation: at `v=4` the
  returned side selects the Section 34 occurrence through `B`, while at
  `v≥5` it selects it through `A`.  It also packages an explicitly supplied
  valuation-two DRAW transition as an exact obligation while retaining its
  DRAW parent, extracts an actual DRAW lift from either obligation form, and
  turns an A-selecting shared WIN child into a concrete DRAW-to-WIN boundary.
  The `v≥6` high-return branch now supplies that A-selecting parity guard
  directly from its constant-tail coordinates.  The odd-coefficient `v=5`
  branch is now recorded separately as the exact exceptional equality, so
  the long-range guard is not silently extended across an invalid case.
- Connected the Section 33 signed valuation equations to the Section 35
  vocabulary without an outcome assumption: they now construct the exact
  `IsConstantTail` certificate for the returned state and for its contracting
  `B`-child.
- Closed the conditional long `v≥6` local boundary.  The `v=6` common side is
  the contracting child of the forced LOSS sibling, while at `v≥7` it is the
  expanding child.  A retained WIN tree at the returned side and the selected
  Section 34 WIN child therefore produce a common-side WIN tree two levels
  lower, and the existing obligation closes at that very occurrence.
- Updated `README.md`, `PROOF_MAP.md`, and `COVERAGE.md` in the same change.
  The records deliberately do not claim that the global DRAW refinement or
  the Section 34 outcome-routing step has been completed.
- Proved the formerly missing concrete high-return B-selecting
  valuation-two transition for every positive returned `Q` coordinate with
  `v≥4`. The proof expands both embedded values, factors the shared power of
  two, and checks both tail-bit cases exactly.
- Added the direct carrier bridge: an explicitly supplied `DRAW` at the
  Section 33 return lift now yields the Section 35 `DrawObligation` for the
  returned contracting side. This remains conditional on that actual DRAW
  carrier; no Section 33--34 outcome-routing premise was added or hidden.
- Composed that bridge with the `v≥6` lower-height boundary. A concrete DRAW
  at the return lift, a returned-side WIN tree, and the selected Section 34
  WIN witness now give one exact DRAW-to-WIN boundary at the common side with
  a WIN proof tree at least two levels lower. Those three outcome carriers
  remain parameters of the theorem.
- Added `HighReturnProvenance.lean`, which formalizes the first admissible
  alternative in the red lifecycle obligation for `v≥7`: when exact WIN
  occurrences at the returned state and contracting child are already
  retained, their two exact common-grandchild descendants replace them with
  both individual heights and the common forest rank strictly lower. The
  file deliberately supplies no fresh pair and makes no claim about entry,
  carry, or a later re-entry.

## Verification record

- The one-worker workflow ran successfully four times after the Section 34--35
  additions: run #2 checked the height/transfer work, run #3 checked the
  added `v=5` exceptional phase, run #4 checked the return-to-tail bridge,
  and run #7 checked the complete conditional `v≥6` local boundary. Each used
  only the single Lean kernel and `leanchecker` job. Runs #5--6 exposed and
  then resolved arithmetic details in the new `v=6` identity.
- Run #10 checked the exact high-return valuation-two proof, and run #11
  checked its concrete DRAW-lift-to-obligation bridge. Each run contained
  exactly one GitHub Actions job. Run #9 exposed an intermediate proof error;
  it was repaired before run #10 rather than being suppressed.
- Run #12 checked the composed direct return-lift-to-lower-WIN boundary with
  the same single job.
- Runs #14--16 checked, respectively, the two-token rank composition, the
  paired common-grandchild packaging, and its long high-return specialization.
  Each run used exactly one GitHub Actions job. Run #13 exposed a namespace
  spelling error in the intermediate proof and was repaired in run #14.
- Local Lean tools remain unavailable in this environment; the GitHub checks
  are the claimed kernel verification.  `git diff --check` is clean.
- `lean-one-worker.yml` runs the pull-request Lean check.  The legacy entry is
  also reduced to one Lean job and does not run for pull requests.

## Next exact target

Prove the entry, carry, and no-reseed part of the long high-return lifecycle:
connect actual Section 33--34 DRAW/WIN carriers to the now-kernel-checked
retained-pair replacement. The `v=5` exceptional branch remains a separate
finite target.
The remaining global boundary remains the construction of
`DrawMacroRefinement`; it is not an axiom and is not closed by this change.
