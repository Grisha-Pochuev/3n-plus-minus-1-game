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
- Updated `README.md`, `PROOF_MAP.md`, and `COVERAGE.md` in the same change.
  The records deliberately do not claim that the global DRAW refinement or
  the Section 34 outcome-routing step has been completed.

## Verification record

- The one-worker workflow ran successfully twice after the Section 34--35
  additions: run #2 checked the height/transfer work, and run #3 checked the
  added `v=5` exceptional phase.  Both used only the single Lean kernel and
  `leanchecker` job.
- Local Lean tools remain unavailable in this environment; the GitHub checks
  are the claimed kernel verification.  `git diff --check` is clean.
- `lean-one-worker.yml` runs the pull-request Lean check.  The legacy entry is
  also reduced to one Lean job and does not run for pull requests.

## Next exact target

Derive the concrete high-return valuation-two tail and the final common-child
WIN witness required to feed the now-kernel-checked Section 35 boundary.
The remaining global boundary remains the construction of
`DrawMacroRefinement`; it is not an axiom and is not closed by this change.
