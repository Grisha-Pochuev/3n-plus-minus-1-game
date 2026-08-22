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

- The inherited commit `c518f8c` records a green GitHub Actions run #52 for
  the prior codebase.  It does not verify the unpushed Section 34 addition.
- Local Lean tools are unavailable in this environment, so no new kernel
  build is claimed.  `git diff --check` is clean.
- `lean-one-worker.yml` is a separate one-job Lean workflow.  It runs for a
  pull-request update limited to `formal/**` (and can also be started by hand);
  the old two-job workflow ignores such formal-only updates.

## Next exact target

Formalize the Section 35 transfer that carries the returned B-selecting DRAW
lift to the lower-height WIN occurrence while preserving the actual DRAW
carrier.  The remaining global boundary remains the construction of
`DrawMacroRefinement`; it is not an axiom and is not closed by this change.
