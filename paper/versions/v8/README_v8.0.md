# Two-Player 3n +/- 1 Game - Version 8.0

## Status

Version 8.0 is the audit-ready reduction written on 12 August 2026. It is
self-contained for every theorem it asserts and passed the claim-by-claim
hostile audit recorded in `HOSTILE_AUDIT_REPORT_v8.0.md`.

Its scope is deliberately limited: it is a rigorous reduction, local-repair,
and gap-report article. It does not claim a proof of the unconditional
no-`DRAW` theorem. The remaining high-return token provenance and lifecycle
obligation is stated explicitly in the manuscript and in the repository.

## Files

- `3n_plus_minus_1_game_v8.0.pdf` - reviewed 17-page manuscript;
- `3n_plus_minus_1_game_v8.0.tex` - self-contained LaTeX source;
- `HOSTILE_AUDIT_REPORT_v8.0.md` - claim-by-claim hostile-audit report;
- `SHA256SUMS_v8.0.txt` - hashes of the release files.

The machine-checkable supporting code, Lean sources, tests, and conditional
global-routing certificate live in the repository outside this historical
snapshot. Their exact research state was committed together with the canonical
version 8 source.

## Build and verification

The release PDF was built with Tectonic. The final log contained no LaTeX
warnings, undefined references, overfull or underfull boxes, or fatal errors.
All 17 rendered pages were visually inspected. The associated repository state
passed 112 unit tests, finite arithmetic checks through 100,000, the conditional
global-routing certificate checker, the local audit driver, and a 30-job Lean
build.

These checks establish the stated partial results and reproducibility. They do
not discharge the explicitly open provenance obligation.
