# Command-line tools

All scripts use only the Python standard library. Run them from the repository
root.

| Command | Purpose | Logical status |
|---|---|---|
| `python audit.py` | recommended one-command local audit | orchestrates the checks below |
| `python scripts/verify_claims.py --limit 100000` | normal-form and descent identities over the printed range | **COMPUTATIONALLY VERIFIED** only at that range |
| `python scripts/retrograde_prefix.py --limit 1000000` | boundary-safe `WIN`/`LOSS` propagation | unresolved nodes remain `UNKNOWN` |
| `python scripts/find_finite_draw_kernel.py --limit 1000000` | search for a finite boundary-independent draw countercertificate | nonempty output would be a counterexample; empty output is finite evidence only |
| `python scripts/analyze_suffixes.py --limit 1000000 --suffix-bits 12` | exploratory suffix statistics | experiment, not proof |
| `python scripts/extract_proof.py 100 --limit 200000 --output proof.json` | generate one finite outcome proof DAG | certificate generator |
| `python scripts/verify_outcome_certificate.py proof.json` | validate a finite proof DAG independently | certificate checker |

## Generator versus checker

`extract_proof.py` may use the full retrograde implementation. The checker is
kept separate and small; it reimplements only the exact conjugated moves and
the local `WIN`/`LOSS` proof rules. A bug in the generator therefore cannot
make an invalid certificate pass unless the independent checker has a matching
bug.

## Choosing limits

The default audit uses `100000` for identities and `200000` for its sample
certificate. Larger values cost time and memory but do not strengthen the
infinite theorem. Always publish the exact command, revision, and output for a
notable run.
