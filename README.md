# Optimal 3n±1 Game

Research repository for the two-player `3n±1` game introduced by Ingo Althöfer.

From an odd integer `n > 1`, the player to move chooses one of

- `3n + 1`,
- `3n - 1`,

and then removes every factor of `2`. The player whose move first produces `1` wins.
The open problem asks whether, under optimal play, every odd starting value reaches `1` in finitely many moves.

The repository is private while the problem is open. Its purpose is to preserve rigorous progress, make computational claims reproducible, and support local work with Codex. The long-term goal is a proof suitable for public release and submission for Althöfer's €500 prize.

## Current state

What is rigorously established here:

- an exact binary normal form of the game;
- a conjugated game with one strictly decreasing branch;
- two useful descent inequalities for the decreasing move;
- a sound bounded retrograde solver that never labels boundary-dependent positions as proved;
- explicit warnings about several tempting but invalid arguments.

No complete proof is currently claimed.

## Quick start

```bash
python -m unittest discover -s tests -v
python scripts/verify_claims.py --limit 1000000
python scripts/retrograde_prefix.py --limit 1000000
python scripts/analyze_suffixes.py --limit 1000000 --suffix-bits 12
```

The code uses only the Python standard library.

## Read in this order

1. [`AGENTS.md`](AGENTS.md) — rules for Codex and future agents.
2. [`docs/problem.md`](docs/problem.md) — exact problem and sources.
3. [`docs/normal-form.md`](docs/normal-form.md) — the binary reduction.
4. [`docs/verified-results.md`](docs/verified-results.md) — proved lemmas.
5. [`docs/proof-ledger.md`](docs/proof-ledger.md) — status of every major claim.
6. [`docs/pitfalls.md`](docs/pitfalls.md) — arguments that must not be repeated.
7. [`docs/research-plan.md`](docs/research-plan.md) — prioritized next steps.
8. [`CODEX_PROMPT.md`](CODEX_PROMPT.md) — a ready starting prompt for local Codex.

## Repository principles

- A finite computation is evidence, not a proof of the infinite statement.
- Every computational claim must be reproducible from committed code and parameters.
- `UNKNOWN` in bounded retrograde analysis means exactly unknown; it is not a draw or a counterexample.
- Failed ideas are recorded because they prevent repeated work.
- Prefer structural mathematics over large brute-force runs, especially on a modest local laptop.

## References

- Official prize page: <https://althofer.de/collatz-prizes.html>
- I. Althöfer, M. Hartisch, T. Zipproth, *Analysis of a Collatz Game and Other Variants of the 3n+1 Problem*, Advances in Computer Games, 2024, DOI: `10.1007/978-3-031-54968-7_11`.
