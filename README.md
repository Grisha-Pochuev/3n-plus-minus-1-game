# Optimal `3n±1` Game

A rigorous and reproducible investigation of the two-player `3n±1` game
(also known as Conway's *Beans-Don't-Talk* game).

## Main claim and current status

Let `n > 1` be odd. A move chooses `3n+1` or `3n-1` and removes every factor
of two. Reaching `1` wins immediately.

The target theorem is:

> For every odd positive starting integer, optimal play reaches `1` after
> finitely many moves. Equivalently, the game has no `DRAW` positions.

**Current status on this repair branch: OPEN IN THE MANUSCRIPT.**

The earlier repository revision labelled the theorem `PROVED (human proof)`.
An external audit by Ingo Althöfer identified a genuine gap in the old
Section 137: a decrease of the canonical odd coefficient was incorrectly
used as a decrease of its coefficient source, and the arbitrary
factorful exponent-one family was not covered by the reverse-factor lemma.

Corrected Sections 136--138 in
[`docs/verified-results.md`](docs/verified-results.md) now:

- withdraw the false source-descent inference;
- prove an exact two-level arithmetic normalization for every
  `Q_1^epsilon(3^k J(s))`, `k>0`, using Sections 79--81;
- distinguish retained source anchors from temporary routing cursors;
- isolate the remaining **arbitrary exponent-one attachment lemma** needed
  to reconnect that normalization to the global source/proof-token rank.

Until that attachment lemma is proved, neither the symbolic certificate nor
the finite computations should be cited as a proof of the infinite no-`DRAW`
theorem.

The concise status and remaining lemma are in
[`docs/global-proof.md`](docs/global-proof.md).  The complete local mathematics
is in [`docs/verified-results.md`](docs/verified-results.md).

## Start here

For an independent check, begin with [`AUDIT.md`](AUDIT.md). The first-time
reader guide is [`START_HERE.md`](START_HERE.md). A useful mathematical reading
route is:

1. [`docs/problem.md`](docs/problem.md) — exact rules and provenance;
2. [`docs/normal-form.md`](docs/normal-form.md) — binary conjugation;
3. Sections 14--17 of [`docs/verified-results.md`](docs/verified-results.md) — the original exponent-one obstruction;
4. Sections 79--81 — the universal factor-level normalization used in the repair;
5. Sections 91--135 — typed normalizer and proof-token provenance;
6. corrected Sections 136--138 — repaired entry audit and the exact remaining lemma;
7. [`docs/global-proof.md`](docs/global-proof.md) — concise current status.

The article source and reviewed PDF live under [`paper/`](paper/).  The
published preprint remains archived at
[doi:10.5281/zenodo.21844684](https://doi.org/10.5281/zenodo.21844684); the
repair branch should be read as a correction to the proof status of that
version.

## Reproduce the checks

Requirements: Python 3.10 or newer; no third-party Python packages.

Run:

```bash
python audit.py
```

The command checks repository layout, tests, finite arithmetic identities,
finite outcome certificates, and the declared symbolic routing assembly.
The symbolic stage may report `CONDITIONAL_MACHINE_CHECK`.  After the
external audit this status has a deliberately narrow meaning: it validates
the declared typed control/rank graph, while the semantic attachment of the
arbitrary factorful exponent-one entry remains a human-proof obligation and
is currently open.

The main stages can also be run separately:

```bash
python -m unittest discover -s tests -v
python scripts/verify_claims.py --limit 100000
python scripts/verify_global_certificate.py
```

Optional larger experiments:

```bash
python scripts/retrograde_prefix.py --limit 1000000
python scripts/find_finite_draw_kernel.py --limit 1000000
python scripts/analyze_suffixes.py --limit 1000000 --suffix-bits 12
```

`UNKNOWN` in a bounded computation means only "not resolved by this
computation". It is neither a `DRAW` nor a counterexample.

### Lean

Lean is optional, pinned to version `v4.32.1`:

```bash
cd formal
lake update
lake build
```

See [`formal/COVERAGE.md`](formal/COVERAGE.md) before interpreting the result.
The current Lean project does not kernel-check the global no-`DRAW` theorem.

## Repository map

| Path | Purpose |
|---|---|
| [`AUDIT.md`](AUDIT.md) | independent audit protocol and current trust boundary |
| [`START_HERE.md`](START_HERE.md) | first-time reader guide |
| [`docs/global-proof.md`](docs/global-proof.md) | concise global status and remaining attachment lemma |
| [`docs/verified-results.md`](docs/verified-results.md) | detailed local results and corrected Sections 136--138 |
| [`docs/proof-ledger.md`](docs/proof-ledger.md) | claim/dependency ledger; being synchronized with the audited repair |
| [`docs/proof-map.md`](docs/proof-map.md) | dependency map |
| [`src/optimal_3n1/`](src/optimal_3n1/) | exact arithmetic and bounded solvers |
| [`tests/`](tests/) | regression and soundness tests |
| [`scripts/`](scripts/) | reproducible verification and exploration |
| [`certificates/`](certificates/) | finite proof DAGs and conditional typed-routing assembly |
| [`formal/`](formal/) | Lean project and explicit formalization coverage |
| [`paper/`](paper/) | article source and publication files |

## Status vocabulary

Research claims should be read according to their explicit local status.
In particular, local lemmas marked `PROVED` remain distinct from the current
`OPEN` status of the global theorem.

## Problem provenance

Ingo Althöfer's official page states the `3n+-1 game` problem addressed by
this repository and records Michael Hartisch's finite verification below one
million. See [`docs/problem.md`](docs/problem.md) for the complete
bibliographic information.

- Official problem page: <https://althofer.de/collatz-prizes.html>
- Althöfer, Hartisch, Zipproth (2024), DOI:
  <https://doi.org/10.1007/978-3-031-54968-7_11>

## License

The repository is released under the [MIT License](LICENSE). Citation
metadata are provided in [`CITATION.cff`](CITATION.cff).
