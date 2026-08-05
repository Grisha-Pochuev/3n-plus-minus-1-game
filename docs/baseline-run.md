# Reproducible baseline run

Date: 5 August 2026.

This file records a small validation run suitable for an ordinary laptop. It is not evidence for the full infinite theorem beyond checking the implementation and providing a baseline for later comparisons.

## Unit tests

Command:

```bash
python -m unittest discover -s tests -v
```

Result:

```text
Ran 38 tests
OK
```

The tests cover:

- odd-part arithmetic;
- alternating-suffix deletion;
- equality of the original and normal-form children for `m < 10000`;
- strict descent `B(q)<q` for `q < 10000`;
- inversion of `F`;
- exact side-branch identities, their suffix-state refinement, and the forbidden four-WIN block;
- explicit formulas for all four exceptional side-branch classes;
- the uniform full-length formula for every long exceptional suffix;
- the closed recurrence and boundary identities for both constant-tail families;
- canonical constant-tail coordinates and coefficient descent at their shared boundary;
- the exact second-boundary fork and divisible-coefficient frame identities;
- the unique coefficient-source conjugacy and its signed boundary transitions;
- the two lifted source-coefficient identities and the exact lifted side return;
- the exact nondecreasing source-return classes and their phase-mismatch fork;
- the larger diamond excluding every phase-mismatch return;
- the long-suffix filter excluding four phase-match subclasses modulo 128;
- the proof-height descent diamond for every returned suffix of length at least three;
- the exact WIN-source / LOSS-source fork at returned suffix length two;
- the arithmetic characterization and closure of height-one WIN positions;
- exact bounded enumeration of all `B`-predecessors;
- the Gray-code normal form for alternating-suffix deletion;
- the exact eight-state Gray transducer for the expanding move;
- strict descent of all length-three blocks with one `A` and two `B` moves;
- the two-step endpoint rule for nonexceptional WIN-only paths;
- the exact counterexample cycle to a coarse exceptional-return rank;
- the two descent blocks for odd `n < 100000`;
- the exact `5 -> 7 -> 5` counterexample to the one-player always-`D` termination claim;
- soundness invariants of the bounded retrograde labels;
- absence of a certified finite DRAW kernel at the small test cutoff;
- strict decrease of resolution order inside extracted finite proof DAGs.

## Identity and descent verification

Command:

```bash
python scripts/verify_claims.py --limit 200000
```

Output:

```text
verified m-space normal form for 1 <= m <= 200,000
verified B(q) < q for 1 <= q <= 200,000
verified descent blocks for odd 3 <= n <= 400,001
nonterminal descent cases: 199,982
D(n)=1 cases: 18
```

These are finite regression checks of identities that also have symbolic proofs in the documentation.

## Bounded retrograde baseline

Command:

```bash
python scripts/retrograde_prefix.py --limit 200000
```

Output:

```text
limit: 200,000
counts: {'loss': 55067, 'win': 86411, 'unknown': 58523}
first unknown: 7635
resolved prefix end: 7,634
original odd starts covered by that contiguous transformed prefix: n <= 15,269
WARNING: unknown positions are not draws or counterexamples.
```

The calculation is boundary-safe: positions are labeled `LOSS` only if both actual children are already proved `WIN`, and labeled `WIN` only if an actual child is already proved `LOSS`.

## Finite proof extraction

Command:

```bash
python scripts/extract_proof.py 100 --limit 200000 --output results/proof-100.json
```

Result:

```text
59 proof nodes
```

Each proof edge goes to a position resolved earlier by the retrograde procedure. This makes the generated JSON a finite acyclic certificate inside the chosen cutoff.

## Finite DRAW-kernel search

Status: **COMPUTATIONALLY VERIFIED** at revision `03aa398`.

Command:

```bash
python scripts/find_finite_draw_kernel.py --limit 1000000
```

Output:

```text
cutoff: 1,000,000
outcomes: {'loss': 274504, 'win': 430883, 'unknown': 294614}
first unknown: 46582
certified finite DRAW kernel size: 0
No isolated finite DRAW kernel was found at this cutoff.
This does not exclude a boundary-connected or unbounded DRAW kernel.
```

The certificate logic is proved in `docs/verified-results.md`, Section 8. A
nonempty kernel would be a genuine counterexample, not merely a collection of
boundary-dependent `UNKNOWN` nodes. The empty result above is still only a
finite statement at the displayed cutoff.
