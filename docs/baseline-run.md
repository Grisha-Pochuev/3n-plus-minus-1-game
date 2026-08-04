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
Ran 10 tests
OK
```

The tests cover:

- odd-part arithmetic;
- alternating-suffix deletion;
- equality of the original and normal-form children for `m < 10000`;
- strict descent `B(q)<q` for `q < 10000`;
- inversion of `F`;
- the two descent blocks for odd `n < 100000`;
- soundness invariants of the bounded retrograde labels;
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
