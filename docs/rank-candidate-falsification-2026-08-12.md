# Falsification record for three tempting rank candidates

Status: **COMPUTATIONALLY VERIFIED NEGATIVE EVIDENCE**.  This note does not
prove or disprove the no-DRAW theorem.  It records exact counterexamples to
three proposed simplifications of the remaining global rank, so that none is
silently reused in the article.

## 1. A fixed canonical coefficient source is not an acyclic state graph

For a positive state `q`, let `sigma(q)` be the source returned by
`constant_tail_source_coordinates(q)`.  The directed graph containing every
game edge `q -> q'` with `sigma(q')=sigma(q)` already contains

```text
1 -> 2 -> 1,
sigma(1)=sigma(2)=1.
```

Indeed `moves(1)=(2,0)` and `moves(2)=(3,1)`.  Therefore equality of the
canonical source cannot by itself rank the `D=2` attached module.  This is
not an outcome-compatible DRAW cycle: the exact finite outcomes are
`1:WIN`, `2:LOSS`.  It refutes only the source-only graph rank.

Reproducible diagnostic: enumerate both exact children up to `2,000,000`,
retain edges of equal canonical source, and run directed cycle detection.
The first cycle is the one displayed above.

## 2. The side WIN height is not monotone along arithmetic skeleton returns

Canonical finite proof heights were computed for every state resolved by
`bounded_retrograde(2_000_000)`, in the exact resolution order.  The resolved
prefix ends at `81,237`, and the largest constructed height is `111`.

The proposed rule

> replace the current side WIN by the next finite side WIN and use its proof
> height as a nonincreasing rank

is false even on small fully resolved states.  For example, the arithmetic
transition based at `q=15` has the current side state `B(15)=11` of height
`5`, while the next displayed side state is `B(A(15))=17` of height `9`.
Other counterexamples include

```text
q=16:  h(B(q))=3,  h(B(A(q)))=9;
q=17:  h(B(q))=1,  h(B(A(q)))=7;
q=27:  h(B(q))=7,  h(B(A(q)))=23.
```

These are counterexamples to the proposed height monotonicity, not DRAW
positions and not counterexamples to the theorem.

## 3. The finite outcome language shows no small binary DFA

The sound bounded retrograde computation at limit `4,000,000` resolves the
entire prefix through `120,482`.  For the empirical binary `2`-kernel, compare
the sequences

```text
n |-> outcome(2^d n + r),   0 <= r < 2^d,
```

on a common sample of `256` values of `n`.  The number of distinct observed
residual sequences is

```text
d = 1,2,3,4,5,6,7,8
    2,4,8,16,32,64,128,256.
```

Thus every possible residue is empirically distinct through depth eight.
This does not prove that the true outcome language is nonautomatic, but it
strongly falsifies the proposed shortcut through a small suffix DFA.

## Consequence for the current proof plan

The remaining proof cannot rely on any of the following unqualified claims:

1. fixed canonical source implies acyclic routing;
2. successive side WIN witnesses have nonincreasing height;
3. a small finite automaton on a bounded binary suffix classifies outcomes.

The viable directions still require exact outcome provenance: a complete
`D=2` LOSS-anchored exit table, and a high-return lifecycle proof that either
uses already retained token occurrences or pays for one initialization that
cannot recur at fixed earlier rank.
