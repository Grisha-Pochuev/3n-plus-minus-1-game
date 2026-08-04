# Ready-to-use prompt for local Codex

Continue the mathematical research in this repository on the optimal `3n±1` game.

First read `AGENTS.md` and every document it lists. Run the unit tests and `scripts/verify_claims.py --limit 100000` before proposing changes.

The immediate goal is not a larger brute-force bound. Seek a structural theorem excluding draw positions in the conjugated game

```text
A(q) = ceil(3q/2),
B(q) = R(A(q)),
```

where `R` deletes the maximal alternating binary suffix and `B(q) < q` for every `q > 0`.

Investigate one of these routes, choosing the one that appears most tractable after inspecting the repository:

1. construct a well-founded ordinal or vector-valued rank compatible with the `WIN/LOSS` recursion;
2. build a finite transducer on binary suffixes, augmented by a monotone numerical component, that certifies descent over bounded move blocks;
3. characterize a hypothetical closed draw kernel and derive a contradiction from its minimal elements and predecessor structure;
4. prove a uniform structural property of the side branches along expanding trajectories, without assuming a fixed small horizon.

For every proposed lemma, first search for counterexamples. Mark results accurately as proved, computationally verified, conjectural, disproved, or unverified. Do not repeat the invalid arguments in `docs/pitfalls.md`.

When you obtain meaningful progress, update `docs/proof-ledger.md`, add tests or a reproducible script where appropriate, and make a focused commit.
