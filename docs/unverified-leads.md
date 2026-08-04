# Unverified leads inherited from earlier discussion

These items may be useful, but they are **not accepted facts** until reproduced from committed code.

## Reported large contiguous certification

An earlier discussion claimed that a boundary-safe calculation with transformed cutoff `q <= 2,000,000,000` resolved a contiguous prefix through

```text
q = 12,280,568
```

which would correspond to original odd starts through

```text
n = 24,561,137.
```

No durable code, output file, checksum, or resource accounting accompanied that claim. Reproduce it before citing it.

The current Python solver is designed for correctness and moderate laptop runs, not a two-billion-node calculation.

## Reported long side-branch runs

Earlier exploration mentioned examples where several consecutive side branches along

\[
q,A(q),A^2(q),\ldots
\]

were all winning before a losing side branch appeared. Numbers mentioned included:

- `q = 352027`, with a run reportedly longer than seven;
- `q = 6982996`, with ten winning side branches before a losing one;
- a reported stopping side branch `302006063` in the latter case.

These figures should be treated as search seeds only. Reproduce them with a sufficiently large boundary-safe retrograde database before using them.

## Why preserve these leads

Even if correct, they would disprove only small constant-horizon conjectures, not the main theorem. Their value is to stop Codex from repeatedly proposing an unrealistically small universal horizon.
