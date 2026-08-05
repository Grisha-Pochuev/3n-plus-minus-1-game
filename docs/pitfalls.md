# Known pitfalls and invalid shortcuts

This file is as important as the positive results.

## 1. Minimal draw does not propagate indefinitely along A

Let `d` be the smallest hypothetical draw in the conjugated game. Since `B(d)<d`, `B(d)` is already classified. It cannot be a loss, or `d` would be a win. Hence `B(d)` is a win, and therefore `A(d)` must be a draw.

This proves only one propagation step.

For `A(d)`, the side child `B(A(d))` can be larger than `d`, so minimality does not classify it. Therefore one cannot conclude that

\[
d,A(d),A^2(d),\ldots
\]

is entirely drawn.

## 2. A bounded retrograde unknown is not a draw

When `A(q)` lies above a finite cutoff, the bounded solver has insufficient information. Such a position must remain `UNKNOWN` unless its other child already proves it to be a win.

Never report an unknown boundary position as a draw or counterexample.

## 3. A large verified prefix is not the theorem

Extending a verified range can help find patterns and test lemmas, but it does not address the infinite statement by itself.

Every reported range must include:

- exact code revision;
- cutoff and parameters;
- whether the certification is boundary-safe;
- the first unknown position;
- reproducible output.

## 4. Cycles under arbitrary play do not imply draws under optimal play

The cycle `5 -> 7 -> 5` exists, but from `5` a player can move directly to `1`. A graph cycle is not automatically a game-theoretic draw component.

## 5. The one-player `D` strategy does not even force termination

If one designated player always chooses `D`, the opponent can sustain the
exact cycle

\[
5\xrightarrow{U}7\xrightarrow{D}5.
\]

The inequalities `D(D(n))<n` and `D(U(D(n)))<n` compare values at different
turn phases and cannot be iterated to prove termination.  Consequently they
also cannot be used to claim a winning strategy.

## 6. Fixed binary suffix classes cannot determine R globally

The maximal alternating suffix can extend arbitrarily far to the left. Any claim based only on `q mod 2^K` must explain how it handles longer alternating tails.

## 7. Do not assume a fixed small side-branch horizon

Early experiments suggested that along an expanding chain a losing side branch appeared within a small number of steps. Longer runs were later found. A universal constant requires proof and should be attacked adversarially before use.

## 8. Do not preserve unverified numerical claims as facts

Several large bounds and exceptional starting values arose in conversation before a durable script and output were committed. They are recorded only as leads in `docs/unverified-leads.md`.

## 9. Arithmetic exceptional returns alone do not give a rank

Section 9 of `docs/verified-results.md` forces a nonexceptional two-step
`WIN` path from `q` to `B(A(q))`.  It is tempting to allow an arbitrary
two-move word at the four exceptional classes and seek a numerical rank for
that coarse transition system.  This abstraction already contains the exact
cycle

\[
17\xrightarrow{AB}19\xrightarrow{AA}44\xrightarrow{AA}99
\xrightarrow{AA}224\xrightarrow{AB}252\xrightarrow{BB}17.
\]

Equivalently, the legal game word `ABAAAAAAABBB` fixes `17`.  The identity
is regression-tested in `tests/test_game.py`.

This is not a draw counterexample and not a `WIN`-only path: the required
outcome labels of the intermediate vertices are inconsistent.  It disproves
only the coarse proposed rank.  Any successful exceptional-return argument
must retain the forced `LOSS` siblings or their finite proof heights.
