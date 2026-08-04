# Verified mathematical results

Only complete arguments belong in this file.

## 1. One move decreases and the other increases

For every odd `n>1`, exactly one of `3n-1` and `3n+1` is divisible by `4`; the other is divisible by `2` but not by `4`.

After removing all powers of two, one child is less than `n` and the other is greater than `n`. Denote them by

\[
D(n)<n<U(n).
\]

Useful bounds are

\[
D(n)\le \frac{3n+1}{4},
\qquad
U(n)\le \frac{3n+1}{2}.
\]

## 2. Two descent blocks

If `D(n)=1`, the player choosing `D` wins immediately.

Otherwise,

\[
\boxed{D(D(n))<n.}
\]

Proof:

\[
D(D(n))
\le \frac{3D(n)+1}{4}
\le \frac{9n+7}{16}<n
\]

for every `n>1`.

Also,

\[
\boxed{D(U(D(n)))<n.}
\]

For `n>=7`,

\[
\begin{aligned}
D(U(D(n)))
&\le \frac{3U(D(n))+1}{4}\\
&\le \frac{9D(n)+5}{8}\\
&\le \frac{27n+29}{32}<n.
\end{aligned}
\]

For `n=3,5`, one has `D(n)=1`, so the game has already ended.

## 3. Consequence: either player can force finite termination

Suppose a chosen player always plays the decreasing move `D` whenever it is their turn.

After that player's move from `n`, either the game ends, or the opponent moves from `D(n)`.

- If the opponent chooses `D`, the chosen player's next decreasing move reaches `D(D(n))<n`.
- If the opponent chooses `U`, the chosen player's next decreasing move reaches `D(U(D(n)))<n`.

Therefore, after each complete pair of that player's turns, the current positive odd value strictly decreases. The play must terminate after finitely many rounds, regardless of the opponent's choices.

### Important limitation

This proves only that the player can force the game to end. It does **not** prove that the same player can force a win. The forced terminal move may be made by the opponent.

## 4. Exact conjugated form

The derivation in `docs/normal-form.md` gives the conjugated moves

\[
A(q)=\left\lceil\frac{3q}{2}\right\rceil,
\qquad
B(q)=R(A(q)),
\]

with

\[
B(q)<q\quad(q>0).
\]

The implementation and finite identity checks are in `src/optimal_3n1/game.py` and `scripts/verify_claims.py`.
