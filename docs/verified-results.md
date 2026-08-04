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

## 5. Consecutive side branches and a forbidden WIN block

Write

\[
S(q)=B(q),\qquad T(q)=B(A(q)).
\]

For every `q>0` outside the four residue classes

\[
q\equiv1,3,12,14\pmod {16},
\]

one has one of the two exact identities

\[
\boxed{T(q)=A(S(q))\quad\hbox{or}\quad T(q)=B(S(q)).}
\]

The choice between the two identities can depend on higher bits.  The four
exceptional classes never occur consecutively along an `A`-orbit: if `q` is
exceptional, then `A(q)` is not exceptional.

### Proof of the side-branch identities

Put `x=A(q)`, `r=R(x)=B(q)`, and let `k` be the length of the maximal
alternating binary suffix of `x`.  The residues of `x=A(q)` modulo `8`, as
`q` runs through the classes modulo `16`, are

```text
q mod 16 :  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
A(q) mod 8: 0  2  3  5  6  0  1  3  4  6  7  1  2  4  5  7
```

Thus `k>=3` is possible exactly in the four exceptional classes.  Outside
them, `k` is `1` or `2`, and `r>0`.

If `k=1`, the binary expansion of `x` is obtained by appending the last bit
`e` of `r` to `r`.  With `y=A(r)`, direct use of

\[
A(2u)=3u,\qquad A(2u+1)=3u+2
\]

shows that `A(x)=2y+e`.  Deleting the maximal alternating suffix from this
number either stops immediately before the appended bit, giving `y`, or
continues through the suffix of `y`, giving `R(y)`.  Hence

\[
R(A(x))\in\{A(r),R(A(r))\}=\{A(B(q)),B(B(q))\}.
\]

If `k=2`, the appended suffix of `x` is `01` when `r` is even and `10` when
`r` is odd.  The same two parity formulas give

\[
A(x)=
\begin{cases}
4A(r)+2,&r\text{ even},\\
4A(r)+1,&r\text{ odd}.
\end{cases}
\]

So `A(x)` is obtained from `A(r)` by appending an alternating two-bit word.
Again `R` either deletes just that word or continues through the alternating
suffix already present in `A(r)`.  The result is respectively `A(r)` or
`R(A(r))`, proving the identities.

Finally, direct substitution in `A(q)=ceil(3q/2)` shows that the four
exceptional residue classes map modulo `16` as follows:

\[
1\mapsto\{2,10\},\quad
3\mapsto\{5,13\},\quad
12\mapsto\{2,10\},\quad
14\mapsto\{5,13\}.
\]

None of the target classes is exceptional.

### Consequence

There are no four consecutive `WIN` positions on an expanding ray:

\[
\boxed{q,A(q),A^2(q),A^3(q)\text{ cannot all be WIN}.}
\]

Suppose otherwise.  Since `q` and `A(q)` are both `WIN`, while `A(q)` is not
a losing child of `q`, the other child `B(q)` must be `LOSS`.  The same
argument gives that `B(A(q))` and `B(A^2(q))` are `LOSS`.

If `q` were nonexceptional, the side-branch identity would make
`B(A(q))` a child of `B(q)`.  This is impossible because every child of a
`LOSS` position is `WIN`.  Hence `q` is exceptional.  Applying the same
argument to `A(q)` shows that `A(q)` is exceptional too, contradicting the
fact that exceptional classes never occur consecutively.

The arithmetic identities are implemented by `side_branch_relation` and
regression-tested in `tests/test_game.py`.  The outcome consequence is also
checked on the boundary-safe finite table in `tests/test_retrograde.py`; the
proof above, rather than that finite check, establishes the general result.

## 6. Exact parameterization of all B-predecessors

Fix `r>=0`.  The complete set of positions `q` satisfying `B(q)=r` can be
described without scanning the positions `q`.

For `k>=1`, let

\[
t_{k,0}=\left\lfloor\frac{2^k}{3}\right\rfloor,
\qquad
t_{k,1}=\left\lfloor\frac{2^{k+1}}{3}\right\rfloor.
\]

These are the values of the length-`k` alternating binary words with most
significant bit `0` and `1`, respectively.  Leading zeroes in `t_{k,0}` are
understood as part of the word.

If `r>0`, put `e=r mod 2`.  Then

\[
\boxed{
B(q)=r
\quad\Longleftrightarrow\quad
F(q)=2^k r+t_{k,e}
}
\]

for some `k>=1`, subject only to the right-hand side lying in the image of
`F`, equivalently not being `1 mod 3`.

Indeed, `R(F(q))=r` says precisely that the binary expansion of `F(q)` is the
expansion of `r` followed by a nonempty maximal alternating suffix.  The most
significant bit of that suffix must equal the last bit `e` of `r`; otherwise
the suffix could be extended one place farther to the left.  This gives
exactly the displayed formula, and the same observation in reverse proves
sufficiency.

For `r=0`, besides the terminal predecessor `q=0`, the positive predecessors
are exactly those for which

\[
F(q)=t_{k,1}
\]

for some `k>=1`, again retaining only values in the image of `F`.  Here the
whole binary expansion must be alternating, so its leading bit is `1`.

The bounded formula enumeration is implemented by
`transformed_B_predecessors` and compared with exhaustive enumeration in
`tests/test_game.py`.

## 7. A descending BBA block

For every `q>0`,

\[
\boxed{B(B(A(q)))<q.}
\]

For every positive `z`, deletion of a nonempty suffix gives

\[
B(z)\le \left\lfloor\frac{3z+1}{4}\right\rfloor.
\]

Also `A(q)<= (3q+1)/2`.  Applying the preceding bound twice therefore gives

\[
B(B(A(q)))
\le
\left\lfloor\frac{27q+23}{32}\right\rfloor<q
\]

for `q>=5`; the four positive smaller cases are direct.

This has a useful consequence for the still-hypothetical smallest draw `d`.
Minimality first forces `B(d)` to be `WIN` and `A(d)` to be `DRAW`.  If
`B(A(d))` is also `DRAW`, then its own `B`-child is smaller than `d` by the
boxed inequality.  That child cannot be a draw by minimality and cannot be a
loss because its parent is a draw.  Hence it is `WIN`.  Thus in this case
`B(A(d))` is another draw with a winning `B`-child.  This sharply limits the
first draw-preserving descent from a minimal counterexample, but does not by
itself exclude later draw branches.
