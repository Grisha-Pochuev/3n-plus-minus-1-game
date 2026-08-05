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

For later finite-state work, the ordinary `A/B` choice can be refined.  With
`x=A(q)`, let `k` be its alternating-suffix length and `r=R(x)=B(q)`.  Outside
the exceptional classes `k` is `1` or `2`, and

\[
\begin{array}{c|cc}
 & B(A(q))=A(B(q)) & B(A(q))=B(B(q))\\ \hline
k=1 & r\bmod4\in\{0,3\} & r\bmod4\in\{1,2\}\\
k=2 & r\bmod4\in\{1,2\} & r\bmod4\in\{0,3\}.
\end{array}
\]

For `k=1`, `A(x)` is `A(r)` with the bit `r mod 2` appended.  Deletion stops
at that bit exactly when its value equals the last bit of `A(r)`, which gives
the first row by the four cases for `r mod 4`.  For `k=2`, the appended word
is `10` for even `r` and `01` for odd `r`; deletion stops there exactly when
its leading bit repeats the last bit of `A(r)`, giving the second row.

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

## 7. Three descending two-B blocks

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

The other two orderings of one `A` and two `B` moves also decrease:

\[
\boxed{B(A(B(q)))<q},
\qquad
\boxed{A(B(B(q)))<q}
\qquad(q>0).
\]

Using

\[
A(z)\le\frac{3z+1}{2},
\qquad
B(z)\le\frac{3z+1}{4},
\]

successive substitution gives

\[
B(A(B(q)))\le
\left\lfloor\frac{27q+29}{32}\right\rfloor<q
\]

for `q>=6`, and

\[
A(B(B(q)))\le
\left\lfloor\frac{27q+37}{32}\right\rfloor<q
\]

for `q>=8`.  The remaining positive inputs are direct.  Thus every
three-move word containing two `B` moves and one `A` move is uniformly
descending.  The all-`B` word descends already on its first move.

Explicitly, the exceptional small outputs for `B(A(B(q)))`, at `q=1,...,5`,
are `0,1,0,1,0`; those for `A(B(B(q)))`, at `q=1,...,7`, are
`0,0,0,0,2,2,3`.

This is stronger than a drift estimate, but still does not control paths
whose `B` moves are separated by two or more `A` moves.

## 8. A sound finite DRAW-kernel certificate

Let a boundary-safe retrograde calculation be performed on `0,...,N`, and
let `U` be its set of `UNKNOWN` nodes.  Start with every node in `U` that has
an edge above `N`, then close this set backwards along edges whose parent is
also in `U`.  Call the resulting set `H` and put

\[
K=U\setminus H.
\]

If `K` is nonempty, then every node in `K` is a genuine `DRAW` in the
infinite game.

Indeed, a node in `K` has no edge above the cutoff, and none of its UNKNOWN
children lies in `H`; otherwise the node itself would lie in `H`.  Therefore
every UNKNOWN child of a node in `K` also belongs to `K`.  Any already
resolved child must be `WIN`: an UNKNOWN parent cannot have a proved `LOSS`
child, because that would already prove the parent `WIN`.  Finally, every
node in `K` has at least one child in `K`; if both children were proved
`WIN`, bounded retrograde would already have proved the parent `LOSS`.

Thus a player can avoid losing from `K` by always choosing a child in `K`.
If both players do so, play is infinite.  If the opponent instead exits `K`,
the exit hands the player a position already proved `WIN`, from which they
can use its finite winning strategy.  Both players have such a non-losing
strategy, so neither can force a win and all positions in `K` are `DRAW`.

The function `certified_finite_draw_kernel` computes exactly this set with a
reverse reachability pass.  A nonempty result is therefore a rigorous finite
countercertificate.  An empty result only says that no such certificate is
isolated from the selected boundary; it does not exclude an unbounded draw
kernel.

## 9. Two steps along a WIN-only path

Every `WIN` or `LOSS` position has a finite proof height.  This follows
directly from the least fixed-point construction of the two outcomes; since
there are only two children, the union of the finite stages is already a
fixed point.  Equivalently, a winning strategy tree is finitely branching,
and if all its plays terminate then Koenig's lemma makes the tree finite.

Choose the canonical height

\[
h(0)=0,
\]

\[
h(x)=1+\min\{h(y):y\text{ is a LOSS child of }x\}
\quad(x\text{ WIN}),
\]

and

\[
h(x)=1+\max\{h(y):y\text{ is a child of }x\}
\quad(x\text{ LOSS}).
\]

Let `x_0,x_1,x_2` be three `WIN` positions such that each is a child of the
preceding position.  If

\[
x_0\not\equiv1,3,12,14\pmod {16},
\]

then

\[
\boxed{x_2=B(A(x_0))}
\qquad\hbox{and}\qquad
\boxed{h(x_2)\le h(x_0)-2}.
\]

Indeed, because `x_0` and its selected child `x_1` are both `WIN`, the other
child `ell` of `x_0` must be `LOSS`.  If `x_1=A(x_0)`, then
`ell=B(x_0)`.  The side-branch identity makes `B(A(x_0))` a child of `ell`,
so it is `WIN`; it is also the `B`-child of `x_1`.  Hence it is the unique
`WIN` child of `x_1` and equals `x_2`.

If `x_1=B(x_0)`, then `ell=A(x_0)`.  Now `B(A(x_0))` is directly a child of
the losing `ell`, hence is `WIN`, while the side-branch identity makes it a
child of `x_1`.  It again has to equal `x_2`.

In both cases `x_2` is a child of the losing position `ell`.  The height
recursion gives

\[
h(x_0)=1+h(ell)\ge h(x_2)+2.
\]

Consequently, an infinite path containing only `WIN` positions must visit
the four exceptional residue classes infinitely often.  Otherwise a tail
would be entirely nonexceptional, and the displayed inequality on either
parity subsequence of the path would give an infinite descending sequence of
nonnegative proof heights.

This does not yet exclude such a path: an exceptional visit can reset the
proof height.  It reduces the remaining obstruction to the exceptional
returns of the finite binary transducer.

## 10. The canonical base-DRAW skeleton

Call a hypothetical `DRAW` position `q` a **base draw** when `B(q)` is
`WIN`.  Every nonempty draw set has a base draw: its smallest element `d`
has `B(d)<d`, and this child can be neither `DRAW` nor `LOSS`.

Starting from any base draw `q`, put

\[
r_j=B^j(A(q))\qquad(j\ge0).
\]

Here `r_0=A(q)` is `DRAW`, because the other child `B(q)` is `WIN`.  Follow
the `B`-children while they remain `DRAW`.  This process must stop: the
values strictly decrease, while a `DRAW` position cannot have the terminal
loss `0` as a child.  Thus for a unique `k>=0`,

\[
r_0,\ldots,r_k\text{ are DRAW},
\qquad
r_{k+1}\text{ is WIN}.
\]

The last draw `r_k` is the next base draw.  If `k>=2`, the two-B descent
gives

\[
r_k\le B(B(A(q)))<q.
\]

For the smallest draw `d`, this is impossible, so its first skeleton step
has only the alternatives

\[
\begin{array}{ll}
k=0:& A(d)\text{ is a base draw and }B(A(d))\text{ is WIN},\\
k=1:& B(A(d))\text{ is a base draw and }B(B(A(d)))\text{ is WIN}.
\end{array}
\]

There is also an exact local fingerprint below `d`.  Set

\[
x=B(B(d)),
\qquad
y=B(A(B(d))).
\]

Both are smaller than `d`.  Since `B(d)` is `WIN`, either

\[
\boxed{x\text{ is LOSS}}
\]

or

\[
\boxed{x\text{ and }y\text{ are both WIN}}.
\]

Indeed, if `x` is not `LOSS`, minimality makes it `WIN`.  The other child
`A(B(d))` must then be `LOSS`, because `B(d)` itself is `WIN`; consequently
both children of `A(B(d))`, including `y`, are `WIN`.

If `d` is nonexceptional, the side-branch relation sharpens this dichotomy:

- if `B(A(d))=A(B(d))`, then `x` is `LOSS`;
- if `B(A(d))=B(B(d))`, then `x=B(A(d))` is `WIN`, `A(B(d))` is `LOSS`,
  `y` is `WIN`, and `A^2(d)` is `DRAW`.

For the first bullet, `B(A(d))` is a non-losing child of the winning
position `B(d)`, so its other child `x` must be losing.  For the second,
`B(A(d))=x<d` is neither a loss (it is a child of a draw) nor a draw (by
minimality), hence it is winning.  The remaining assertions follow from the
two-child outcome recursion.

This skeleton is well founded between successive `A` moves, but its `k=0`
and `k=1` steps may increase the integer.  A final proof still needs a rank
that controls those two cases and the exceptional residue classes.

## 11. Ordinary transitions of the base-DRAW skeleton

The canonical skeleton admits a sharper size-change table away from the
exceptional classes.  Let `q` be a base draw, put `s=B(q)`, and let `k` be
the index from Section 10.  Write `C(u)` for the letter `A` or `B` in the
ordinary side relation

\[
B(A(u))=C(u)(B(u)).
\]

First suppose `k>=1`, so `z=B(A(q))` is `DRAW`.  If both `q` and `s` are
nonexceptional, exactly one of the following holds:

\[
\begin{array}{c|c|c}
C(q)&C(s)&\text{consequence}\\ \hline
A&A\text{ or }B&k=1\text{ and }h(B(z))\le h(s)-2,\\
B&B&k=1\text{ and }h(B(z))\le h(s)-2,\\
B&A&k\ge2\text{ and the next base draw is smaller than }q.
\end{array}
\]

To prove the table, `z=C(q)(s)` is a non-losing child of the winning
position `s`; its other child `ell` is therefore `LOSS`.

If `C(q)=A`, then `z=A(s)` and `ell=B(s)`.  The value

\[
t=B(A(s))=B(z)
\]

is a child of `ell` by the side relation at `s`, so it is `WIN` and
`h(t)<=h(s)-2`.  Hence the first `B`-child of `z` already ends the draw run,
which is `k=1`.

If `C(q)=B`, then `z=B(s)` and `ell=A(s)`.  Again
`t=B(A(s))` is a `WIN` child of `ell`.  The side relation at `s` says that
`t` is a child of `z`.  When `C(s)=B`, it is `B(z)`, giving the second row.
When `C(s)=A`, it is `A(z)`.  Since `z` is `DRAW` and its `A`-child is
`WIN`, its `B`-child must be `DRAW`; thus `k>=2`, and Section 10 gives the
strict numerical decrease in the third row.

Now suppose `k=0`, so `z=B(A(q))` is `WIN` and `A(q)` is the next base draw.
If `q`, `A(q)`, and `s=B(q)` are all nonexceptional, then the following
skeleton step is forced to have `k=0` as well, and

\[
\boxed{
h(B(A^2(q)))\le h(B(q))-2.
}
\]

Indeed, `z=C(q)(s)` is the `WIN` child of the winning position `s`; the
other child `ell` of `s` is `LOSS`.  As in both cases above,
`t=B(A(s))` is simultaneously a child of `ell` and a child of `z`, so it is
`WIN` and has height at most `h(s)-2`.  The side relation at `A(q)` makes
`B(A^2(q))` a child of `z`.  It cannot be `LOSS`, because its parent
`A^2(q)` is `DRAW`.  Since `t` is already the unique `WIN` child of the
winning position `z`, the two values coincide.  Therefore `A^2(q)` is the
next base draw and the displayed height decrease follows.

Thus an ordinary skeleton has only two escape mechanisms from a strict
certificate-height decrease: it must enter an exceptional class among
`q,A(q),B(q)`, or take the last row of the table, which strictly decreases
the integer.  These two different decreases are not yet a single
well-founded rank, because one component can increase when the other drops.
