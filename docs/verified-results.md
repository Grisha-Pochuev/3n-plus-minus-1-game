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

## 3. The two descent blocks do not give a termination strategy

The previously claimed consequence that one chosen player can force finite
termination by always choosing `D` is false.  There is an exact two-ply
counterexample.  Suppose the state immediately after that player's move is
`5`.  The opponent chooses the increasing move and the chosen player answers
with the decreasing move:

\[
5\xrightarrow{U}7\xrightarrow{D}5.
\]

Repeating these choices gives infinite play even though the designated player
uses `D` on every turn.  In particular,

\[
D(U(5))=5.
\]

The gap in the old argument was a phase mismatch.  The valid inequality
`D(U(D(n)))<n` starts before the designated player's first `D` move.  After
their next `D` move it leaves the opponent, not the designated player, to
move from the smaller value.  It therefore cannot be iterated as a decrease
between equal turn phases.  Sections 4 onward do not use this false
consequence.

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

The four exceptional classes also have exact formulas.  For `t>=0`,

\[
\begin{array}{c|c|c}
q&B(q)&B(A(q))\\ \hline
16t+1  &R(6t)   &18t+1\\
16t+3  &R(6t+1) &18t+4\\
16t+12 &R(6t+4) &18t+13\\
16t+14 &R(6t+5) &18t+16.
\end{array}
\]

For example,

\[
A(16t+1)=4(6t)+2.
\]

The appended word is `10`, and because `6t` is even the alternating suffix
continues into that prefix; hence its deletion leaves `R(6t)`.  On the other
hand

\[
A^2(16t+1)=36t+3=2(18t+1)+1,
\]

whose final `1` repeats the odd last bit of `18t+1`, so deletion leaves
`18t+1`.  The other three rows follow identically from

\[
\begin{array}{c|c|c}
q&A(q)&A^2(q)\\ \hline
16t+3  &4(6t+1)+1&36t+8=2(18t+4),\\
16t+12 &4(6t+4)+2&36t+27=2(18t+13)+1,\\
16t+14 &4(6t+5)+1&36t+32=2(18t+16).
\end{array}
\]

In the even entries of the last column the final two bits are `00`, and in
the odd entries they are `11`, so in every case the final suffix deletion
has length one.  The formulas are implemented by
`exceptional_side_branch_values` and regression-tested directly.

There is a uniform version that retains the whole suffix length.  Put

\[
x=A(q)=2^k r+a,
\qquad r=B(q),
\]

where `k>=3` is the alternating-suffix length and `a` is that suffix.  First
suppose `r>0`, and let `e=r mod 2`, the leading bit of `a`.  Then

\[
A(x)=2^k A(r)+c_{k,e},
\]

where

\[
c_{k,e}=
\begin{cases}
2^{k-1},&e\equiv k\pmod2,\\
2^{k-1}-1,&e\not\equiv k\pmod2.
\end{cases}
\]

Indeed, for a leading-zero alternating word
`a=floor(2^k/3)`, while for a leading-one word
`a=floor(2^(k+1)/3)`.  Substitution in
`A(x)=ceil(3x/2)` gives exactly the two displayed values of `c`.
In `k` binary positions these are respectively

```text
100...0    and    011...1.
```

For `k>=3` the last two bits repeat, so the maximal alternating suffix of
`A(x)` has length exactly one.  Consequently

\[
\boxed{
B(A(q))=
2^{k-1}A(r)+
\begin{cases}
2^{k-2},&e\equiv k\pmod2,\\
2^{k-2}-1,&e\not\equiv k\pmod2.
\end{cases}
}
\]

This is implemented by `long_side_branch_value`.  It replaces the four
exceptional residue classes by a finite phase plus the unbounded counter
`k`; controlling that counter together with proof height is the remaining
rank problem.

If `r=0`, the whole word `x` is alternating and has leading bit one.  Directly

\[
A(x)=
\begin{cases}
2^k,&k\text{ odd},\\
2^k-1,&k\text{ even}.
\end{cases}
\]

Its maximal alternating suffix still has length one for `k>=3`, so the
corresponding complete-word case is

\[
\boxed{
B(A(q))=
\begin{cases}
2^{k-1},&k\text{ odd},\\
2^{k-1}-1,&k\text{ even}.
\end{cases}
}
\]

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

## 12. Minimum-height DRAW/WIN boundaries touch an exception

There is a stronger formulation that removes the numerical escape in the
last row of Section 11.  Call an edge from a `DRAW` parent to a `WIN` child a
**boundary edge**.  A nonempty draw set has at least one: the `B`-edge from
its smallest element.  Hence the set of proof heights of the `WIN` endpoints
of boundary edges has a minimum.

Let `q` be `DRAW`, let one child `s` be `WIN`, and let the other child `t` be
`DRAW`.  (The latter is forced: a draw has no losing child and must have a
draw child.)  If all three of

\[
q,\qquad s,\qquad t
\]

are nonexceptional, then there is another boundary edge, with `WIN` endpoint
`u`, such that

\[
\boxed{h(u)\le h(s)-2.}
\]

This contradicts minimum height.  Consequently, in every hypothetical
nonempty draw set, every boundary edge whose `WIN` endpoint has globally
minimum proof height has an exceptional vertex among its parent and its two
children.

### Proof when the WIN child is B(q)

Suppose `s=B(q)` and `t=A(q)`.  Put

\[
z=B(t)=B(A(q)).
\]

The side relation at `q` makes `z` a child of `s`; it is also a child of the
draw `t`, so it is not `LOSS`.  The other child `ell` of the winning `s` is
therefore `LOSS`.

Now put

\[
u=B(A(s)).
\]

The side relation at `s` makes `u` simultaneously a child of `z` and a child
of `ell`: if `z=A(s)` this is direct on the first side and supplied by the
side relation on the second, while if `z=B(s)` the roles are reversed.
Thus `u` is `WIN` and

\[
h(u)\le h(s)-2.
\]

If `z` is `DRAW`, the edge `z -> u` is the required lower boundary.  If `z`
is `WIN`, then its draw parent `t`, whose `B`-child is `z`, must have
`v=A(t)` as its draw child.  The value `B(A(t))` is a non-losing child of
`v`; by the side relation at `t` it is also a child of `z`.  But `z` already
has the `WIN` child `u`, so its other child is `LOSS`.  Hence
`B(A(t))=u`, and `v -> u` is the required boundary.

### Proof when the WIN child is A(q)

Suppose `s=A(q)` and `t=B(q)`.  Again put

\[
z=B(s)=B(A(q)).
\]

The side relation at `q` makes `z` a child of the draw `t`, so it is
non-losing.  It is the `B`-child of the winning `s`; consequently
`ell=A(s)` is `LOSS`.  Set

\[
u=B(A(s)).
\]

Then `u` is a `WIN` child of `ell`, has height at most `h(s)-2`, and the side
relation at `s` also makes it a child of `z`.

If `z` is `DRAW`, the edge `z -> u` is the lower boundary.  If `z` is
`WIN`, its other sibling under the draw parent `t` is a draw `v`.  When
`z=B(t)`, one has `v=A(t)`; the non-losing child `B(v)=B(A(t))` is also a
child of `z` by the side relation at `t`, so it must equal the unique
non-losing child `u` of `z`.  When `z=A(t)`, one has `v=B(t)`; now
`B(A(t))=B(z)` is also a child of `v`.  It cannot be the losing child of
`z`, hence again equals `u`.  In both cases `v -> u` is the desired lower
boundary.

This reduction is purely game-theoretic plus the ordinary side diamonds.  It
leaves only boundary triples meeting the four explicit exceptional classes
from Section 5; no tradeoff between integer size and proof height remains in
the ordinary region.

## 13. Boundary WINs of height one

The smallest possible positive `WIN` proof height is one.  Such positions
have a complete arithmetic characterization:

\[
\boxed{h(s)=1\quad\Longleftrightarrow\quad B(s)=0.}
\]

Indeed, height one means that `s` has a `LOSS` child of height zero.  The
only such position is the terminal `0`, and only the contracting child can
equal zero.  Conversely, moving to `0` is an immediate height-one winning
certificate.

Every height-one `WIN` is exceptional:

\[
\boxed{B(s)=0\quad\Longrightarrow\quad
s\equiv1,3,12,14\pmod {16}.}
\]

Put `x=A(s)`.  The equality `R(x)=0` says that the whole binary word for `x`
is alternating.  Apart from the one-bit word `1`, which is not in the image
of `A`, such a word is congruent to `2` or `5 mod 8`: an even-length word
ends in `010`, with the two-bit word `10` included, and an odd-length word
ends in `101`.  The residue table for `A(s) mod 8` in Section 5 gives
precisely `s=1,12 mod 16` in the first case and `s=3,14 mod 16` in the
second.

There is also a useful closure identity:

\[
\boxed{B(A(q))=0\quad\Longrightarrow\quad B(B(q))=0.}
\]

If `q` is nonexceptional, its side relation says that `B(A(q))` is either
`A(B(q))` or `B(B(q))`.  In the first case equality to zero forces
`B(q)=0`, and hence also `B(B(q))=0`; the second case is immediate.  If `q`
is exceptional, the explicit formulas in Section 5 show that `B(A(q))` is
one of

\[
18t+1,quad18t+4,quad18t+13,quad18t+16,
\]

and is never zero, so the implication is vacuous.

Consequently, a height-one `WIN` can never be the `A`-child of a draw.  If
`A(q)` has height one, then `B(A(q))=0`, so `B(B(q))=0`.  Moreover `B(q)>0`:
otherwise `q` itself would be a height-one exceptional position, whose
explicit exceptional formula makes `B(A(q))>0`.  Thus both children `A(q)`
and `B(q)` are height-one `WIN` positions, and

\[
\boxed{q\text{ is LOSS}.}
\]

Therefore a hypothetical minimum-height boundary with height one must point
through its `B`-edge.  Its remaining unresolved form is

\[
q\text{ DRAW},\qquad B(q)=s\text{ WIN with }B(s)=0,
\qquad A(q)\text{ DRAW}.
\]

The exact predecessor parameterization in Section 6 describes all such
arithmetic candidates.  Excluding this last family, and its higher-height
exceptional analogue, remains necessary for the full theorem.

## 14. A closed recurrence for dyadic-minus-one families

Long exceptional returns naturally produce numbers with a long final block
of one bits.  They admit a finite exact reduction.  For positive odd `a` and
`r>=0`, put

\[
X_r(a)=a2^r-1.
\]

For every `r>=3`, both game children stay in this family:

\[
\boxed{
A(X_r(a))=X_{r-1}(3a),\qquad
B(X_r(a))=X_{r-2}(3a).
}
\]

Indeed, `X_r(a)` is odd and hence

\[
A(X_r(a))=3a2^{r-1}-1=X_{r-1}(3a).
\]

When `r>=3`, this last number ends in at least two consecutive one bits.
Its maximal alternating suffix therefore consists of its final bit alone,
and deleting that bit gives `X_{r-2}(3a)`.

Thus every play starting at `X_r(a)` reaches one of the boundary exponents
`0,1,2` after at most `r` moves.  This statement is only an arithmetic
reduction: the coefficient is multiplied by three at every step, so it does
not by itself provide a decreasing numerical rank.

The two positive boundary exponents share their contracting child.  More
precisely,

\[
\begin{aligned}
A(X_1(a))&=X_0(3a),&
B(X_1(a))&=R(3a-1),\\
A(X_2(a))&=X_1(3a),&
B(X_2(a))&=R(3a-1).
\end{aligned}
\]

For the nontrivial equality, set `y=3a-1`.  The number `y` is positive and
even, while `6a-1=2y+1`.  Appending the bit `1` to a binary word ending in
`0` extends its maximal alternating suffix by exactly one bit.  Deleting the
extended suffix from `2y+1` therefore leaves exactly the same prefix as
deleting the suffix from `y`:

\[
R(6a-1)=R(3a-1).
\]

At exponent zero there is also an exact, but non-descending, coefficient
map.  Write

\[
c=\frac{3a-1}{2}=2^j b
\]

with `b` odd.  Then

\[
A(X_0(a))=X_j(b),\qquad B(X_0(a))=R(X_j(b)).
\]

For `j>=2`, the second value simplifies to `X_{j-1}(b)`.  For `j=0,1`,
the longer alternating suffix remains the unresolved boundary operation.
The coefficient map `a -> oddpart(3a-1)` contains the familiar `5 <-> 7`
cycle, so ignoring the game-theoretic outcome obligations cannot yield a
well-founded rank here.

### Symmetric constant-tail normal form

The preceding recurrence is not restricted to one bits.  For
`epsilon in {0,1}` define

\[
Q_r^\epsilon(a)=a2^r-\epsilon.
\]

For `r>=1`, this is a word with a constant final run of `r` copies of
`epsilon`; because `a` is odd, the bit immediately before that run is the
opposite bit whenever it exists.  Every positive integer has exactly one
such representation when `r` is chosen maximal.

For either value of `epsilon` and every `r>=3`,

\[
\boxed{
A(Q_r^\epsilon(a))=Q_{r-1}^\epsilon(3a),\qquad
B(Q_r^\epsilon(a))=Q_{r-2}^\epsilon(3a).
}
\]

The proof for `epsilon=1` is the one above.  For `epsilon=0`, the expanding
child ends in at least two zero bits, so its maximal alternating suffix is
again its final bit alone.

The shared-child identity at the boundary is symmetric as well:

\[
B(Q_1^\epsilon(a))=B(Q_2^\epsilon(a)).
\]

To close the expanding transition at `r=1`, factor

\[
3a+1-2\epsilon=2^j b
\]

with `b` odd.  Since the left side is even, `j>=1`, and direct substitution
gives the exact phase switch

\[
\boxed{
A(Q_1^\epsilon(a))=Q_j^{1-\epsilon}(b).
}
\]

Consequently, the constant-tail coordinates give a closed arithmetic
description of every expanding transition.  Long runs have the finite
Fibonacci-like reduction above; all unbounded difficulty is transferred to
the signed coefficient maps `oddpart(3a+1)` and `oddpart(3a-1)` at `r=1`,
together with the common contracting child of the `r=1,2` pair.

## 15. Coefficient descent at the constant-tail boundary

Every positive `q` has unique canonical constant-tail coordinates

\[
q=Q_r^\epsilon(a)=a2^r-\epsilon,
\qquad a\text{ odd},\quad r\ge1,\quad \epsilon\in\{0,1\},
\]

where `epsilon` is the last bit and `r` is the length of the maximal constant
binary suffix.  Write `kappa(q)=a` for its odd coefficient.  The function
`constant_tail_coordinates` computes this representation exactly.

Let `p` be the common contracting child of the two boundary states:

\[
p=B(Q_1^\epsilon(a))=B(Q_2^\epsilon(a))=R(3a-\epsilon).
\]

If `p>0`, then

\[
\boxed{\kappa(p)\le\frac{3a+1}{4}.}
\]

Indeed, `R` deletes at least one binary bit, so

\[
p\le\left\lfloor\frac{3a-\epsilon}{2}\right\rfloor.
\]

For every positive integer `y`, its constant-tail coefficient is at most
`(y+1)/2`: if `y` is even, at least one zero is removed, and if it is odd,
at least one factor of two is removed from `y+1`.  Combining the two bounds
gives the box.  In particular,

\[
\kappa(p)<a\qquad(a\ge3).
\]

For `a=1`, the only equality is `epsilon=0`, when `p=1`.  The corresponding
states `Q_1^0(1)=2` and `Q_2^0(1)=4` are both `LOSS`: `1` and `3` are `WIN`,
so `2` is `LOSS`; then `6` is `WIN` through its child `2`, and both children
of `4` are `WIN`.  For `epsilon=1`, the `r=1` state is terminal and the
common child is zero.

There is a second descent at the expanding boundary.  Factor

\[
3a+1-2\epsilon=2^j b,
\qquad b\text{ odd}.
\]

If `j>=2` and `a>=3`, then

\[
b\le\frac{3a+1}{4}<a.
\]

The only equality at `a=1` is again the already resolved state `2`.

These inequalities have a game-theoretic consequence.  Suppose a DRAW set
exists and choose a DRAW whose canonical coefficient `a` is minimum among
all DRAW positions.

- If its exponent is `r=1` or `r=2`, its common `B`-child has smaller
  coefficient (or is terminal), hence is not DRAW.  A child of a DRAW cannot
  be LOSS, so this common child is WIN.
- At `r=1`, the expanding child must therefore be DRAW.  Its coefficient
  cannot be smaller than `a`; the preceding bound forces
  `v2(3a+1-2epsilon)=1`.
- At `r=2`, the expanding child `Q_1^epsilon(3a)` must be DRAW.

Thus a minimum-coefficient DRAW can cross the signed `r=1` boundary only
through the valuation-one branch.  This is a genuine narrowing of a
hypothetical draw kernel, but not yet a contradiction: the valuation-one
map increases the coefficient for every nonterminal case, and a DRAW with a
larger coefficient can later use its contracting child without violating
global minimality.

## 16. A second boundary fork and division by three

The first forced valuation-one transition in Section 15 can be continued one
step exactly.  Put

\[
s=1-2\epsilon\in\{1,-1\},
\qquad v_2(3a+s)=1,
\qquad b=\frac{3a+s}{2}.
\]

Thus a minimum-coefficient DRAW `Q_1^epsilon(a)` has the DRAW child
`Q_1^(1-epsilon)(b)`.  Now factor

\[
9a+s=2^v d,
\qquad d\text{ odd}.
\]

The initial valuation-one condition implies `v>=2`.  Direct use of the
boundary formula gives

\[
A(Q_1^{1-\epsilon}(b))=Q_{v-1}^{\epsilon}(d).
\]

When `v>=3`, its other child is the adjacent state

\[
B(Q_1^{1-\epsilon}(b))=Q_{v-2}^{\epsilon}(d).
\]

Indeed, the expanding child ends in at least two equal `epsilon` bits, so
`R` deletes only the final bit.  When `v=2`, the two final bits alternate
instead, and direct deletion gives a contracting child whose canonical
coefficient is strictly below `a` (the case `a=1` is already terminal or
resolved).

This yields the following exact trichotomy for a minimum-coefficient DRAW at
exponent one.

1. If `v=2`, its second state has a smaller-coefficient WIN child and is
   forced to the DRAW state
   `Q_1^epsilon((9a+s)/4)`.
2. If `v=3`, its two children are the adjacent pair
   `Q_2^epsilon(d),Q_1^epsilon(d)`, where `d=(9a+s)/8`; at least one is DRAW.
   Their common `B`-child has coefficient below `a` and is therefore WIN.
3. If `v>=4`, both children have coefficient
   `d< a`, so neither can be DRAW, contradicting that their parent is DRAW.

For the last inequality,

\[
d\le\frac{9a+1}{16}<a
\]

for every relevant `a>=3`.  In the middle case, Section 15 gives

\[
\kappa(B(Q_1^\epsilon(d)))
\le\frac{3d+1}{4}<a.
\]

Hence one quarter of the valuation-one residue classes are eliminated at
this second step, and another quarter collapse to an exact adjacent-pair
obstruction.  This remains a conditional reduction, not a proof that the
pair cannot contain a DRAW.

There is also a useful reverse descent for coefficients divisible by three.
Let `c` be odd, `a=3c`, and `r>=2`.  If

\[
Q_r^\epsilon(a)\text{ is DRAW},
\]

then at least one of

\[
Q_{r+1}^\epsilon(c),\qquad Q_{r+2}^\epsilon(c)
\]

is DRAW.

Both displayed states have the original DRAW as one child.  They therefore
cannot be LOSS.  Suppose that neither were DRAW.  Then both would be WIN,
and, because their shared DRAW child cannot be a winning witness, their
other children would both be LOSS.  For `r=2` those two LOSS siblings are
`Q_1^epsilon(a)` and `Q_3^epsilon(a)`; for `r>=3` they are
`Q_(r-1)^epsilon(a)` and `Q_(r+1)^epsilon(a)`.  The constant-tail identities
show that every child of `Q_r^epsilon(a)` is a child of one of these two LOSS
siblings.  Both children of the alleged DRAW would therefore be WIN, making
it LOSS, a contradiction.

Repeatedly applying this lemma removes all factors of three from the
coefficient of a DRAW at exponent at least two.  In particular, if `a` is
the globally minimum DRAW coefficient and `3` divides `a`, then every DRAW
with that coefficient must have exponent exactly one.  The exponent-one
case is not covered by the reverse frame and remains open.

## 17. Every three-free coefficient contains a copy of the game

Define the increasing embedding

\[
J(s)=2A(s)+1.
\]

This is exactly the original odd state represented by the transformed state
`s`.  Consequently its two original children are

\[
\boxed{J(A(s)),\qquad J(B(s)).}
\]

This follows either from the conjugacy in `docs/normal-form.md` or by direct
substitution.  It is regression-tested by `embedded_original_state`.

Every positive odd constant-tail coefficient has a unique representation

\[
\boxed{a=3^kJ(s)},
\qquad k\ge0,quad s\ge0.
\]

To prove existence, remove all factors of three from `a`, leaving an odd
integer `c` not divisible by three.  Then `(c-1)/2` is `0` or `2 mod 3`, so
it lies in the image of `A=F`; its unique inverse is `s`, and `c=J(s)`.
Uniqueness follows from unique factorization and injectivity of `A`.  The
function `constant_tail_coefficient_source` returns `(s,k)`.  We call `s`
the **source** of the coefficient.

At the signed `r=1` boundary of a three-free coefficient, the apparent
coefficient map is literally one move of the embedded game.  For `s>0`,

\[
\operatorname{oddpart}(3J(s)+1-2\epsilon)
\in\{J(A(s)),J(B(s))\}.
\]

The phase selecting `A(s)` is

\[
\boxed{\alpha(s)=1-\left(\left\lfloor s/2\right\rfloor\bmod2\right).}
\]

For `epsilon=alpha(s)` the valuation is exactly one and the source child is
`A(s)`.  The other phase has valuation at least two and selects `B(s)`.
Indeed, `J(A(s))>J(s)>J(B(s))`; in the original game the increasing move
removes exactly one factor of two, while the decreasing move removes at
least two.  The sign of the increasing move is determined by `s mod 4`,
which gives the displayed formula for `alpha`.  The function
`source_boundary_transition` checks the exact identity, not merely the
inequalities.

This gives another conditional reduction for a hypothetical draw kernel.
Choose a DRAW whose coefficient source `s` is globally minimum.  If a state

\[
Q_1^\epsilon(J(s))
\]

is DRAW, its common `B`-child has coefficient below `J(s)` by Section 15,
hence has source below `s`.  It cannot be DRAW and, as a child of a DRAW,
cannot be LOSS; it is WIN.  The expanding child must therefore be DRAW.  It
cannot select `B(s)`, whose source is smaller, so necessarily

\[
\boxed{
\epsilon=\alpha(s),\qquad
Q_1^{1-\epsilon}(J(A(s)))\text{ is DRAW}.
}

Likewise, if `Q_2^epsilon(J(s))` is DRAW, its common child is WIN and
`Q_1^epsilon(3J(s))` is DRAW.  At every exponent `r>=3`, both children have
the same source as their parent because the coefficient is merely multiplied
by three.  Finally, Section 16 implies that any DRAW with exponent at least
two and coefficient `3^kJ(s)` can be pulled back repeatedly to a DRAW with
coefficient `J(s)` and a larger exponent.

Thus multiplication by three in the long-tail recurrence is no longer an
uncontrolled numerical growth: it preserves the exact source state.  The
remaining non-well-founded transition is concentrated at exponent one with
`k>0`, where

\[
3^{k+1}J(s)\mathbin{\pm}1=2^jJ(t)
\]

can increase the source `t`.  Controlling this source/valuation exchange,
together with the adjacent pair from Section 16, is still required for a
complete proof.

## 18. The lifted side branch returns to the ordinary source diamond

Write `kappa(q)` for the odd coefficient in the canonical constant-tail
coordinates of a positive state, and retain

\[
J(s)=2A(s)+1.
\]

Two elementary identities explain the next level of the source embedding.
For every positive odd `w`,

\[
\boxed{
\kappa(3w)=J(R(w)),\qquad
\kappa(3w-1)=J(R(2w-1)).
}
\]

For the first identity, write

\[
w=2^m z+a,\qquad z=R(w),
\]

where `a` is the maximal alternating suffix.  It ends in one, and, when
`z>0`, its leading bit is `z mod 2`.  Hence

\[
3a+1=
\begin{cases}
2^m,&z\text{ even},\\
2^{m+1},&z\text{ odd}.
\end{cases}
\]

Since `J(z)=3z+1+(z mod 2)`, substitution gives

\[
3w=J(z)2^m-1.
\]

If the whole word is alternating, then `z=0` and the exponent is `m+1`
instead; the coefficient is still `J(0)=1`.  This proves the first identity.

For the second, put `y=2w-1`.  Except for the immediate case `w=1`, the
odd word `y` ends in `01`, so its alternating-suffix length `m` is at least
two.  Applying the same calculation to

\[
A(y)=\frac{3y+1}{2}=3w-1
\]

gives

\[
A(y)=J(R(y))2^{m-1}
\]

when a prefix remains.  In the complete-word case only the exponent changes.
Thus the second canonical coefficient is `J(R(y))`, as claimed.  Both
identities are regression-tested for odd `w<10000`.

Now define the exponent-one **source lift**

\[
L_e(s)=Q_1^e(J(s)).
\]

Let `alpha(s)` be the `A`-selecting phase from Section 17, and put

\[
u=A(s),\qquad f=1-\alpha(s),\qquad
p=B(L_f(u)),\qquad z=B(u)=B(A(s)).
\]

The first source transition is exactly

\[
A(L_{\alpha(s)}(s))=L_f(u).
\]

The side child `p` has the following exact source:

\[
\boxed{
s\not\equiv1,3,12,14\pmod {16}
\quad\Longrightarrow\quad
\operatorname{source}(p)=z,
\quad 3\nmid\kappa(p).
}
\]

If `f` is the `B`-selecting phase at `u`, Section 17 gives

\[
A(L_f(u))=Q_j^{1-f}(J(B(u))),\qquad j\ge2.
\]

The last two bits are then equal, so applying `R` merely lowers `j` by one;
the side child has source `B(u)=z`.

It remains to consider when `f` is the `A`-selecting phase at `u`.  Outside
the four exceptional residues this happens only in the following four rows.
Directly deleting the displayed fixed two-bit alternating suffix reduces the
claim to one of the two boxed identities above:

\[
\begin{array}{c|c|c|c}
u & p & w & B(u)\\ \hline
16t+1  &3(12t+1)       &12t+1  &R(w)\\
16t+6  &3(12t+5)-1     &12t+5  &R(2w-1)\\
16t+9  &3(12t+7)       &12t+7  &R(w)\\
16t+14 &3(12t+11)-1    &12t+11 &R(2w-1).
\end{array}
\]

For example, in the first row
`A(L_1(16t+1))=144t+14`, whose maximal alternating suffix is the final
`10`, leaving `p=36t+3`.  The other three rows have exactly the same fixed
two-bit deletion.  The coefficient identities therefore give
`kappa(p)=J(B(u))` in all four rows.

The exceptional source residues do strictly better:

\[
\boxed{
s\equiv1,3,12,14\pmod {16},\ p>0
\quad\Longrightarrow\quad
\operatorname{source}(p)<s.
}
\]

Indeed, for `s=16t+c` the four arguments from which `p` is obtained by `R`
are respectively

\[
216t+21,\quad216t+50,\quad216t+165,\quad216t+194.
\]

Their final three bits are `101`, `010`, `101`, `010`, so `R` deletes at
least three bits.  Hence `p` is at most one eighth of the corresponding
argument.  If `x` is the source of `p`, then

\[
3x+1\le J(x)\le\kappa(p)\le\frac{p+1}{2},
\]

which gives `x<(216t+d)/48<16t+c` in each of the four rows.  This proves the
strict source drop.  The possible terminal value `p=0` is handled separately.

There is a useful conditional consequence.  Suppose a DRAW exists and `s`
is the globally least coefficient source of any DRAW.  If

\[
L_{\alpha(s)}(s)
\]

is DRAW, Section 17 forces its `A`-child `L_f(A(s))` to be DRAW.  Its side
child `p` is non-losing.  Therefore:

- at an exceptional `s`, `p=0` is immediately impossible, while a positive
  `p` has smaller source and is consequently WIN;
- at a nonexceptional `s` with `B(A(s))<s`, the same argument makes `p` WIN;
- the only source-level escape is a DRAW side child whose source is exactly
  `B(A(s))>=s`.

Thus two lifted boundary steps reproduce the ordinary side return
`s -> B(A(s))`; the four old exceptional classes now cause a strict source
drop rather than an uncontrolled affine jump.  This does not yet rule out an
infinite sequence of nondecreasing ordinary side returns.  The forced LOSS
siblings or the minimum boundary proof height must still be retained to close
that last case.

## 19. The exact nondecreasing return and its phase-mismatch fork

The source-level escape left by Section 18 has only four residue classes.
For every positive nonexceptional `s`, put

\[
b=B(s),\qquad z=B(A(s)).
\]

Then

\[
\boxed{
z\ge s
\quad\Longleftrightarrow\quad
s\equiv0,5,10,15\pmod {16}.
}
\]

In fact the four cases have the exact affine form

\[
\begin{array}{c|c|c}
s&b&z\\ \hline
16t   &12t   &18t\quad(t\ge1),\\
16t+5 &12t+4 &18t+6,\\
16t+10&12t+7 &18t+11,\\
16t+15&12t+11&18t+17.
\end{array}
\]

To prove the classification, let `m` be the alternating-suffix length of
`A(s)`.  Outside the exceptional classes, `m` is one or two.  If `m=2`,
then `A(s)=4b+a` with `a` equal to one or two.  Section 5 gives
`z` as either `A(b)` or `B(b)`, and therefore

\[
z\le A(b)\le\frac{3b+1}{2}
\le\frac{3A(s)+1}{8}
\le\frac{9s+5}{16}<s.
\]

If `m=1`, then `A(s)=2b+(b\bmod2)`.  The refined side-branch table in
Section 5 says that `z=A(b)` exactly when `b mod 4` is zero or three;
otherwise `z=B(b)<s`.  Since a value is in the image of `A` exactly when it
is not `1 mod 3`, the `A(b)` cases have

\[
b\equiv0,4,7,11\pmod {12}.
\]

Substitution and inversion of `A` give precisely the four rows above.  Each
displayed `z` is strictly larger than the corresponding positive `s`.

The lifted geometry in these rows is also exact.  Let

\[
e=\alpha(s),\quad q_0=L_e(s),\quad q_1=A(q_0),\quad
p=B(q_1),\quad h=A(q_1).
\]

For the four nondecreasing classes, `u=A(s)` is `0` or `7 mod 8`.
Consequently `1-e` is the `B`-selecting phase at `u`, and its signed
valuation is exactly two.  The two children of `q_1` are therefore

\[
\boxed{
p=Q_1^e(J(z))=L_e(z),\qquad
h=Q_2^e(J(z)).
}
\]

The phase at the returned source either agrees with `e` or flips, according
to one more binary bit:

\[
\begin{array}{c|c}
e=\alpha(z)&s\equiv0,10,21,31\pmod {32},\\
e\ne\alpha(z)&s\equiv5,15,16,26\pmod {32}.
\end{array}
\]

This follows immediately from the four affine rows by separating even and
odd `t`.

The phase-mismatch rows retain enough outcome information to force another
DRAW.  Suppose `s` is the globally least coefficient source of any DRAW and
`q_0=L_{\alpha(s)}(s)` is DRAW.  In a mismatch row, Section 17 and the
identities above force

\[
\boxed{
q_1\text{ is DRAW},\quad p\text{ is WIN},\quad h\text{ is DRAW}.
}
\]

Indeed, `p=L_e(z)` is now in the `B`-selecting phase at `z`.  Both its
children have source `B(z)`.  The general bound for `B`, together with
`z\le(9s+3)/8`, gives

\[
B(z)\le\frac{3z+1}{4}
\le\frac{27s+17}{32}<s,
\]

where every mismatch row has `s>=5`.  Thus neither child of `p` is DRAW.
Since a child of a DRAW cannot be LOSS, `p` is WIN, and the other child `h`
of `q_1` must be DRAW.

There is a sharper forced fingerprint.  The exponent-one and exponent-two
states `p` and `h` share their `B`-child.  Denote it by `c`, and put
`d=A(p)`.  Both `c` and `d` have source `B(z)<s`.  Since `h` is DRAW, `c`
cannot be LOSS; hence `c` is WIN.  Since `p` is WIN, its remaining child is
then LOSS.  Finally the remaining child of `h` must be DRAW:

\[
\boxed{
d=A(p)\text{ is LOSS},\quad
c=B(p)=B(h)\text{ is WIN},\quad
k=A(h)=Q_1^e(3J(z))\text{ is DRAW}.
}
\]

The expanding child of this last factor-three state has another exact source
formula.  Write `delta=1-2e`.  Because `e` is the `B`-selecting phase at
`z`,

\[
3J(z)+\delta\equiv0\pmod4.
\]

As `9` is one modulo four, this implies

\[
9J(z)+\delta\equiv2\pmod4,
\]

so its valuation is exactly one.  Moreover `e` is the parity of `A(z)` in
the mismatch rows.  A direct parity split therefore gives

\[
\frac{9J(z)+\delta}{2}=J(3A(z)+1).
\]

With `t=3A(z)+1`, the exact arithmetic transition is

\[
\boxed{
A(k)=Q_1^{1-e}(J(t))=L_{\alpha(z)}(t).
}
\]

This last identity does not by itself say that `A(k)` is DRAW: the other
child of the proved-DRAW state `k` can still carry the DRAW continuation.
Controlling that competing child, and the phase-match rows above, is the
remaining source-level obstruction.

## 20. A larger diamond excludes every phase mismatch

The competing child left open at the end of Section 19 closes the outcome
fingerprint into a contradiction.  Retain a phase-mismatch row and write

\[
a=J(z),\qquad g=1-e,qquad w=B(z).
\]

Because `e` is the `B`-selecting phase at `z`, there is a `j>=2` such that

\[
3a+1-2e=2^jJ(w).
\]

Put `b=J(w)`.  The four states in the fingerprint of Section 19 are

\[
\begin{aligned}
p&=Q_1^e(a),& h&=Q_2^e(a),\\
d=A(p)&=Q_j^g(b),& c=B(p)&=Q_{j-1}^g(b),\\
k=A(h)&=Q_1^e(3a).&&
\end{aligned}
\]

The adjacent states `d` and `c` have exactly one common child.  Let `x` be
that child and let `y` be the other child of `c`.  Then the following exact
large-diamond identity holds:

\[
\boxed{B(k)=y.}
\]

Here is a complete proof.  First note that

\[
A(k)=9a-e.
\]

For `j=2`, the states `Q_2^g(b)` and `Q_1^g(b)` share their `B`-child, so
`y=A(c)`.  If `e=0`, then `y=3b-1` and

\[
A(k)=4y+1;
\]

the appended word is `01`, and its leading zero repeats the final zero of
`y`.  If `e=1`, then `y=3b` and

\[
A(k)=4y+2;
\]

the same statement holds with the word `10` and a repeated one.  Thus in
both cases deleting the maximal alternating suffix leaves `y`.

For `j=3`, the common child is `Q_1^g(3b)` and

\[
y=R(3b-g).
\]

When `e=0`, one has `A(k)=8(3b-1)+5`; the appended word `101` continues
the alternating suffix of the even number `3b-1`.  When `e=1`, one has
`A(k)=8(3b)+2`; now `010` continues the alternating suffix of the odd
number `3b`.  Hence `R(A(k))=R(3b-g)=y`.

Finally suppose `j>=4`.  The long-tail recurrence gives

\[
x=Q_{j-2}^g(3b),\qquad y=Q_{j-3}^g(3b).
\]

For `e=0`, `A(k)=8y+5`; the word `101` begins with the same one bit on
which `y` ends.  For `e=1`, `A(k)=8y+2`; the word `010` begins with the
same zero bit on which `y` ends.  In either case the maximal alternating
suffix is exactly the appended three-bit word, proving `B(k)=y`.

Now impose the minimum-source DRAW hypothesis of Section 19.  It proved

\[
d\text{ LOSS},\qquad c\text{ WIN},\qquad k\text{ DRAW}.
\]

Every child of the LOSS state `d` is WIN, so their common child `x` is WIN.
The WIN state `c` must have a LOSS child; since `x` is WIN, its other child
`y` is LOSS.  But the large-diamond identity makes this same `y` a child of
the DRAW state `k`, which is impossible.  Therefore

\[
\boxed{
s\equiv5,15,16,26\pmod {32}
\quad\Longrightarrow\quad
L_{\alpha(s)}(s)\text{ cannot be a globally minimum-source DRAW lift}.
}
\]

Combining Sections 18--20, the only nondecreasing source returns still able
to carry such a DRAW lift are the phase-match classes

\[
\boxed{s\equiv0,10,21,31\pmod {32}.}
\]

In those classes `p=L_{\alpha(z)}(z)` has the same canonical form at the
larger returned source `z=B(A(s))`; it may itself be DRAW, so the LOSS/WIN
fingerprint used above is not yet forced.

## 21. Long returned suffixes exclude four phase-match subclasses

The phase-match gadget has two additional exact source identities.  Retain

\[
e=\alpha(s)=\alpha(z),\quad a=J(z),\quad
p=Q_1^e(a),\quad h=Q_2^e(a),
\]

and put

\[
d=A(p)=3a-e,qquad c=B(p)=B(h)=R(d),qquad
k=A(h)=Q_1^e(3a).
\]

First, although the integer `c` need not be smaller than `s`, its own
coefficient source always is.  If `rho` is the source of `c`, Section 15
gives

\[
3\rho+1\le J(\rho)\le\kappa(c)
\le\frac{3J(z)+1}{4}.
\]

Since `J(z)\le3z+2` and the four affine rows of Section 19 give
`z\le(9s+3)/8`, it follows that

\[
\rho\le\frac{3z+1}{4}
\le\frac{27s+17}{32}<s.
\]

Every phase-match source is at least ten, so the last inequality has no
small exception.

Second, the two children of `k` are adjacent constant-tail states whose
three-free coefficient is exactly `J(c)`.  More precisely, for some `r>=1`
and `g=1-e`,

\[
\boxed{
A(k)=Q_{r+1}^g(J(c)),\qquad
B(k)=Q_r^g(J(c)).
}
\]

To prove this, observe that `A(k)=9a-e`.  If `e=0`, then `d=3a` and the
first coefficient identity of Section 18 gives

\[
\kappa(A(k))=\kappa(9a)=J(R(3a))=J(c).
\]

If `e=1`, then `d=3a-1`.  The second coefficient identity, followed by the
shared-child identity, gives

\[
\kappa(A(k))=\kappa(9a-1)=J(R(6a-1))=J(R(3a-1))=J(c).
\]

The equality `e=alpha(z)` also says that `a` is `3 mod 4` when `e=0` and
`1 mod 4` when `e=1`.  Thus `9a-e` ends respectively in `11` or `00`; its
constant suffix has length at least two and tail bit `g`.  Applying `R`
removes just its last bit, proving the adjacent-pair formula.

It remains to compare the integer `c` itself with `s`.  In the four
phase-match classes write `s=32t+r`.  Direct substitution gives

\[
\begin{array}{c|c}
s&d=A(p)\\ \hline
32t    &324t+2\quad(t\ge1),\\
32t+10 &324t+105,\\
32t+21 &324t+218,\\
32t+31 &324t+321.
\end{array}
\]

The alternating suffix of `d` has length at least four exactly when its last
four bits are `0101` or `1010`.  Reducing the table modulo 16 gives

\[
\boxed{
\operatorname{altsuffixlen}(d)\ge4
\quad\Longleftrightarrow\quad
s\equiv21,63,64,106\pmod {128}.
}
\]

In these four classes, `c=R(d)\le d/16<s`.  In every other phase-match class
the suffix has length at most three, while the same table gives `d>8s+8`;
hence `c\ge\lfloor d/8\rfloor>s`.  Therefore the residue test is equivalently

\[
\boxed{c<s\quad\Longleftrightarrow\quad
s\equiv21,63,64,106\pmod {128}.}
\]

The four long-suffix classes are impossible under the globally
minimum-source DRAW hypothesis.  Indeed, `q_1` from Section 19 is DRAW and
has children `p,h`.  Their common child `c` has source below `s`; since at
least one of `p,h` is DRAW, `c` is non-losing, and minimality therefore makes
it WIN.

If `p` is WIN, then its other child `d` is LOSS, while `h` is DRAW and its
other child `k` is DRAW.  But both children of `k` have source `c<s` by the
adjacent-pair identity, so `k` cannot have a DRAW child, a contradiction.

If instead `p` is DRAW, its WIN child `c` forces `d` to be DRAW.  Let `m>=4`
be the alternating-suffix length of `d`, so `c=R(d)`.  The long-suffix
calculation of Section 5 can be rewritten as

\[
A(d)=Q_{m-1}^{\eta}(J(c)),\qquad
B(d)=Q_{m-2}^{\eta}(J(c))
\]

for the appropriate tail bit `eta`.  Both children again have source
`c<s`, contradicting that `d` is DRAW.  The two cases exhaust the
possibilities, and hence

\[
\boxed{
s\equiv21,63,64,106\pmod {128}
\quad\Longrightarrow\quad
L_{\alpha(s)}(s)
\text{ cannot be a globally minimum-source DRAW lift}.
}
\]

Together with Section 20, a surviving nondecreasing return must now be a
phase match outside these four long-suffix subclasses.  There the returned
integer `c` is larger than `s`, even though the coefficient source of `c`
is smaller; that split between the two orders is the remaining obstruction.

## 22. Every returned suffix of length at least three lowers boundary height

The phase-match gadget also carries the proof-height component that was
deliberately retained in Section 12.  Use the notation of Section 21 and
write

\[
q_0=L_e(s),\qquad q_1=A(q_0),\qquad z=B(A(s)).
\]

In every phase-match row there is an exact identity

\[
\boxed{B(q_0)=z.}
\]

It follows directly by writing `q_1=L_{1-e}(A(s))` and continuing the
alternating suffix through its final appended bit.  The coefficient source
of the integer `z` is below `s`.  Indeed, if `sigma(z)` denotes that source,
then

\[
3\sigma(z)+1\le\kappa(z)\le\frac{z+1}{2},
\]

while Section 19 gives `z\le(9s+3)/8`; hence `sigma(z)<s` for every relevant
`s>=10`.

Now retain

\[
p=B(q_1),\qquad h=A(q_1),\qquad
d=A(p),\qquad c=B(p)=B(h),
\]

and let `m` be the alternating-suffix length of `d`.  If `m>=3`, the
following larger diamond is exact:

\[
\boxed{
c\in\operatorname{moves}(A(z))
\quad\text{and}\quad
c\in\operatorname{moves}(B(z)).
}

For a direct arithmetic proof, put `u=A(z)`.  In a phase match, the parity
of `u` is `1-e`.  Since `p=4u+2-e`, direct substitution gives

\[
d=A(p)=
\begin{cases}
4A(u)+1,&e=0,\\
4A(u)+2,&e=1.
\end{cases}
\]

Thus `d` is obtained from `A^2(z)` by appending respectively `01` or `10`.
The condition `m>=3` says exactly that its alternating suffix continues
through the boundary into `A^2(z)`.  Therefore

\[
c=R(d)=R(A^2(z))=B(A(z)).
\]

In the eight residue classes where `m>=3`, direct reduction of the affine
rows modulo 16 gives `z=0,7,8,15 mod 16`.  Hence `z` is nonexceptional, and
the side relation of Section 5 makes this same `c=B(A(z))` a child of
`B(z)` as well.  This proves the boxed diamond.  The identity is also
regression-tested without assuming any outcomes.

There is a useful game-theoretic consequence.  Suppose again that `s` is
the globally least coefficient source of a DRAW and `q_0` is DRAW.  Its
child `z` has source below `s`; it is non-losing and cannot be DRAW, so it is
WIN.  Section 17 makes `q_1` DRAW.  At least one of its children `p,h` is
DRAW, and their common child `c` likewise has source below `s`; therefore
`c` is WIN and is the endpoint of another DRAW-to-WIN boundary.

Let `ell` be a LOSS child witnessing that `z` is WIN.  When `m>=3`, the
boxed diamond makes `c` a child of `ell` regardless of which child of `z`
is `ell`.  Consequently

\[
\boxed{h(c)\le h(z)-2.}
\]

Thus every phase-match gadget with returned suffix length at least three
replaces the current boundary by one with strictly smaller finite WIN proof
height.  Such replacements cannot occur infinitely often.  In particular,
after the outright exclusions of Sections 20--21, any indefinitely surviving
phase-match reduction must eventually enter the suffix-length-two rows

\[
s\equiv10,31,32,53,74,95,96,117\pmod {128}.
\]

This is a height descent, not yet a contradiction: the length-two diamond
contains only one of the two possible LOSS witnesses of `z`.  Closing that
remaining witness orientation is the next boundary problem.

## 23. Exact outcome normal form at returned suffix length two

The eight length-two classes left by Section 22 have a finite exact normal
form.  Keep all its notation.  Since the alternating suffix of

\[
d=A(p)
\]

has length exactly two, the two appended bits in the proof of Section 22 are
deleted and no more.  Hence

\[
\boxed{c=A^2(z).}
\]

Moreover the final two bits are `01` for `e=0` and `10` for `e=1`.  Thus
`c mod 2=e`, and direct substitution gives

\[
\boxed{v:=A(d)=L_e(c).}
\]

Put

\[
r:=B(d),
\]

and let `ell` be the other child of `c`.  The side relation at the
length-two diamond makes `r` one of the two ordinary children of `c`.  Its
coefficient source is below `s`.  One convenient bound is as follows.  The
canonical source `rho(r)` satisfies

\[
\rho(r)\le\frac{r-1}{6},
\]

while `r<=A(c)`, `c=A^2(z)`, and `z<=(9s+3)/8`.  Successive use of
`A(q)<=(3q+1)/2` gives

\[
\rho(r)\le\frac{243s+169}{384}<s.
\]

The eight residue rows split into two symmetric groups:

\[
\begin{array}{c|c|c|c}
s\bmod128&e=\alpha(c)?&r&\ell\\ \hline
10,32,95,117&\text{yes}&A(c)&B(c),\\
31,53,74,96&\text{no}&B(c)&A(c).
\end{array}
\]

Thus the phase `e` of `v=L_e(c)` always selects the ordinary child `r`,
while the opposite phase selects `ell`.  These identities are obtained by
substituting the eight residues modulo 128; no higher bits enter because all
suffix deletions used here have already stopped at length two.

Now impose the globally minimum-source DRAW hypothesis.  Sections 21--22
already make `c` WIN.  The two possible outcomes of `p` give a complete
forced fork.

If `p` is DRAW, then its other child `d` is DRAW.  Since `r` has source below
`s`, it is not DRAW; as a child of `d` it is not LOSS, so it is WIN.  Hence
the other child is forced DRAW:

\[
\boxed{p,d,v=L_e(c)\text{ are DRAW},\qquad r\text{ is WIN}.}
\]

If `p` is WIN, its other child `d` is LOSS because `c` is WIN.  The other
child `h` of `q_1` is DRAW, and its WIN child `c` forces
`k=A(h)` to be DRAW.  The children of `k` are exactly

\[
Q_2^{1-e}(J(c)),\qquad Q_1^{1-e}(J(c)),
\]

so at least one of this adjacent pair is DRAW.  In this case

\[
\boxed{p\text{ is WIN},\quad d\text{ is LOSS},\quad
h,k\text{ are DRAW}.}
\]

In either fork `r` is WIN: in the second fork it is a child of the LOSS
state `d`.  Since `c` is WIN and its other child `r` is WIN, the remaining
ordinary child is forced LOSS:

\[
\boxed{\ell\text{ is LOSS}.}
\]

The obstruction is therefore reduced to one exact switch.  The first fork
continues a DRAW through the lifted phase selecting the ordinary WIN child
`r`; the second continues through an adjacent pair in the opposite phase,
which selects the ordinary LOSS child `ell`.  Closing this WIN-source versus
LOSS-source switch, while retaining their proof heights, is sufficient to
finish the canonical minimum-source lift analysis.

## 24. The A-selecting lift closes one half of the final switch

There is a universal two-bit diamond behind the `A`-selecting phase.  Let
`x>0`, put

\[
e=\alpha(x),\qquad w=L_e(x),\qquad y=A(x),\qquad u=A(y).
\]

Then

\[
\boxed{B(w)\in\{A(y),B(y)\}.}
\]

In other words, the side child of the `A`-selecting source lift is always
an ordinary child of the selected source `A(x)`.  More precisely,

\[
B(w)=
\begin{cases}
A(y),&A(y)\bmod2=e,\\
B(y),&A(y)\bmod2\ne e.
\end{cases}
\]

Indeed, the source-boundary identity gives

\[
A(w)=L_{1-e}(y)=4A(y)+1+e.
\]

For `e=0` the last two appended bits are `01`, and for `e=1` they are
`10`.  If the last bit of `A(y)` equals `e`, the first appended bit repeats
it, so the maximal alternating suffix consists of exactly the appended two
bits and its deletion leaves `A(y)`.  Otherwise the alternation continues
into `A(y)`, and deleting it leaves `R(A(y))=B(y)`.  This proves both the
boxed identity and the refined formula.

The diamond retains exactly the proof-height information needed when the
selected source is losing.  Suppose `x` is WIN, `A(x)` is LOSS, and
`B(x)` is WIN.  Write

\[
b=B(L_{\alpha(x)}(x)).
\]

The boxed identity makes `b` a child of the unique LOSS child `A(x)` of
`x`.  Hence

\[
\boxed{b\text{ is WIN},\qquad h(b)\le h(x)-2.}
\]

Moreover `Q_1^{\alpha(x)}(J(x))` and
`Q_2^{\alpha(x)}(J(x))` share this same `B`-child.  Consequently, if either
member of that adjacent pair is DRAW, it supplies a DRAW-to-WIN boundary
whose endpoint height is at most `h(x)-2`.

Apply this to the second fork of Section 23 in the four rows

\[
s\equiv31,53,74,96\pmod {128}.
\]

There `e\ne\alpha(c)`, so the opposite phase in the adjacent pair is
`1-e=\alpha(c)`, while

\[
r=B(c)\text{ is WIN},\qquad \ell=A(c)\text{ is LOSS}.
\]

At least one member of the pair is DRAW.  Taking `x=c` in the preceding
diamond therefore produces a new boundary whose WIN endpoint has height at
most `h(c)-2`.  Thus this entire fork is a strict height descent.  This is a
conditional reduction, not yet the global no-DRAW theorem: the
`B`-selecting LOSS-source fork in the other four rows and the two
WIN-source continuations still have to be closed.

## 25. Every B-selecting fork transfers the DRAW to the selected source

The large diamond of Section 20 is not special to the phase-mismatch rows.
It gives a universal transfer rule for a `B`-selecting source phase.  Let
`x>0`, put

\[
e=1-\alpha(x),\qquad a=J(x),\qquad g=1-e,
\]

and factor the `B`-selecting signed transition as

\[
3a+1-2e=2^jJ(y),qquad j\ge2,qquad y=B(x).
\]

Define

\[
P=Q_1^e(a),\qquad U=Q_2^e(a),
\]

and their shared child and expanding siblings by

\[
D=A(P)=Q_j^g(J(y)),\qquad
C=B(P)=B(U)=Q_{j-1}^g(J(y)),\qquad
F=A(U)=Q_1^e(3a).
\]

The states `D` and `C` are an adjacent constant-tail frame over the ordinary
selected source `y=B(x)`.  Let `X` be their common child and `Y` the other
child of `C`.  Then

\[
\boxed{B(F)=Y.}
\]

The arithmetic proof in Section 20 used only the displayed valuation
identity, split into `j=2`, `j=3`, and `j>=4`; none of its steps used an
outcome or a special residue of `x`.  It therefore proves this universal
form verbatim.  The source and adjacent-exponent identities, as well as the
large diamond, are regression-tested for every `x<100000`.

This arithmetic identity has a useful outcome consequence.  Suppose first
that `P` is DRAW.  Its child `C` is non-losing, and at least one of `D,C`
must be DRAW.  Thus the lower adjacent frame over `B(x)` contains a DRAW.

There is a second version needed by Section 23.  Suppose some DRAW state
`K` has exactly `U` and `P` as its two children.  Again `C`, being a child
of every DRAW member among `U,P`, cannot be LOSS.  If `P` is DRAW, the
previous paragraph applies.  Otherwise `P` cannot be LOSS because it is a
child of `K`.  If both `P,U` were WIN, then `K` would be LOSS, so the only
remaining case is

\[
P\text{ WIN},\qquad U\text{ DRAW}.
\]

If `C` were WIN, then `D` would be LOSS and `F` would be DRAW.  The common
child `X` of the LOSS state `D` is WIN.  Since `C` is WIN and already has
the WIN child `X`, its other child `Y` must be LOSS.  But the universal
diamond makes `Y=B(F)` a child of the DRAW state `F`, a contradiction.
Therefore `C` is DRAW, and the lower adjacent frame again contains a DRAW.
We have proved the transfer rule

\[
\boxed{
\begin{array}{c}
P\text{ DRAW},\quad\text{or}\quad
K\text{ DRAW with children }U,P
\end{array}
\Longrightarrow
\{D,C\}\text{ contains a DRAW}.}
\]

This unifies all cases left after Section 24.  In the
`31,53,74,96 mod 128` rows, the first fork of Section 23 has
`P=L_e(c)` DRAW with `e` selecting `B(c)=r`, which is WIN.  In the
`10,32,95,117 mod 128` rows, the second fork has a DRAW parent whose two
children are the `B`-selecting pair over `c`; here `B(c)=ell` is LOSS.  In
both cases the boxed rule transfers the obligation to an adjacent frame
whose ordinary source is exactly `B(c)`.  What remains is to prove that an
indefinite sequence of these transferred adjacent frames must either drop
below the globally minimum DRAW source or expose a child of the retained
LOSS witness and hence lower the boundary proof height.

## 26. The transferred B-source survives only at valuation two

In the eight length-two rows of Section 23, the transfer of Section 25 can
be compared directly with the globally minimum DRAW source `s`.  Retain

\[
z=B(A(s)),\qquad c=A^2(z),\qquad y=B(c),
\]

and let `j>=2` be the valuation of the `B`-selecting signed source
transition at `c`.  Then

\[
\boxed{
y\ge s
\quad\Longleftrightarrow\quad
j=2
\quad\Longleftrightarrow\quad
s\bmod256\in
\{10,31,53,95,160,202,224,245\}.}
\]

Here is a proof that does not assume a fixed modulus determines an
unbounded suffix.  In the eight rows of Section 23, direct substitution
first gives

\[
\begin{array}{c|c}
s=128t+r&r\mapsto c\text{ offset in }c=324t+C_r\\ \hline
10&26\\
31&80\\
32&81\\
53&135\\
74&188\\
95&242\\
96&243\\
117&297.
\end{array}
\]

The valuation `j` is one more than the alternating-suffix length of
`A(c)`.  To see this, write `v=A(c)`, so `J(c)=2v+1`.  According to the
parity of `v`, the decreasing original move divides either
`3J(c)+1=2(3v+2)` or `3J(c)-1=2(3v+1)`.  Section 1's arithmetic formula for
`R(v)` says that the valuation of the expression in parentheses is exactly
the alternating-suffix length of `v`.  The extra displayed factor two proves
the claim about `j`.

Thus `j=2` exactly when that suffix has length one, a condition decided by
the last two bits of `A(c)`.  Substitution in the displayed table gives
precisely the eight residue classes modulo 256 in the box.  In those classes
write `s=256u+r`; deletion of the one-bit suffix gives the exact affine rows

\[
\begin{array}{c|c|c}
r&c&y=B(c)\\ \hline
10 &648u+26 &486u+19\\
31 &648u+80 &486u+60\\
53 &648u+135&486u+101\\
95 &648u+242&486u+181\\
160&648u+405&486u+304\\
202&648u+512&486u+384\\
224&648u+567&486u+425\\
245&648u+621&486u+466.
\end{array}
\]

Every right-hand entry is at least `256u+r`, proving `y>=s` in these
classes.  In all other rows `j>=3`, so the alternating suffix of `A(c)` has
length at least two and

\[
y\le\frac{3c+1}{8}.
\]

The bounds `z<=(9s+3)/8` and `c=A^2(z)<=(9z+5)/4` give

\[
y\le\frac{243s+233}{256}<s
\]

for every remaining residual source, all of which are at least 31.  This
proves the converse without making any assumption about how much farther
the suffix may continue.

Now impose the globally minimum-source hypothesis and either of the two
`B`-selecting forks left after Section 24.  Section 25 transfers a DRAW to
an adjacent frame whose source is `y=B(c)`.  If `y<s`, this contradicts the
definition of `s`.  Therefore only the eight boxed classes survive, and in
all of them the transferred frame is exactly the exponent-two/one pair

\[
\boxed{Q_2^{\alpha(c)}(J(y)),\qquad
Q_1^{\alpha(c)}(J(y)),}
\]

with at least one DRAW member.

One further phase bit is also finite.  Comparing `alpha(c)` with `alpha(y)`
in the eight affine rows, split once more modulo 512, gives

\[
\boxed{
\alpha(c)=\alpha(y)
\quad\Longleftrightarrow\quad
s\bmod512\in\{10,31,160,202,309,351,480,501\}.}
\]

The complementary surviving classes

\[
53,95,224,245,266,287,416,458\pmod {512}
\]

remain in the `B`-selecting phase at `y`.  Thus the final obstruction is no
longer an arbitrary-exponent frame: it is one exact exponent-one/two pair,
with its next ordinary source letter and phase completely specified.

## 27. At most two further B-source transfers can survive

It is useful to package the two ways in which an exponent-one/two pair
occurs.  For a source `x` and phase `e`, write `O(x,e)` for the following
**DRAW obligation**:

- either `Q_1^e(J(x))` is DRAW;
- or there is a DRAW state whose two children are exactly
  `Q_2^e(J(x))` and `Q_1^e(J(x))`.

This notation introduces no new assumption.  The first alternative is the
first fork of Section 23, and the second is its adjacent-pair fork.

Suppose `e` is the `B`-selecting phase at `x`, and let its valuation be
`j`.  Section 25 gives an adjacent frame over `y=B(x)` containing a DRAW.
When `j=2`, this transfer preserves the exact obligation form:

\[
\boxed{O(x,e)\Longrightarrow O(B(x),1-e).}
\]

Indeed, if `Q_1^e(J(x))` is DRAW, it is itself a DRAW parent of the
transferred exponent-two/one pair.  In the second alternative, if that same
exponent-one state is DRAW, the conclusion is identical.  Otherwise the
outcome proof in Section 25 forces the common transferred child
`Q_1^{1-e}(J(B(x)))` to be DRAW, which is the first alternative of the new
obligation.

After Section 26's first transfer, write its source as `x_0=B(c)`.  The
eight affine rows there give

\[
\boxed{s\le x_0<2s.}
\]

The lower inequality is required for survival.  The upper inequality is
immediate row by row; alternatively the general bound

\[
x_0\le\frac{243s+233}{128}

\]

proves it for `s>=18`, and the only smaller surviving source is `s=10`,
where `x_0=19`.

Now consider any further `B`-selecting obligation at a source `x<2s`.  If
its valuation is at least three, the alternating suffix of `A(x)` has
length at least two, so

\[
B(x)\le\frac{3x+1}{8}<s.
\]

Section 25 still transfers a DRAW to a frame over this source, contradicting
the global minimality of `s`.  Thus every surviving transfer has valuation
exactly two, preserves `O`, and satisfies

\[
x_{i+1}=B(x_i)\le\frac{3x_i+1}{4}.
\]

Three consecutive valuation-two transfers are also impossible.  Iterating
the last inequality gives

\[
x_3\le\frac{27x_0+37}{64}.
\]

For `s>=18`, substitution of the displayed bound for `x_0` yields

\[
x_3\le\frac{6561s+11027}{8192}<s.
\]

For `s=10`, the exact value `x_0=19` gives the same strict conclusion
directly.  Therefore

\[
\boxed{
\text{a surviving transferred obligation reaches its A-selecting phase}
\text{ after at most two further B transfers}.}
\]

This removes an infinite `B`-frame escape.  The remaining obstruction is
now an `A`-selecting obligation `O(x,alpha(x))` with `s<=x<2s`.  Section 24
places its common side child below the ordinary selected source `A(x)`;
the outstanding step is to retain enough of the WIN/LOSS proof tree when
the exponent-two member, rather than the exponent-one member, carries the
DRAW.

## 28. The A-selecting obligation has one bounded factor escape

Let `s` remain the globally minimum coefficient source of a DRAW, and let

\[
O(x,e),\qquad e=\alpha(x),\qquad s\le x<2s
\]

be the `A`-selecting obligation reached in Section 27.  Put

\[
P=Q_1^e(J(x)),\qquad U=Q_2^e(J(x)),\qquad
y=A(x),\qquad g=1-e,
\]

and

\[
V=A(P)=Q_1^g(J(y)),\qquad
b=B(P)=B(U),\qquad F=A(U)=Q_1^e(3J(x)).
\]

Section 24 says that `b` is an ordinary child of `y=A(x)`.  Its own
coefficient source is below `s`.  Indeed, for positive `b`, if `rho(b)` is
that source, then

\[
\rho(b)\le\frac{b-1}{6},
\]

while

\[
b\le A(y)=A^2(x)\le\frac{9x+5}{4}.
\]

Since the integer inequality `x<2s` means `x<=2s-1`, it follows that

\[
\boxed{\rho(b)\le\frac{9x+1}{24}<s.}
\]

Now apply the two alternatives in the definition of `O`.  Whenever `P` is
DRAW, its child `b` is non-losing.  The boxed source inequality makes it
non-DRAW, so it is WIN, and the other child `V` is forced DRAW.  Thus

\[
\boxed{P\text{ DRAW}\Longrightarrow O(A(x),1-e)}
\]

through the first alternative of `O`.

Otherwise `O(x,e)` is witnessed by a DRAW parent `K` of `U,P`.  The state
`P` cannot be LOSS.  If it is DRAW, the preceding paragraph applies.  The
only other possibility is therefore

\[
P\text{ WIN},\qquad U\text{ DRAW}.
\]

The common child `b` is again WIN.  Hence `V`, the other child of `P`, is
LOSS, while `F`, the other child of `U`, is DRAW:

\[
\boxed{P,b\text{ WIN},\quad V\text{ LOSS},\quad U,F\text{ DRAW}.}
\]

The factor state `F` has an exact source frame.  For some `r>=1`,

\[
\boxed{
A(F)=Q_{r+1}^g(J(b)),\qquad
B(F)=Q_r^g(J(b)).}
\]

This is the universal form of Section 21's coefficient calculation.  For
`e=0`, the identity `kappa(9J(x))=J(R(3J(x)))` gives source `b`; for `e=1`,
the identity for `9J(x)-1`, together with the shared-child formula, gives
the same result.  The final two equal bits then make the two children
adjacent.  Since `F` is DRAW, this adjacent frame contains a DRAW.

If `b<s`, the frame contradicts minimum source immediately.  If `b>=s`,
its lower exponent is at most three.  To prove this, the displayed frame
identity gives

\[
J(b)2^{r+1}=9J(x)-e+g\le27x+19.
\]

As `J(b)>=3b+1`, an exponent `r>=4` would imply

\[
b\le\frac{27x-13}{96}
\le\frac{54s-40}{96}<s,
\]

a contradiction.  Therefore the only surviving factor frames are

\[
\boxed{
\{Q_2^g(J(b)),Q_1^g(J(b))\},\quad
\{Q_3^g(J(b)),Q_2^g(J(b))\},\quad
\{Q_4^g(J(b)),Q_3^g(J(b))\}.}
\]

All arithmetic identities and the exponent bound are regression-tested in
the actual residual source trajectory.  The first pair is again an exact
obligation `O(b,g)`.  Two mechanisms therefore remain open: the canonical
continuation `O(A(x),g)` from the first case, and the factor continuation at
one of the three displayed exponents from the second case.  A completion
must control their possible alternation, using the retained LOSS state `V`,
or show that the resulting boundary WIN `b` has lower proof height than the
original endpoint.  The exponent bound alone does not exclude the canonical
continuation.

## 29. The factor escape is an opposite-tail twin switch

The retained LOSS state in Section 28 is not merely auxiliary.  It produces
the opposite tail twin of the lower factor-frame child.  Keep all notation
from that section.  If

\[
B(F)=Q_r^g(J(b)),\qquad g=1-e,
\]

then

\[
\boxed{A(V)=Q_r^e(J(b)).}
\]

For `e=0`, one has `V=3J(x)` and

\[
A(V)=\frac{9J(x)+1}{2}.
\]

The factor identity

\[
A(F)=9J(x)=Q_{r+1}^1(J(b))

\]

says that `J(b)2^(r+1)=9J(x)+1`; division by two proves the box.  For
`e=1`, one has `V=3J(x)-1` and

\[
A(V)=\frac{9J(x)-3}{2}.
\]

Now `A(F)=9J(x)-1=Q_{r+1}^0(J(b))`, so division by two followed by
subtraction of one again gives exactly `Q_r^1(J(b))`.  These two cases
prove the identity.

The forced outcomes in the factor fork therefore have the exact form

\[
\boxed{
V\text{ LOSS},\qquad
Q_r^e(J(b))=A(V)\text{ WIN},\qquad
Q_r^{1-e}(J(b))=B(F)\text{ is non-losing},
}
\]

while the DRAW parent `F` has children

\[
Q_{r+1}^{1-e}(J(b)),\qquad Q_r^{1-e}(J(b))
\]

and at least one of them is DRAW.  By Section 28 only `r=1,2,3` can survive
at source `b>=s`.

This is a structural normalization, not an outcome contradiction.  Two
opposite-tail twins are consecutive integers, but consecutive positions can
have any of the relevant finite outcome combinations; no rule proved so far
allows their outcomes to be identified.  The remaining task is to use their
coupled long-tail recurrences and the finite proof tree below the explicit
LOSS state `V`, rather than assuming that neighboring integers share an
outcome.

## 30. The factor frame and the retained WIN share the next twin switch

The two adjacent children of the factor DRAW in Section 29 have one common
child.  This exposes the first exact recursive step of the twin obstruction.
Keep the notation there and abbreviate

\[
a=J(b),\qquad
E=Q_r^e(a)=A(V),\qquad
H=Q_{r+1}^g(a)=A(F),\qquad
G=Q_r^g(a)=B(F).
\]

Because \(V\) is LOSS, both \(E\) and \(B(V)=R(E)\) are WIN.  Because
\(F\) is DRAW, \(H\) and \(G\) are non-losing and at least one of them is
DRAW.

The states \(H\) and \(G\) have the exact common child

\[
\boxed{
X=
\begin{cases}
B(Q_1^g(a))=B(Q_2^g(a)),&r=1,\\
Q_{r-1}^g(3a),&r=2,3.
\end{cases}}
\]

For \(r=1\) this is the symmetric shared-child identity of Section 14.  For
\(r\ge2\), the lower state has expanding child

\[
A(G)=Q_{r-1}^g(3a),
\]

while the upper state has the same contracting child

\[
B(H)=Q_{r-1}^g(3a).
\]

The latter identity uses the long-tail recurrence because \(r+1\ge3\).
Therefore \(X\) is a child of whichever member of \(\{H,G\}\) is DRAW.  It
cannot be LOSS.  There are exactly two outcome alternatives:

- if \(X\) is WIN, that DRAW member and \(X\) form another boundary edge;
- if \(X\) is DRAW, the factor obligation has transferred to this one
  common state (and for \(r=2,3\) its coefficient is \(3J(b)\) and its
  exponent is \(r-1\)).

For \(r=2,3\) the retained WIN state \(E\) exposes the opposite-tail twin of
\(X\) one step later:

\[
\boxed{A(E)=Q_{r-1}^e(3a).}
\]

Thus \(A(E)\) and \(X\) are consecutive integers with opposite constant
tails.  Since \(E\) is WIN, either \(A(E)\) is LOSS or the other child
\(B(E)\) is LOSS.  In the case \(r=3\) this becomes the particularly compact
forced alternative

\[
\boxed{
Q_2^e(3a)\text{ is LOSS}
\quad\text{or}\quad
Q_1^e(3a)\text{ is LOSS}.}
\]

This is a genuine recursive outcome constraint, but still not the final
contradiction.  If the common child \(X\) is DRAW, the next level contains a
DRAW state on one tail side and a forced LOSS on the opposite side.  At
\(r=1\) the shared child crosses the signed boundary instead, so a completion
must control that signed transition as well as the two long-tail cases.
The identities in this section are regression-tested throughout the actual
residual source trajectory.

## 31. The exponent-one factor switch has a strict source return

Section 30 leaves a signed boundary when the lower factor exponent is
\(r=1\).  In the actual residual trajectory this boundary has an additional
rank property.  Retain Sections 28--30 and suppose

\[
O(x,e),\qquad e=\alpha(x),\qquad s\le x<2s,
\]

enters the factor fork with \(r=1\).  Then

\[
\boxed{b=A^2(x).}
\]

Indeed, \(V=L_g(A(x))\), where \(g=1-e\), and Section 29 writes its expanding
child as \(Q_1^e(J(b))\).  Exponent one means exactly that \(g\) is the
\(A\)-selecting phase at \(A(x)\).  The selected ordinary source is therefore
\(A^2(x)\).

Let

\[
X=B(Q_1^g(J(b)))=B(Q_2^g(J(b)))
\]

be the common factor child from Section 30, and let \(\rho(X)\) denote its
coefficient source.  If \(g=\alpha(b)\), then

\[
\boxed{\rho(X)<x.}
\]

Section 24 makes \(X\) an ordinary child of \(A(b)\), so

\[
X\le A^2(b)\le\frac{9b+5}{4}.
\]

For every positive state \(q\), its coefficient source satisfies
\(\rho(q)\le(q-1)/6\).  Also

\[
b=A^2(x)\le\frac{9x+5}{4}.
\]

Combining these estimates gives

\[
\rho(X)\le\frac{9b+1}{24}
\le\frac{81x+49}{96}<x,
\]

where the final inequality holds for \(x\ge4\); every residual source here
has \(x\ge19\).  Thus if \(X\) is DRAW, the factor escape has made a strict
source descent relative to the \(A\)-selecting source that generated it.  If
\(\rho(X)<s\), global source minimality excludes that alternative outright.

Suppose instead that \(g\) is the \(B\)-selecting phase at \(b\), with signed
valuation \(j\ge2\).  Section 25 identifies the common factor child's source
exactly:

\[
\boxed{\rho(X)=B(b).}
\]

The valuation is one more than the alternating-suffix length of \(A(b)\), so

\[
B(b)\le\frac{3b+1}{2^j}
\le\frac{27x+19}{2^{j+2}}.
\]

Since \(x\le2s-1\), this proves the finite trichotomy

\[
\boxed{
\begin{array}{c|c}
j\ge4&B(b)<s,\\
j=3&B(b)<27s/16,\\
j=2&B(b)<27s/8.
\end{array}}
\]

Consequently an exponent-one factor switch cannot hide an unbounded signed
valuation.  An \(A\)-selecting continuation strictly decreases the source
relative to \(x\), while a source-surviving \(B\)-selection has only
valuation two or three and remains in an explicit constant-size window over
\(s\).  This still does not close the \(r=2,3\) DRAW/LOSS twin switch or the
possible alternation with canonical \(A\)-continuations, but it supplies the
first well-founded component at the signed boundary.  All displayed
identities and bounds are regression-tested in the residual trajectory.

## 32. The exponent-two and three switches have finite signed valuations

The two long-tail alternatives from Section 30 also reach only finitely many
signed valuation states.  Continue to assume

\[
s\le x<2s
\]

at the \(A\)-selecting obligation of Section 28, put \(a=J(b)\), and suppose
the common factor child \(X\) of Section 30 is DRAW.

First let the lower factor exponent be \(r=2\).  The factor equation gives

\[
8J(b)=9J(x)+1-2e.
\]

Using \(J(q)\le3q+2\) and \(J(q)\ge3q+1\) yields

\[
\boxed{b\le\frac{27x+11}{24}
\le\frac{27s-8}{12}<\frac94s.}
\]

Here the common DRAW is

\[
X=Q_1^g(3J(b)).
\]

Factor its signed expanding transition as

\[
9J(b)+1-2g=2^vJ(t).
\]

If \(v\ge2\), both children of \(X\) have source \(t\): they are the
adjacent states with exponents \(v\) and \(v-1\).  If \(t<s\), neither child
can be DRAW; both are non-losing children of a DRAW and hence both are WIN,
which would make \(X\) LOSS.  Therefore a surviving transition has
\(t\ge s\).  But

\[
t\le\frac{(27b+19)/2^v-1}{3},
\]

and the boxed bound makes the right side strictly below \(s\) when
\(v\ge5\).  Consequently

\[
\boxed{r=2,\ X\text{ DRAW}\quad\Longrightarrow\quad v\le4.}
\]

Now let the lower factor exponent be \(r=3\).  The same factor equation has
one additional power of two:

\[
16J(b)=9J(x)+1-2e,
\]

so

\[
\boxed{b\le\frac{27x+3}{48}
\le\frac{9s-4}{8}<\frac98s.}
\]

The common DRAW is

\[
X=Q_2^g(3J(b)).
\]

Its contracting child is also the boundary child of
\(Q_1^g(3J(b))\).  Write

\[
9J(b)+1-2g=2^vJ(t).
\]

If this contracting child is DRAW, then \(t\ge s\) by the same adjacent-frame
argument.  The last boxed estimate makes \(t<s\) for every \(v\ge4\).
Therefore this DRAW continuation has

\[
\boxed{v\le3.}
\]

If the contracting child is WIN, the other child of \(X\) must be DRAW.  It
is

\[
Y=Q_1^g(9J(b)).
\]

Write its signed transition as

\[
27J(b)+1-2g=2^wJ(u).
\]

For \(w\ge2\), both children of \(Y\) have source \(u\), so survival again
requires \(u\ge s\).  The estimate

\[
u\le\frac{(81b+55)/2^w-1}{3}
\]

and \(b<(9/8)s\) give \(u<s\) for \(w\ge5\).  Hence

\[
\boxed{r=3,\ Y\text{ DRAW}\quad\Longrightarrow\quad w\le4.}
\]

Sections 31--32 therefore replace every unbounded signed scan immediately
following the final factor fork by a finite list: valuation \(2\) or \(3\)
at the exponent-one source return, valuation at most \(4\) after \(r=2\),
and valuations at most \(3\) then \(4\) in the two \(r=3\) continuations.
This is a finite-state reduction, not yet a proof that none of these states
can cycle with the canonical \(A\)-continuation.  The arithmetic bounds are
regression-tested in every residual row below \(100000\).

## 33. A high-valuation exponent-three switch returns to a B-selecting lift

The apparently unbounded valuation in the \(r=3\) case of Section 32 is
actually one finite transition type.  Keep its notation, let
\(g=1-e\), and write

\[
9J(b)+1-2g=2^vJ(t).
\]

Suppose \(v\ge4\).  The contracting child of the common DRAW

\[
X=Q_2^g(3J(b))
\]

is

\[
C=Q_{v-1}^e(J(t)).
\]

Section 32 gives \(t<s\), so global source minimality makes \(C\) WIN.
Therefore the other child

\[
Y=A(X)=Q_1^g(9J(b))
\]

is forced DRAW.

The next signed numerator is

\[
27J(b)+1-2g
=3\bigl(9J(b)+1-2g\bigr)-2(1-2g).
\]

Because \(v\ge2\), the last display has 2-adic valuation exactly one.
Consequently there is a source \(u\) such that

\[
27J(b)+1-2g=2J(u),
\qquad
A(Y)=Q_1^e(J(u))=L_e(u).
\]

Put \(T=J(t)\).  The source \(u\) itself has the closed form

\[
\boxed{u=Q_{v-1}^e(T).}
\]

For \(g=0\), one has
\(J(u)=3\cdot2^{v-1}T-1\), so
\(u=2^{v-1}T-1\).  For \(g=1\), one has
\(J(u)=3\cdot2^{v-1}T+1\), so
\(u=2^{v-1}T\).  These are precisely the two instances of the box.  Since
\(v\ge4\), the last two bits of \(u\) are \(11\) when \(e=1\) and \(00\)
when \(e=0\).  Hence

\[
\boxed{\alpha(u)=g,\qquad e=1-\alpha(u).}
\]

Thus \(L_e(u)\) is a B-selecting lift, not an A-selecting one.  Its other
child still has a closed form:

\[
\boxed{B(Y)=Q_{v-3}^e(3J(t)).}
\]

For \(g=0\), the expanded state is

\[
A(Y)=3\cdot2^vJ(t)-3.
\]

Its last bits are the fixed suffix \(101\), preceded by another one because
\(v\ge4\); deleting that suffix gives
\(Q_{v-3}^1(3J(t))\).  For \(g=1\), the expanded state is

\[
A(Y)=3\cdot2^vJ(t)+2.
\]

Its last bits are \(010\), preceded by another zero, and deletion gives
\(Q_{v-3}^0(3J(t))\).  These are the two instances of the boxed identity.
In particular \(B(Y)\) has source \(t<s\), so it too is WIN.  Since \(Y\)
is DRAW, its other child is forced DRAW:

\[
\boxed{L_e(u)\text{ is DRAW},\qquad e=1-\alpha(u).}
\]

The returned source remains in a fixed window.  From

\[
2J(u)=27J(b)+1-2g
\]

and Section 32's \(b\le(9s-4)/8\),

\[
u\le\frac{81b+53}{6}
\le\frac{729s+100}{48}<16s
\]

for every residual \(s\ge10\).  Thus all valuations \(v\ge4\) collapse to
one automaton edge:

\[
\boxed{
r=3,\ v\ge4
\quad\Longrightarrow\quad
\text{a B-selecting DRAW lift at }u<16s,
}
\]

with two explicitly known WIN side states of source below \(s\).  The size
window is larger than the one in Section 28, so this is not yet a descent
proof.  Its importance is that the unbounded valuation has disappeared
without enumeration, while the two retained WIN states remain available for
a proof-height diamond.  The exact identities and the \(16s\) bound are
regression-tested in the residual trajectory.

## 34. The high-valuation return carries a strict ordinary height drop

The two small-source WIN states retained in Section 33 recover the proof
height lost in the source lift.  Keep its notation and put

\[
C=B(X)=Q_{v-1}^e(J(t)),\qquad
Z=B(Y)=Q_{v-3}^e(3J(t)).
\]

Both \(C\) and \(Z\) are WIN because their source \(t\) is below the globally
minimum DRAW source \(s\).  The long-tail recurrence gives

\[
\boxed{B(C)=Z.}
\]

Therefore the other child

\[
L=A(C)=Q_{v-2}^e(3J(t))
\]

is LOSS.  The states \(L\) and \(Z\) have one exact common child.  For
\(v=4\), they are the exponent-two/one boundary pair, so

\[
W=B(L)=B(Z).
\]

For \(v\ge5\), the long-tail formulas instead give

\[
W=B(L)=A(Z)=Q_{v-4}^e(9J(t)).
\]

In either case \(W\) is a child of the LOSS state \(L\), hence is WIN, and
the canonical proof heights satisfy

\[
\boxed{h(W)\le h(C)-2.}
\]

The common child is not merely another lifted coordinate.  It is exactly the
ordinary two-step return of the source \(u\) from Section 33:

\[
\boxed{W=B(A(u)).}
\]

For \(v\ge5\), direct substitution into
\(2J(u)=27J(b)+1-2g\) gives

\[
A^2(u)=
\begin{cases}
2W+1,&g=0,\\
2W,&g=1.
\end{cases}
\]

In the first row \(W\) is odd and in the second it is even.  The appended
bit therefore repeats the last bit of \(W\), so deleting the maximal
alternating suffix from \(A^2(u)\) removes exactly that appended bit and
leaves \(W\).

For \(v=4\), write \(J(t)=T\).  If \(g=0\), then

\[
A(u)=12T-1,\qquad A^2(u)=18T-1,
\]

whereas \(A(Z)=9T-1\); the first value is obtained from the second by
appending an alternating one bit.  If \(g=1\), then

\[
A(u)=12T,\qquad A^2(u)=18T,
\]

and \(A(Z)=9T\), with an alternating zero bit appended.  In both rows the
suffix deletion from \(A^2(u)\) is therefore the same as the deletion from
\(A(Z)\), namely \(B(Z)=W\).  This proves the boxed return identity at the
boundary as well.

Thus the high-valuation \(r=3\) escape does not merely return to a
B-selecting lift below \(16s\).  Its ordinary source diamond has already
produced a WIN node \(W=B(A(u))\) whose proof height is at least two below
the preceding boundary endpoint \(C\).  A final completion still has to
show that the lifted continuation at \(u\) exposes \(W\) (or another child
of the same LOSS witness) as a DRAW-boundary endpoint despite the exceptional
lift parent.  The exact common-child and return identities are
regression-tested in all high-valuation residual rows.

## 35. The returned lift transfers to the lower-height WIN source

The B-selecting correction in Section 33 makes the high-valuation return
more rigid.  Keep Sections 33--34 and write \(T=J(t)\).  Since

\[
u=Q_{v-1}^e(T),\qquad v\ge4,
\]

the long-tail recurrence gives

\[
\boxed{B(u)=Q_{v-3}^e(3T)=Z.}
\]

The B-selecting signed transition of \(L_e(u)\) has valuation exactly two.
Indeed, for \(g=0\) one has

\[
J(u)=3\cdot2^{v-1}T-1,\qquad
3J(u)-1=4\bigl(9\cdot2^{v-3}T-1\bigr),
\]

and the factor in parentheses is odd.  For \(g=1\),

\[
J(u)=3\cdot2^{v-1}T+1,\qquad
3J(u)+1=4\bigl(9\cdot2^{v-3}T+1\bigr),
\]

with the same conclusion.  Hence the DRAW state \(L_e(u)\) has the exact
children

\[
Q_2^g(J(Z)),\qquad Q_1^g(J(Z)).
\]

In the notation of Section 27 this is the obligation

\[
\boxed{O(Z,g),\qquad g=\alpha(u).}
\]

Moreover this phase selects exactly the lower-height WIN \(W=B(A(u))\) from
Section 34.  There are two boundary forms:

\[
\boxed{
\begin{array}{c|c|c}
v&\text{phase at }Z&\text{selected child}\\ \hline
4&g=1-\alpha(Z)&B(Z)=W,\\
v\ge5&g=\alpha(Z)&A(Z)=W.
\end{array}}
\]

For \(v=4\), the state \(Z=Q_1^e(3T)\) has
\(\alpha(Z)=e\), and Section 34 already proved \(B(Z)=W\).  For \(v\ge5\),
the exponent of \(Z=Q_{v-3}^e(3T)\) is at least two; its two final bits are
both \(e\), so \(\alpha(Z)=1-e=g\), and Section 34 gives \(A(Z)=W\).
Since \(Z\) and \(W\) are WIN, the unselected child \(M\) of \(Z\) is LOSS.

All cases \(v\ge6\) now give a strict boundary-height descent.  In this
range \(Z\) has constant-tail exponent at least three and is nonexceptional.
The selected WIN has

\[
W=Q_{v-4}^e(9T)
\]

with at least two final bits equal to \(e\).  Consequently
\(A(W)\bmod2\ne g\).  Section 24 therefore identifies the common side child
of the exponent-one/two obligation as

\[
q=B(L_g(Z))=B(W).
\]

The ordinary side relation at the nonexceptional state \(Z\) makes the same
\(q=B(A(Z))\) a child of the LOSS state \(M=B(Z)\).  Thus \(q\) is WIN and

\[
\boxed{h(q)\le h(Z)-2.}
\]

Both members of the obligation share \(q\) as their contracting child, and
at least one member is DRAW.  Hence \(q\) is the endpoint of a new
DRAW-to-WIN boundary.  We have proved the conditional reduction

\[
\boxed{
r=3,\ v\ge6
\quad\Longrightarrow\quad
\text{a strict boundary-height descent}.}
\]

Only the two explicit high-valuation boundary cases \(v=4,5\) remain; the
unbounded class \(v\ge6\) is closed without a modulus scan.  The transfer,
selected-child, and common-side identities are regression-tested throughout
the residual trajectory.

## 36. The two remaining high-valuation boundaries are finite

Section 35 leaves only \(v=4\) and \(v=5\).  Both have a bounded exact
normal form.

### The case \(v=4\)

Here the obligation \(O(Z,g)\) is B-selecting and selects the WIN source
\(W=B(Z)\).  Let \(j\ge2\) be this B-selecting valuation.  Section 25
transfers the DRAW to an adjacent frame over \(W\).  If \(W<s\), global
source minimality excludes that frame, so survival requires \(W\ge s\).

The first high-valuation equation and the \(r=3\) source bound give

\[
t\le\frac{27b+3}{48}
\le\frac{81s-28}{128}.
\]

Also \(Z=Q_1^e(3J(t))\), so \(Z\le18t+12\).  If \(j\ge6\), the signed source
identity at \(Z\), together with \(J(q)\ge3q+1\), gives

\[
W\le\frac{54t+17}{64}
\le\frac{4374s+664}{8192}<s.
\]

This contradicts survival.  Hence

\[
\boxed{
v=4,\ \text{the transfer survives}\quad\Longrightarrow\quad
\text{the transferred frame over }W\text{ has }2\le j\le5.}
\]

Thus every surviving lower exponent is one of \(1,2,3,4\); no unbounded
suffix remains in this branch.

### The case \(v=5\)

Now \(O(Z,g)\) is A-selecting, with

\[
Z=Q_2^e(3J(t)),\qquad
W=A(Z)=Q_1^e(9J(t)),
\]

and the other ordinary child

\[
M=B(Z)
\]

is LOSS.  Section 24 gives the common side child of the exponent-one/two
obligation as

\[
q=B(L_g(Z))=A(W).
\]

This state has the exact source form

\[
\boxed{q=Q_k^g(J(M))}
\]

for some \(k\ge1\), with no factor of three in its coefficient.  To prove
this, put \(T=J(t)\).  If \(e=0\), then \(q=27T\).  Section 18 applied to
\(3(9T)\), together with
\(R(18T)=R(9T)\), gives \(\kappa(q)=J(M)\).  If \(e=1\), then
\(q=27T-1\), and Section 18 applied to \(3(9T)-1\) gives directly
\(\kappa(q)=J(R(18T-1))=J(M)\).  The final bit of \(q\) is \(g\) in both
cases, proving the box.

The valuation-five equation sharpens the bound for \(t\):

\[
t\le\frac{27b-13}{96}
\le\frac{243s-212}{768}.
\]

The coordinate identity

\[
2^kJ(M)=q+g=27J(t)-e+g
\]

then implies, for \(k\ge4\),

\[
M\le\frac{27t+13}{16}
\le\frac{6561s+4260}{12288}<s.
\]

The common child \(q\) is non-losing because it belongs to a DRAW member of
the obligation.  If it is DRAW, its source cannot be below \(s\).
Consequently

\[
\boxed{
v=5,\ q\text{ DRAW}\quad\Longrightarrow\quad k\le3.}
\]

If \(q\) is WIN instead, it is already the endpoint of a new boundary.
Thus the whole former high-valuation \(r=3\) branch now has only finite
parameters: \(v\ge6\) is a strict height descent, \(v=4\) leaves four
adjacent exponents over the lower-height WIN source \(W\), and \(v=5\)
leaves one DRAW state of exponent at most three over the explicit LOSS
source \(M\).  Closing these finite frames and the low-valuation cases
\(v=1,2,3\) remains necessary.  All coordinate identities and numerical
bounds are regression-tested in the residual trajectory.

## 37. The valuation-four branch has a finite WIN/DRAW ladder

The \(v=4\) frame of Section 36 retains the ordinary LOSS sibling
\(M=A(Z)\).  Let \(e=1-g\), and write its surviving B-selecting transition
as

\[
3J(Z)+1-2g=2^jJ(W),\qquad 2\le j\le5.
\]

Because \(J(Z)=2A(Z)+1=2M+1\), this identity is equivalent to

\[
3M+2-g=2^{j-1}J(W).
\]

Its parity gives \(M\bmod2=g\).  Therefore, whenever \(j\ge3\),

\[
\begin{aligned}
A(M)
&=\frac{3M+g}{2}\\
&=2^{j-2}J(W)-e\\
&=\boxed{Q_{j-2}^e(J(W)).}
\end{aligned}
\]

If \(j\ge4\), the displayed state has constant-tail exponent at least two,
so the contracting move from \(M\) deletes one final bit and gives

\[
\boxed{B(M)=Q_{j-3}^e(J(W)).}
\]

Since \(M\) is LOSS, all displayed children are WIN.  On the other hand,
Section 25 supplies an adjacent frame containing a DRAW at the upper levels

\[
Q_j^e(J(W)),\qquad Q_{j-1}^e(J(W)).
\]

Thus the surviving \(v=4\) obstruction has only the following finite ladder
forms:

\[
\boxed{
\begin{array}{c|c|c}
j&\text{upper frame containing DRAW}&\text{forced lower WIN states}\\ \hline
3&Q_3^e,Q_2^e&Q_1^e,\\
4&Q_4^e,Q_3^e&Q_2^e,Q_1^e,\\
5&Q_5^e,Q_4^e&Q_3^e,Q_2^e.
\end{array}}
\]

All coefficients in the table are \(J(W)\).  The case \(j=2\) remains a
separate signed boundary, while \(j\ge6\) was already excluded in Section
36.  This ladder is an outcome normalization, not yet a contradiction:
one must still propagate the upper DRAW through the long-tail recurrence
and use the lower WIN witnesses to produce a boundary below \(h(W)\).
The exact lower-level identities are regression-tested in every residual
\(v=4\) row.

## 38. A DRAW in the valuation-five side state is exceptional

Retain the notation of the \(v=5\) case in Section 36.  Thus \(Z\) and
\(W=A(Z)\) are WIN, \(M=B(Z)\) is LOSS, and the common non-losing side state
is

\[
q=A(W)=Q_k^g(J(M)).
\]

Suppose first that \(q\) is DRAW.  Since \(W\) is WIN and one of its two
children is the non-losing state \(q\), its other child

\[
N=B(W)=B(A(Z))
\]

must be LOSS.  If \(Z\) is nonexceptional, however, the ordinary side
relation makes the same \(N\) a child of \(M=B(Z)\).  This is impossible,
because every child of the LOSS state \(M\) is WIN.  Hence

\[
q\text{ DRAW}\quad\Longrightarrow\quad
Z\bmod16\in\{1,3,12,14\}.
\]

Here \(Z=Q_2^e(3J(t))=12J(t)-e\).  As \(J(t)\) is odd, its possible residues
modulo \(16\) are \(4,12\) when \(e=0\), and \(3,11\) when \(e=1\).
Intersecting with the exceptional set leaves only

\[
\boxed{q\text{ DRAW}\quad\Longrightarrow\quad
Z\bmod16\in\{3,12\}.}
\]

These two rows also force at least two final \(g\)-bits in \(q\).  If
\(Z\equiv3\pmod {16}\), then \(g=0\), \(W=A(Z)\equiv5\pmod8\), and
\(q=A(W)\equiv0\pmod4\).  If \(Z\equiv12\pmod {16}\), then \(g=1\),
\(W\equiv2\pmod8\), and \(q\equiv-1\pmod4\).  In the exact coordinate
\(q=Q_k^g(J(M))\), both alternatives imply \(k\ge2\).  Section 36 already
proved \(k\le3\) whenever \(q\) is DRAW.  Therefore

\[
\boxed{
v=5,\ q\text{ DRAW}
\quad\Longrightarrow\quad
Z\equiv3\text{ or }12\pmod {16},\qquad k\in\{2,3\}.}
\]

For every nonexceptional \(Z\), the common state \(q\) is consequently WIN
and is an immediate endpoint of a new DRAW-to-WIN boundary.  The only
valuation-five DRAW continuation is now one of two adjacent constant-tail
levels over the explicit LOSS source \(M\).  The exceptional classification,
the side-child identity in every nonexceptional row, and the lower bound on
\(k\) are regression-tested.

## 39. A surviving valuation-five DRAW strictly lowers boundary height

The exceptional continuation isolated in Section 38 also contains the
missing height comparison.  Suppose \(q=A(W)\) is DRAW.  Since \(W\) is WIN
and its child \(q\) is not LOSS, the other child

\[
N=B(W)
\]

must be LOSS.  Section 38 makes \(Z\) exceptional.  Exceptional classes
never occur consecutively on an \(A\)-orbit, so \(W=A(Z)\) is
nonexceptional.  The ordinary side relation at \(W\) therefore makes

\[
p=B(q)=B(A(W))
\]

a child of \(N=B(W)\).  Hence \(p\) is WIN.  It is also a child of the DRAW
state \(q\), so \(q\to p\) is a new boundary edge, and the canonical height
recursion gives

\[
\boxed{h(p)\le h(W)-2.}
\]

Consequently the valuation-five branch has the exact dichotomy

\[
\boxed{
v=5\quad\Longrightarrow\quad
\begin{cases}
q\text{ is WIN},&\text{a new boundary is already exposed},\\
q\text{ is DRAW},&\text{a new boundary endpoint has height at most }
                  h(W)-2.
\end{cases}}
\]

The second alternative is a strict descent from the lower-height WIN
already retained by Sections 34--35.  It closes every DRAW continuation in
the \(v=5\) side state; only the WIN-boundary alternative can re-enter the
factor analysis.  The nonexceptionality of \(W\) and the exact side-child
identity are regression-tested.

## 40. The valuation-four ladders force a finite set of LOSS witnesses

The three ladders in Section 37 admit a complete local outcome split.  Put

\[
S_r=Q_r^e(J(W)),\qquad T_r=Q_r^e(3J(W)),
\]

and denote the common boundary child of \(S_1,S_2\) by

\[
C=B(S_1)=B(S_2),\qquad D=A(S_1).
\]

For \(r\ge3\), the long-tail recurrence gives

\[
S_r\longrightarrow T_{r-1},T_{r-2}.
\]

In particular, the two upper members \(S_j,S_{j-1}\) share exactly
\(T_{j-2}\).  The transfer proof of Section 25 supplies slightly more than
the statement that this pair contains a DRAW:

- \(S_{j-1}\) is always non-losing;
- at least one of \(S_j,S_{j-1}\) is DRAW.

Indeed, in the direct alternative they are the two children of a DRAW
state.  In the other alternative Section 25 forces \(S_{j-1}\) DRAW (and
may force \(S_j\) LOSS).

Now use the lower WIN states supplied by the LOSS position \(M\).

### The \(j=3\) ladder

Here \(S_1\) is WIN.  If \(S_2\) is DRAW, both of its children \(T_1,C\)
are non-losing, so the other child \(D\) of the WIN state \(S_1\) must be
LOSS.  If \(S_2\) is WIN, then \(S_3\) must be DRAW.  Their common child
\(T_1\) is non-losing, so the other child \(C\) of \(S_2\) must be LOSS.
Thus

\[
\boxed{j=3\quad\Longrightarrow\quad D\text{ LOSS}\ \text{or}\ C\text{
 LOSS}.}
\]

### The \(j=4\) ladder

Now \(S_2,S_1\) are both WIN.  If \(S_3\) is DRAW, its child \(T_1\) is
non-losing; the WIN state \(S_2\), whose children are \(T_1,C\), therefore
forces \(C\) LOSS.  If \(S_3\) is WIN, then \(S_4\) must be DRAW.  Their
common child \(T_2\) is non-losing, so the other child \(T_1\) of \(S_3\)
is LOSS.  Hence

\[
\boxed{j=4\quad\Longrightarrow\quad C\text{ LOSS}\ \text{or}\ T_1\text{
 LOSS}.}
\]

### The \(j=5\) ladder

Here \(S_3,S_2\) are WIN.  If \(S_4\) is DRAW, its child \(T_2\) is
non-losing, so the other child \(T_1\) of the WIN state \(S_3\) is LOSS.
If \(S_4\) is WIN, then \(S_5\) must be DRAW.  Their common child \(T_3\)
is non-losing, forcing the other child \(T_2\) of \(S_4\) to be LOSS.
Therefore

\[
\boxed{j=5\quad\Longrightarrow\quad T_1\text{ LOSS}\ \text{or}\ T_2\text{
 LOSS}.}
\]

In the second \(j=5\) alternative, the remaining WIN state \(S_2\) also
forces at least one of \(T_1,C\) to be LOSS.  Thus every \(j=3,4,5\)
ladder now comes with an explicit LOSS witness drawn from the fixed set
\(\{C,D,T_1,T_2\}\).  Closing the branch no longer requires guessing which
upper member carries the DRAW; it requires coupling only these four LOSS
states to the next common side child.  The shared-child and lower-ladder
identities are regression-tested.

## 41. A one-sided LOSS witness either descends or meets an exception

The outcome splits of Sections 39--40 are instances of one general
boundary lemma.  Let \(x\) be WIN, let one of its ordinary children
\(\ell\) be LOSS, and let its other child \(y\) also be a child of some
DRAW state \(d\).  Then \(y\) is non-losing.  There are two alternatives.

If \(y\) is WIN, the edge \(d\to y\) is already a boundary edge.  If \(y\)
is DRAW and \(x\) is nonexceptional, put

\[
p=B(A(x)).
\]

The ordinary side relation at \(x\) makes \(p\) a child of both \(\ell\)
and \(y\), irrespective of whether \(\ell=A(x)\) or \(\ell=B(x)\).  Hence
\(p\) is WIN, \(y\to p\) is a boundary edge, and, because \(\ell\) is the
unique LOSS child of \(x\),

\[
\boxed{h(p)\le h(x)-2.}
\]

Thus

\[
\boxed{
\begin{array}{c}
x\text{ WIN},\quad \ell\text{ LOSS},\quad
y\in\operatorname{moves}(d),\quad d\text{ DRAW}\\[2mm]
\Longrightarrow\
y\text{ is a boundary WIN},\quad\text{or}\quad
\bigl(x\text{ exceptional}\bigr),\quad\text{or}\quad
\text{a strict height descent}.
\end{array}}
\]

Apply this lemma to Section 40.  In every alternative, the relevant
\((x,\ell,y,d)\) is one of

\[
\begin{array}{c|c|c|c}
&x&\ell&y\\ \hline
j=3&S_1&D&C\\
   &S_2&C&T_1\\
j=4&S_2&C&T_1\\
   &S_3&T_1&T_2\\
j=5&S_3&T_1&T_2\\
   &S_4&T_2&T_3.
\end{array}
\]

The DRAW state \(d\) is respectively the upper ladder member that contains
\(y\).  Therefore every nonexceptional row either exposes a new boundary
WIN immediately or strictly lowers its endpoint height.

Only two constant-tail levels in this table can be exceptional.  Since
\(J(W)\) is odd,

\[
\begin{aligned}
S_1\text{ exceptional}&\Longrightarrow
S_1\bmod16\in\{1,14\},\\
S_2\text{ exceptional}&\Longrightarrow
S_2\bmod16\in\{3,12\},
\end{aligned}
\]

whereas \(S_3\bmod16\in\{7,8\}\), and
\(S_4\bmod16\in\{0,15\}\).  Consequently the residual DRAW continuation in
the \(v=4\), \(j=3,4,5\) ladders is confined to the four explicit rows

\[
\boxed{S_1\equiv1,14\pmod {16}\quad\text{or}\quad
S_2\equiv3,12\pmod {16}.}
\]

All branches through a LOSS witness \(T_1\) or \(T_2\) are
nonexceptional and hence satisfy the boundary/strict-descent dichotomy
without a residue scan.  The residue classification and all side identities
are regression-tested.

## 42. The exceptional valuation-four rows have bounded source lifts

The \(S_1\)-exception in Section 41 is impossible under the minimum-source
hypothesis.  It occurs only in the \(j=3\) row, where the residual
alternative makes

\[
C=B(S_1)
\]

DRAW.  Write \(a=J(W)\).  Since \(S_1=Q_1^e(a)\) is exceptional, the
alternating suffix of \(A(S_1)\) has length at least three.  Therefore, for
positive \(C\), its coefficient source \(\rho(C)\) satisfies

\[
\rho(C)\le\frac{C-1}{6}<\frac{a}{16}.
\]

The \(j=3\) signed identity and the bounds already used in Section 36 give

\[
a\le\frac{3J(Z)+1}{8}
\le\frac{162t+115}{8},\qquad
t\le\frac{81s-28}{128}.
\]

Consequently

\[
\rho(C)<\frac{162t+115}{128}
\le\frac{13122s+10184}{16384}<s,
\]

where the last inequality holds for every residual source \(s\ge10\).
This contradicts global source minimality.  The case \(C=0\) is even more
immediate because a terminal state cannot be DRAW.  Thus no \(S_1\)
exception survives.

It remains to normalize an exceptional \(S_2\).  Put

\[
x=S_2=Q_2^e(a),\qquad C=B(x),\qquad y=A(x),\qquad p=B(y).
\]

The only possibilities are \(x\equiv12\pmod {16}\) for \(e=0\), and
\(x\equiv3\pmod {16}\) for \(e=1\).  In both cases

\[
p=\frac{9a-1}{2}.
\]

Moreover \(p\) has the exact source form

\[
\boxed{p=Q_k^{1-e}(J(C)),\qquad k\ge1.}
\]

For \(e=0\), the exceptional congruence gives \(a\equiv3\pmod4\).
Deleting one final one bit from \(9a\) does not change its constant-tail
coefficient, while Section 18 gives
\(\kappa(9a)=J(R(3a))=J(C)\).  For \(e=1\), one has
\(a\equiv1\pmod4\); deleting one final zero bit from \(9a-1\) again
preserves its coefficient, and Section 18 gives
\(\kappa(9a-1)=J(R(3a-1))=J(C)\).  The parity of \(p\) is \(1-e\), proving
the box.

In the residual alternative \(y\) is DRAW.  If \(p\) is WIN, it is already
a boundary endpoint.  If \(p\) is DRAW, minimum source forces \(C\ge s\).
Using

\[
2^kJ(C)=p+1-e\le\frac{9a+1}{2}
\]

together with the preceding bounds for \(a,t\) gives the finite limits

\[
\boxed{
\begin{array}{c|c}
j& p\text{ DRAW}\\ \hline
3&k\le4,\\
4&k\le3.
\end{array}}
\]

For example, if \(j=3\) and \(k\ge5\), then

\[
32(3s+1)\le2^kJ(C)
\le\frac{9a+1}{2}
\le\frac{1458t+1043}{16},
\]

which contradicts \(t\le(81s-28)/128\).  With \(j=4\), the last
upper bound becomes \((1458t+1051)/32\), and already \(k\ge4\) is
impossible.

Hence every exceptional \(v=4\) DRAW continuation is an exponent-at-most-
four constant-tail state over an explicit ordinary LOSS source \(C\).
The source identity, the strict \(S_1\) source drop, and both exponent bounds
are regression-tested in the actual residual trajectory.

## 43. The valuation-four \(j=2\) boundary returns to a bounded WIN source

It remains to normalize the exponent-zero row omitted from Section 37.
Keep \(a=J(W)\).  The \(j=2\) signed identity at \(Z\) gives

\[
3J(Z)+1-2g=4a.
\]

Since \(M=A(Z)\) is LOSS, its two children are WIN.  They have the exact
form

\[
\boxed{
E=A(M)=a-e=Q_0^e(a),\qquad
R=B(M)=R(a-e).
}
\]

The transferred upper pair is \(S_2,S_1\), so it is again the exact
obligation \(O(W,e)\).  Crucially, the phase \(e\) at \(W\) selects the
ordinary WIN source \(R\):

\[
\boxed{\operatorname{selected}_e(W)=R=B(M).}
\]

For a direct proof, write \(T=J(t)\).  From
\(Z=Q_1^e(3T)=6T-e\), the valuation-two equation gives

\[
a=J(W)=\frac{27T+1-2e}{2},
\qquad
M=9T-e,
\qquad
A(M)=a-e.
\]

For every odd \(a\), the odd coefficient of the signed expression
\(3a+1-2e\) is \(J(R(a-e))\).  When \(e=0\), this is the first coefficient
identity of Section 18 after deleting the final one bit; when \(e=1\), it
is its zero-bit symmetric form.  Section 17 then identifies the selected
ordinary source as \(R(a-e)=B(M)\), proving the box.

The same valuation condition leaves only

\[
\boxed{Z\bmod16\in\{2,5,10,13\}.}
\]

Thus \(Z\) is nonexceptional.  Its ordinary side relation makes
\(R=B(A(Z))\) the corresponding child of \(W=B(Z)\).  Since \(R\) is a
child of the LOSS state \(M\), it is WIN.  The other ordinary child of the
WIN state \(W\) is consequently LOSS.  More precisely, the four rows are

\[
\begin{array}{c|c|c}
Z\bmod16&e\text{ selects at }W&R\\ \hline
2,13&B&B(W),\\
5,10&A&A(W).
\end{array}
\]

Finally this returned WIN source is numerically bounded.  Section 36 gives
\(t\le(81s-28)/128\), while

\[
J(W)=\frac{27J(t)+1-2e}{2}\le\frac{81t+55}{2}.
\]

Using \(J(W)\ge3W+1\) yields

\[
W\le\frac{6561s+4516}{768}<10s
\qquad(s\ge10).
\]

If the phase at \(W\) is already A-selecting, the residual object is an
A-selecting obligation whose selected ordinary source is the explicit WIN
\(R\), with a retained LOSS sibling.  If it is B-selecting, Section 27
preserves the exact obligation when the signed valuation is two.  Every
such transfer satisfies

\[
x_{i+1}\le\frac{3x_i+1}{4}.
\]

Starting from \(x_0=W<10s\), nine such transfers give

\[
x_9\le1+\left(\frac34\right)^9(W-1)<s.
\]

Therefore at most eight B-source transfers can survive before the source
drops below \(s\) or the A-selecting phase is reached.

There is one necessary qualification.  A B-selecting valuation at least
three transfers the DRAW to a higher adjacent frame rather than preserving
\(O\).  This exit is still finite here.  If its selected source \(y\)
survives with \(y\ge s\), then

\[
2^jJ(y)=3J(x)+1-2\epsilon<90s+7
\qquad(x<10s).
\]

Since \(J(y)\ge3s+1\), a valuation \(j\ge5\) is impossible.  Thus every
surviving B-phase step has exactly one of the forms

\[
\boxed{
j=2\text{ and }O\text{ is preserved},\qquad
j=3,4\text{ and the process enters a finite exponent-}2,3\text{ frame}.}
\]

The \(j=2\) branch therefore has no unbounded B escape: after at most eight
preserving transfers it reaches the A-phase, drops below \(s\), or enters
one of the two finite adjacent frames.  All exact identities, residue rows,
valuation bounds, and the source bound are regression-tested.

## 44. The A-selecting half of the \(j=2\) return is a one-sided descent

In the A-selecting rows \(Z\equiv5,10\pmod {16}\) of Section 43, write

\[
P=Q_1^e(J(W)),\qquad U=Q_2^e(J(W)),\qquad
q=B(P)=B(U).
\]

The exact obligation \(O(W,e)\) makes \(q\) non-losing and makes it a child
of at least one DRAW member among \(P,U\).  Section 24 also makes the same
\(q\) an ordinary child of the selected source

\[
R=A(W),
\]

which is WIN by Section 43.

If \(q\) is WIN, it is immediately the endpoint of a boundary edge from the
DRAW member.  If \(q\) is DRAW, the other ordinary child of the WIN state
\(R\) must be LOSS.  Section 41 now applies with \(x=R\), \(y=q\), and the
DRAW member of the obligation as the second parent.  Hence

\[
\boxed{
\begin{array}{c}
v=4,\ j=2,\ e=\alpha(W)\\
\Longrightarrow\
q\text{ is a boundary WIN},\quad\text{or}\quad
R\text{ is exceptional},\quad\text{or}\quad
\text{a boundary endpoint of height at most }h(R)-2.
\end{array}}
\]

Thus the only DRAW continuation in the A-selecting half has
\(R\bmod16\in\{1,3,12,14\}\).  The B-selecting half is already covered by
Section 43: it either drops below \(s\), reaches this A-selecting form, or
enters an exponent-two/three frame after a bounded number of
valuation-two transfers.  The common-child occurrence under \(R\) is
regression-tested.

## 45. The \(r=2\), \(v=3,4\) opposite LOSS is a known finite ladder

Return to the exponent-two factor switch of Sections 30 and 32.  Put

\[
a=J(b),\qquad
X=Q_1^g(3a)\text{ DRAW},\qquad
E=Q_2^e(a)\text{ WIN},\qquad
L=A(E)=Q_1^e(3a),
\]

where \(g=1-e\).  Write the signed transition at \(X\) as

\[
9a+1-2g=2^vJ(t),\qquad v\le4.
\]

For every \(v\ge3\), the opposite twin has the exact contracting child

\[
\boxed{B(L)=Q_{v-2}^e(J(t)).}
\]

Indeed, the opposite signed expression differs by two:

\[
9a+1-2e=2^vJ(t)+2(2g-1).
\]

Its valuation is one.  The expanding child \(A(L)\) is obtained by
appending the two-bit word \(10\) when \(g=0\), and \(01\) when \(g=1\),
to \(Q_{v-2}^e(J(t))\).  Since \(v-2\ge1\), the leading appended bit
repeats the existing final \(e\)-bit, so deleting the maximal alternating
suffix removes exactly those two appended bits and proves the box.

The lower state \(B(L)\) is WIN except possibly when \(E\) itself is
exceptional.  Indeed, because \(E\) is WIN, at least one of \(L,B(E)\) is
LOSS.  If \(L\) is LOSS, this is immediate.  Otherwise \(B(E)\) is LOSS.
When \(E\) is nonexceptional, the ordinary side relation makes
\(B(L)=B(A(E))\) a child of \(B(E)\), so it is again WIN.  Thus the only
unresolved orientation at this step has

\[
\boxed{E\bmod16\in\{3,12\}.}
\]

Outside these two rows, the two possible valuations are exactly the finite
ladders already analyzed in Sections 40--41.

For \(v=3\), the DRAW state \(X\) has children

\[
Q_3^e(J(t)),\qquad Q_2^e(J(t)),
\]

while the lower state \(Q_1^e(J(t))=B(L)\) is WIN.  If the exponent-two
member is DRAW, the other child of the lower WIN is LOSS; if it is WIN,
the exponent-three member is DRAW and the common side child is LOSS.  This
is precisely the \(j=3\) split of Section 40.

For \(v=4\), the children of \(X\) are

\[
Q_4^e(J(t)),\qquad Q_3^e(J(t)),
\]

and \(Q_2^e(J(t))=B(L)\) is WIN.  If the exponent-three member is DRAW, its
lower common child forces the boundary side of \(Q_2^e\) to be LOSS.  If
it is WIN, the exponent-four member is DRAW and
\(Q_1^e(3J(t))\) is LOSS.  This is the \(j=4\) split; the second lower WIN
used in Section 40 is not needed for this dichotomy.

Applying the one-sided lemma of Section 41 in each row gives

\[
\boxed{
\begin{array}{c}
r=2,\quad v=3,4,\quad E\text{ nonexceptional}\\
\Longrightarrow\
\text{a boundary WIN},\quad\text{or a strict height descent},\quad
\text{or an exceptional lower WIN state}.
\end{array}}
\]

Besides an exceptional \(E\), the only possible exceptional lower states
are

\[
v=3:\quad Q_1^e(J(t))\equiv1,14
\ \text{or}\ Q_2^e(J(t))\equiv3,12\pmod {16},
\]

and

\[
v=4:\quad Q_2^e(J(t))\equiv3,12\pmod {16}.
\]

The exponent-three state is always \(7\) or \(8\) modulo \(16\), so it is
never exceptional.  Thus the high half of the \(r=2\) twin switch contains
no new outcome geometry: it is the same finite ladder, plus the exceptional
rows \(E\equiv3,12\) and the same lower \(S_1/S_2\) rows already isolated
for \(r=3\).  The twin return, side-child occurrence, and all constant-tail
coordinates are regression-tested.

## 46. The exceptional \(E\) in the \(r=2\) switch is a bounded LOSS-source lift

It remains to normalize the orientation exception
\(E\equiv3,12\pmod {16}\) from Section 45.  Put

\[
C=B(E),\qquad L=A(E),\qquad p=B(L).
\]

The unresolved orientation has \(C\) LOSS.  Write again \(a=J(b)\), so
\(E=Q_2^e(a)\).  The same exceptional-\(S_2\) calculation as in Section 42
gives

\[
\boxed{
p=Q_k^{1-e}(J(C)),\qquad k\ge1,\qquad
p=\frac{9a-1}{2}.}
\]

Indeed, \(E\equiv12\) forces \(e=0,a\equiv3\pmod4\), while
\(E\equiv3\) forces \(e=1,a\equiv1\pmod4\).  In the first case the
constant-tail coefficient of \(p\) is
\(\kappa(9a)=J(R(3a))=J(C)\); in the second it is
\(\kappa(9a-1)=J(R(3a-1))=J(C)\).  The final bit is \(1-e\).

The exponent-two factor bound from Section 32 says

\[
b\le\frac{27s-8}{12},
\]

and hence

\[
a=J(b)\le3b+2\le\frac{27s}{4}.
\]

Because \(k\ge1\),

\[
2J(C)\le p+1-e\le\frac{9a+1}{2},
\]

which gives the strict source window

\[
\boxed{C<\frac{81}{16}s.}
\]

If \(p\) is DRAW, global source minimality additionally forces \(C\ge s\).
Then \(k\ge4\) would imply

\[
16(3s+1)\le2^kJ(C)=p+1-e
\le\frac{243s+4}{8},
\]

an impossibility.  Therefore

\[
\boxed{p\text{ DRAW}\quad\Longrightarrow\quad
s\le C<\frac{81}{16}s,\qquad k\le3.}
\]

If \(L\) is DRAW and \(p\) is WIN, the edge \(L\to p\) is already a new
boundary.  If both remain DRAW, the continuation is one of only three
constant-tail levels over the explicit LOSS source \(C\).  If \(L\) is
WIN, the same exact lift still records its side outcome, so no unbounded
valuation is hidden in the exceptional orientation.  Thus all
\(r=2,\ v=3,4\) branches are reduced to boundary/height alternatives or
finite exponent-at-most-three LOSS-source lifts.  The source identity,
window, and exponent bound are regression-tested.

## 47. The \(r=2\) valuations one and two have bounded source returns

Keep the notation of Sections 45--46:

\[
X=Q_1^g(3J(b))\text{ DRAW},\qquad
9J(b)+1-2g=2^vJ(t),
\]

with \(b<9s/4\).  The two low signed valuations have exact normal forms.

### Valuation two

If \(v=2\), then

\[
\boxed{
A(X)=Q_2^e(J(t)),\qquad
B(X)=Q_1^e(J(t)).}
\]

The first equality is the signed boundary formula.  The first state ends
in two equal \(e\)-bits, so applying the raw suffix deletion in the
definition of \(B(X)\) removes exactly one bit and proves the second.
Because \(X\) is DRAW, its two children are non-losing and at least one is
DRAW.  They are therefore exactly the second alternative of the obligation

\[
\boxed{O(t,e).}
\]

The source is bounded.  Section 32 gives
\(J(b)\le3b+2\le27s/4\), and hence

\[
J(t)\le\frac{9J(b)+1}{4}\le\frac{243s+4}{16}.
\]

Using \(J(t)\ge3t+1\) yields

\[
\boxed{t<\frac{81}{16}s.}
\]

Thus valuation two returns directly to the already studied obligation
automaton in a fixed source window.

### Valuation one

If \(v=1\), put

\[
P=A(X)=Q_1^e(J(t)),\qquad K=B(X)=R(P).
\]

Again \(P,K\) are non-losing and at least one is DRAW.  If \(P\) is DRAW,
the first alternative of \(O(t,e)\) holds.  If \(P\) is WIN, then \(K\)
must be DRAW.  This second possibility is not silently identified with a
source lift: \(K\) uses the raw alternating-suffix deletion, and may have
a different canonical coefficient source.

The two possible sources are nevertheless bounded.  First,

\[
J(t)\le\frac{9J(b)+1}{2}\le\frac{243s+4}{8},
\]

so

\[
\boxed{t<\frac{81}{8}s.}
\]

Second, the exponent-one word \(P=Q_1^e(J(t))\) always ends in a two-bit
alternating suffix: the bit before its final \(e\)-bit is \(1-e\).
Consequently

\[
K=R(P)\le\frac{P}{4}\le\frac{J(t)}2.
\]

If \(u\) is the coefficient source of a positive \(K\), then
\(u\le(K-1)/6<K/6\).  Therefore

\[
\boxed{
K\text{ DRAW}\quad\Longrightarrow\quad
s\le u<\frac{243s+4}{96}.}
\]

The lower bound is global source minimality.  Hence valuation one either
returns to \(O(t,e)\) with \(t<81s/8\), or makes a raw-side DRAW return whose
coefficient source is below \(81s/32+1/24\).  Together with Sections 45--46,
this gives a finite source/exponent normalization for every \(r=2\)
continuation.  All coordinate identities and bounds are regression-tested.

## 48. The exponent-one factor switch has three bounded continuation types

Return to the \(r=1\) factor switch of Section 31.  Put

\[
b=A^2(x),\qquad a=J(b),\qquad
G=Q_1^g(a),\qquad H=Q_2^g(a),
\]

and suppose their common child

\[
X=B(G)=B(H)
\]

is DRAW.  Section 31 already proves that the signed phase \(g\) at \(b\)
has only three source-surviving forms.

### A-selecting phase

If \(g=\alpha(b)\), the coefficient source \(\rho(X)\) satisfies

\[
\boxed{s\le\rho(X)<x.}
\]

The upper inequality is Section 31; the lower one follows from global
source minimality because \(X\) is DRAW.  Thus every A-selecting \(r=1\)
continuation strictly decreases the source relative to the obligation
source \(x\) that created the factor fork.

### B-selecting valuation two

Let \(y=B(b)\).  If the signed valuation is two, the exact boundary formula
and one-bit raw deletion give

\[
A(G)=Q_2^e(J(y)),\qquad
X=B(G)=Q_1^e(J(y)).
\]

Consequently

\[
\boxed{O(y,e)}
\]

holds through its first alternative.  Section 31 gives

\[
\boxed{s\le y<\frac{27}{8}s}
\]

whenever this source survives.  Thus valuation two is a direct return to
the existing obligation automaton.

### B-selecting valuation three

For valuation three the common DRAW has the exact form

\[
\boxed{X=Q_2^e(J(y)),\qquad s\le y<\frac{27}{16}s.}
\]

Put

\[
C=B(X)=B(Q_1^e(J(y))),\qquad F=A(X)=Q_1^e(3J(y)).
\]

The common-boundary coefficient estimate of Section 15 gives, for the
coefficient source \(u=\rho(C)\),

\[
\boxed{u\le\frac{3y+1}{4}
<\frac{81s+16}{64}.}
\]

Since \(X\) is DRAW, \(C,F\) are non-losing and at least one is DRAW.  If
\(C\) is DRAW, minimum source also gives \(u\ge s\), so this is a raw-side
return in the narrow interval

\[
s\le u<\frac{81s+16}{64}.
\]

If \(C\) is WIN, the other child \(F\) is forced DRAW.  This is one explicit
exponent-one factor state with source \(y<27s/16\); it contains no
unbounded suffix or source choice.

We have therefore proved the finite trichotomy

\[
\boxed{
r=1,\ X\text{ DRAW}\Longrightarrow
\begin{cases}
\rho(X)<x,&g\text{ A-selecting},\\
O(y,e),\ y<27s/8,&g\text{ B-selecting},\ j=2,\\
Q_2^e(J(y))\text{ DRAW},\ y<27s/16,&g\text{ B-selecting},\ j=3.
\end{cases}}
\]

The last row either returns through a source below
\((81s+16)/64\) or enters the displayed exponent-one factor state.
All source coordinates and inequalities are regression-tested.

## 49. The low contracting continuations of \(r=3\) return near the minimum source

Return to the exponent-three factor switch of Section 32.  Write

\[
a=J(b),\qquad
X=Q_2^g(3a)\text{ DRAW},\qquad
G=Q_1^g(3a),
\]

and suppose the shared contracting child

\[
K=B(X)=B(G)
\]

is DRAW.  Factor

\[
9a+1-2g=2^vJ(t).
\]

Section 32 proves \(v\le3\).  The factor-source bound there also gives

\[
b\le\frac{9s-4}{8},\qquad
a=J(b)\le\frac{27s+4}{8},
\]

and therefore

\[
9a+1\le\frac{243s+44}{8}.
\]

The three valuations now have exact forms.

### Valuation three

Here

\[
A(G)=Q_3^e(J(t)),\qquad
K=B(G)=Q_2^e(J(t))\text{ DRAW}.
\]

Moreover

\[
\boxed{t<\frac{243s+44}{192}.}
\]

Thus the exponent-two DRAW returns with source only slightly above the
global minimum.

### Valuation two

Now

\[
A(G)=Q_2^e(J(t)),\qquad
K=Q_1^e(J(t))\text{ DRAW}.
\]

The latter is the first alternative of the exact obligation

\[
\boxed{O(t,e),\qquad
t<\frac{243s+44}{96}.}
\]

### Valuation one

Put

\[
P=A(G)=Q_1^e(J(t)).
\]

The DRAW child is the raw side

\[
K=R(P).
\]

The source itself satisfies

\[
t<\frac{243s+44}{48}.
\]

As in Section 47, the word \(P\) has an alternating suffix of length at
least two, so \(K\le P/4\le J(t)/2\).  If \(u\) is the coefficient source
of the positive DRAW state \(K\), then

\[
\boxed{s\le u<\frac{243s+44}{192}.}
\]

Consequently every contracting-DRAW continuation of the low \(r=3\) switch
either returns to an obligation below roughly \(2.54s\), or returns a
single exponent-two/raw-side DRAW whose coefficient source is below roughly
\(1.27s\).  No low contracting row contains an unbounded exponent or source
jump.  The exact coordinates and all three bounds are regression-tested.

## 50. The low expanding continuations of \(r=3\) are finite adjacent frames

Keep the exponent-three notation of Section 49, but now suppose the common
contracting child \(K=B(X)\) is WIN.  Since

\[
X=Q_2^g(3J(b))
\]

is DRAW, its other child

\[
Y=A(X)=Q_1^g(9J(b))
\]

is DRAW.  Factor its signed transition as

\[
27J(b)+1-2g=2^wJ(u).
\]

Section 32 proves that every source-surviving transition has \(w\le4\).
The same source bound as in Section 49 gives

\[
J(b)\le\frac{27s+4}{8},
\qquad
27J(b)+1\le\frac{729s+116}{8}.
\]

Therefore, for every \(w\ge1\),

\[
\boxed{u<\frac{729s+116}{24\cdot2^w}.}
\]

The outcome normal forms are now explicit.

### Valuations two, three, and four

For \(w\ge2\), the two children of \(Y\) are the adjacent frame

\[
\boxed{
Q_w^e(J(u)),\qquad Q_{w-1}^e(J(u)).}
\]

They are non-losing and at least one is DRAW.  In particular:

- \(w=2\) is exactly the second alternative of \(O(u,e)\), with
  \(u<(729s+116)/96\);
- \(w=3\) is the exponent-three/two frame with
  \(u<(729s+116)/192\);
- \(w=4\) is the exponent-four/three frame with
  \(u<(729s+116)/384\).

These are precisely the finite adjacent frames already treated by the
ladder and factor reductions; no additional suffix type appears.

### Valuation one

Put

\[
P=A(Y)=Q_1^e(J(u)),\qquad Z=B(Y)=R(P).
\]

Both are non-losing and at least one is DRAW.  If \(P\) is DRAW, the first
alternative \(O(u,e)\) holds, with

\[
u<\frac{729s+116}{48}.
\]

If \(P\) is WIN, then \(Z\) is DRAW.  Its coefficient source \(\rho(Z)\)
is much smaller.  The word \(P\) has an alternating suffix of length at
least two, so

\[
Z\le\frac{P}{4}\le\frac{J(u)}2,
\qquad
\rho(Z)<\frac{J(u)}{12}
\le\frac{729s+116}{192}.
\]

Thus

\[
\boxed{
Z\text{ DRAW}\quad\Longrightarrow\quad
s\le\rho(Z)<\frac{729s+116}{192}.}
\]

Combining both outcome branches, every low expanding \(r=3\) continuation
is an obligation or an adjacent frame of exponent at most four, with the
displayed constant source windows, or a raw-side DRAW whose source is below
roughly \(3.80s\).  Together with Sections 33--39 and 49, this exhausts all
signed valuations following the \(r=3\) factor switch.  All coordinates and
source bounds are regression-tested.

## 51. A minimum-height factor endpoint carries a two-WIN barrier

The retained LOSS state in the factor fork gives a clean height certificate
when the corresponding boundary endpoint is itself chosen at global minimum
height.  Keep the factor alternative of Section 28.  Thus some DRAW state
\(K\) has children \(U,P\), and the forced outcomes are

\[
P,b\text{ WIN},\qquad U,F\text{ DRAW},\qquad V\text{ LOSS},
\]

where the two children of \(P\) are exactly \(V,b\).  In particular, \(P\)
is the WIN endpoint of the boundary edge \(K\mathbin{\to}P\), and \(V\) is
its unique LOSS child.

Put

\[
E=A(V),\qquad D=B(V).
\]

Both \(E,D\) are WIN because \(V\) is LOSS.  The canonical height equations
give

\[
h(P)=1+h(V)
\]

and

\[
h(E),h(D)\le h(V)-1=h(P)-2.
\]

Now suppose \(h(P)\) is the global minimum of the heights of all WIN
endpoints of DRAW-to-WIN boundary edges.  No DRAW position can have \(E\)
or \(D\) as a child: such an edge would be another boundary whose WIN
endpoint has height at most \(h(P)-2\).  Hence

\[
\boxed{
h(P)\text{ globally minimum}
\quad\Longrightarrow\quad
\text{every parent of }E\text{ or }D\text{ is non-DRAW}.}
\]

This is the exact height information that a recursive factor-switch graph
must retain.  It is stronger than knowing only that \(V\) is LOSS, because
it constrains every arithmetic diamond that later meets either child of
\(V\).

The qualification is essential.  A factor occurrence reached later from a
minimum-source trajectory makes \(P\) a boundary endpoint, but it does not
by itself prove that \(h(P)\) equals the global minimum boundary height.
Thus the boxed barrier cannot simply be attached to every factor fork.
A completion must either transport the originally minimum endpoint through
the return graph or prove a genuine height descent before restarting the
argument.

## 52. The \(r=2,3\) factor source is a two-sided ordinary return

The source \(x\) in the final A-selecting obligation carries more
game-theoretic information than was used in Sections 28--50.  First, it is
itself a finite-outcome position.  Indeed, Section 28 has

\[
s\le x<2s.
\]

For every positive state \(q\), its coefficient source satisfies
\(\rho(q)\le(q-1)/6\).  Consequently

\[
\rho(x)\le\frac{x-1}{6}<s.
\]

Global source minimality therefore excludes \(x\) from DRAW:

\[
\boxed{x\text{ is WIN or LOSS}.}
\]

Now retain the factor alternative and its lower exponent \(r\).  Put
\(y=A(x)\), \(e=\alpha(x)\), and \(g=1-e\).  The state

\[
V=Q_1^g(J(y))
\]

has expanding child

\[
A(V)=Q_r^e(J(b)).
\]

This is exactly the signed source transition at \(y\) in phase \(g\).
Its valuation is \(r\), and its selected ordinary source is \(b\).
Section 17 therefore gives the dichotomy

\[
\boxed{
r=1\Longrightarrow b=A^2(x),\qquad
r\ge2\Longrightarrow b=B(A(x)).}
\]

The first identity recovers Section 31.  In the second case, \(x\) is
necessarily nonexceptional.  Direct substitution in the four exceptional
classes \(1,3,12,14\pmod {16}\) shows that \(g=\alpha(A(x))\), so the
transition at \(A(x)\) would instead have valuation one.

Suppose now that \(r\ge2\) and \(x\) is WIN.  The value
\(b=B(A(x))\) is directly a child of \(A(x)\).  Since \(x\) is
nonexceptional, the ordinary side relation makes the same \(b\) a child of
\(B(x)\).  Let \(\ell\) be a LOSS child realizing the canonical height of
\(x\).  Whichever of \(A(x),B(x)\) is \(\ell\), the value \(b\) is its
WIN child.  Hence

\[
\boxed{h(b)\le h(x)-2.}
\]

In the factor alternative \(U\) is DRAW and \(b=B(U)\) is WIN, so \(b\) is
also a boundary endpoint.  Thus every \(r=2,3\) factor fork whose ordinary
source \(x\) is WIN already pays a strict proof-height descent from \(x\).
The unresolved orientation is correspondingly sharper: it is enough to
transport provenance through the case where \(x\) is LOSS, together with
the one-sided \(r=1\) return \(b=A^2(x)\).

## 53. The exponent-one factor return selects a LOSS source

The exponent-one switch retains more outcome information than the source
bounds of Sections 31 and 48 record.  Keep the factor alternative of
Sections 28--30, let

\[
u=A(x),\qquad b=A(u)=A^2(x),\qquad c=B(u),
\]

and retain \(g=1-\alpha(x)=\alpha(u)\).  Thus

\[
V=L_g(u)\text{ is LOSS},\qquad b\text{ is WIN}.
\]

Put

\[
D=B(V),\qquad G=L_g(b),\qquad X=B(G)=B(Q_2^g(J(b))).
\]

There is an exact nested-source identity:

\[
\boxed{
D=
\begin{cases}
B(b),&g=\alpha(b),\\
A(b),&g=1-\alpha(b).
\end{cases}}
\]

In words, \(D\) is the ordinary child of \(b\) not selected by phase
\(g\).  To prove this, apply the refined formula of Section 24 to
\(V=L_g(u)\).  The condition \(g=\alpha(u)\), together with the
exponent-one condition \(g=1-\alpha(x)\), leaves

\[
x\equiv1,3,4,6,9,11,12,14\pmod {16}.
\]

Substitution in these eight rows shows that \(A(b)\bmod2=1-g\) in the
four rows where \(g=\alpha(b)\), and \(A(b)\bmod2=g\) in the other four.
Section 24 then gives exactly the boxed identity.  No unbounded suffix is
being decided by this residue calculation.

Because \(V\) is LOSS, \(D\) is WIN.  The state \(b\) is also WIN, so its
other, phase-selected child must be LOSS.  This immediately resolves the
A-selecting continuation.  If \(g=\alpha(b)\), then \(A(b)\) is LOSS and
Section 24 makes \(X=B(L_g(b))\) one of its children.  Hence

\[
\boxed{X\text{ is WIN},\qquad h(X)\le h(b)-2.}
\]

At least one of the two factor-frame parents of \(X\) is DRAW, so \(X\)
is a new boundary endpoint.  In particular the A-selecting, \(X\)-DRAW
row of Section 48 is arithmetically possible in isolation but impossible
with the retained factor outcomes.

It remains to consider \(g=1-\alpha(b)\).  Now the selected ordinary
source

\[
\boxed{y=B(b)}
\]

is LOSS.  The four possible residue classes are

\[
x\equiv4,6,9,11\pmod {16},
\]

so \(x\) is nonexceptional.  Consequently \(c=B(A(x))\) is a child of
both \(u=A(x)\) and \(B(x)\).  The factor outcome \(b=A(u)\) WIN now gives
the following exact outcome and height return:

\[
\boxed{
\operatorname{outcome}(c)=\operatorname{outcome}(x),\qquad
h(c)\le h(x)-2.}
\]

Indeed, if \(x\) is LOSS, then \(u\) and \(B(x)\) are WIN.  Since \(u\)
has the WIN child \(b\), its other child \(c\) is LOSS, and
\(h(c)=h(u)-1\le h(x)-2\).  If \(x\) is WIN and \(u\) were WIN, then
\(c\) would be LOSS while \(B(x)\) would also be LOSS.  This contradicts
the fact that \(c\) is a child of the LOSS state \(B(x)\).  Thus \(u\) is
LOSS and \(c\) is WIN.  If \(B(x)\) is WIN, \(u\) is the only LOSS child
of \(x\); if \(B(x)\) is also LOSS, \(c\) is a child of both LOSS children.
The canonical height recursion gives the displayed bound in either case.

The next split is finite.  The B-selecting condition at \(b=A(u)\) forces

\[
u\equiv1,6,9,14\pmod {16}.
\]

For \(u\equiv6,9\pmod {16}\), the state \(u\) is nonexceptional and the
side relation makes the LOSS state \(y=B(A(u))\) a child of \(c=B(u)\).
Therefore \(c\) cannot be LOSS, and the preceding box forces \(x\) to be
WIN.  Direct evaluation of the signed valuation gives \(j\ge3\); the
source-survival bound of Section 31 then leaves exactly \(j=3\).

For \(u\equiv1,14\pmod {16}\), the state \(u\) is exceptional and the
signed valuation is exactly \(j=2\).  The returned LOSS source is a
constant-tail lift over the lower-height state \(c\):

\[
\boxed{y=Q_m^\delta(J(c))\quad\text{for some }m\ge1,}
\]

with no factor of three in its coefficient.  Here is a general identity
that proves the claim.  For every \(z\ge0\), if \(R(z)\) is its alternating
suffix remainder, then

\[
\boxed{
3z+1=Q_m^{\,1-(z\bmod2)}(J(R(z)))
\quad\text{for some }m\ge1.}
\]

Write \(z\) as its prefix \(R(z)\) followed by its maximal alternating
suffix.  Multiplication of that suffix by three and addition of one turns
it into a constant terminal block; the remaining odd coefficient is
(3R(z)+1+(R(z)\bmod2)=J(R(z))\).  If the whole word is alternating, the
constant block is one bit longer and the same formula holds with
\(R(z)=0\).  This proves the identity.  In the two exceptional rows,

\[
\begin{array}{c|c|c}
u&c=B(u)&y=B(A(u))\\ \hline
16t+1&R(6t)&18t+1=3(6t)+1,\\
16t+14&R(6t+5)&18t+16=3(6t+5)+1,
\end{array}
\]

so the boxed lift follows.

Combining these facts sharpens Section 48 to the type-sensitive dichotomy

\[
\boxed{
r=1,\ X\text{ DRAW}\Longrightarrow
\begin{cases}
j=3,\ x\text{ WIN},\ y\text{ LOSS},\ y\in\operatorname{moves}(c),
&u\text{ nonexceptional},\\
j=2,\ y\text{ LOSS},\ y=Q_m^\delta(J(c)),
&u\text{ exceptional},
\end{cases}}
\]

where in both rows \(c\) has the same finite outcome as \(x\) and
\(h(c)\le h(x)-2\).  Thus the only exponent-one continuation not already
paying a boundary-height descent is an exact LOSS-source return carrying a
strictly lower finite witness; its sole failure of the ordinary side
diamond is the displayed exceptional constant-tail lift.

## 54. The second factor coefficient has three exact ordinary sources

The signed transitions following the \(r=2,3\) factor switch have a
universal source trichotomy that is hidden by the numerical bounds in
Sections 32 and 45--50.  Let \(b>0\), \(g\in\{0,1\}\), and factor

\[
9J(b)+1-2g=2^vJ(t).
\]

Then

\[
\boxed{
\begin{array}{c|c}
v&t\\ \hline
1&3A(b)+1,\\
2&A^2(b),\\
v\ge3&B(A(b)).
\end{array}}
\]

In the first row the returned ordinary state is itself an exact
constant-tail lift over \(B(b)\):

\[
\boxed{
t=3A(b)+1=Q_m^\delta(J(B(b)))
\quad\text{for some }m\ge1.}
\]

To prove the trichotomy, put \(w=A(b)\), so \(J(b)=2w+1\).  The signed
numerator is

\[
9J(b)+1-2g=2(9w+5-g).
\]

If its valuation is one, parity forces \(g=w\bmod2\), and direct
substitution gives

\[
J(t)=9w+5-g=J(3w+1).
\]

Thus \(t=3w+1\).  Section 53's identity for \(3z+1\), applied to
\(z=w=A(b)\), gives the displayed lift over
\(R(A(b))=B(b)\).

If \(v\ge2\), parity instead gives \(g=1-(w\bmod2)\).  After removing the
first factor two, one has

\[
9w+5-g
=3J(w)+1-2(w\bmod2).
\]

This is exactly a signed source transition at \(w=A(b)\), with valuation
\(v-1\).  Valuation one selects \(A(w)=A^2(b)\), while valuation at least
two selects \(B(w)=B(A(b))\), proving the remaining rows.

There is an immediate proof-height consequence in the last row.  Suppose
\(b\) is WIN and nonexceptional.  The value

\[
t=B(A(b))
\]

is a child of both ordinary children \(A(b)\) and \(B(b)\).  At least one
of those children is LOSS, and whichever LOSS child realizes the canonical
height of \(b\) has \(t\) as a WIN child.  Hence

\[
\boxed{
v\ge3,\quad b\text{ WIN and nonexceptional}
\Longrightarrow
t\text{ WIN},\qquad h(t)\le h(b)-2.}
\]

This applies directly to the \(v=3,4\) ladders following \(r=2\), and to
the corresponding low and high signed transitions following \(r=3\).
Valuation one is no longer an untyped raw source jump: it is an explicit
lift over the ordinary child \(B(b)\).  Valuation two remains the sole
one-sided row \(A^2(b)\).  These statements do not by themselves make
\(t\) a boundary endpoint; the adjacent DRAW frame over \(t\) must still
be coupled to the retained lower-height witness.

## 55. Valuation two returns in the opposite phase exactly off the exceptions

The one-sided row \(v=2\) of Section 54 also has a finite phase and outcome
normal form.  Retain

\[
9J(b)+1-2g=4J(t),\qquad
t=A^2(b),\qquad e=1-g.
\]

Direct reduction modulo \(16\) gives

\[
\boxed{
e=\alpha(t)
\quad\Longleftrightarrow\quad
b\equiv1,3,12,14\pmod {16}.}
\]

Thus an exceptional \(b\) returns an A-selecting obligation over
\(t=A^2(b)\), while every nonexceptional \(b\) returns in the B-selecting
phase.  This calculation uses only the exact condition \(v=2\) and the two
bits defining \(\alpha(t)\); it does not attempt to determine an unbounded
alternating suffix from a fixed modulus.

There is a useful outcome split in the nonexceptional rows.  Suppose \(b\)
is WIN and put

\[
w=A(b),\qquad z=B(b),\qquad
t=A(w),\qquad q=B(w)=B(A(b)).
\]

Section 54 gives

\[
q\text{ WIN},\qquad h(q)\le h(b)-2.
\]

Whenever the global minimum-source bounds make \(t\) finite, its outcome
determines that of \(w\):

\[
\boxed{
t\text{ WIN}\Longrightarrow w\text{ LOSS},\qquad
t\text{ LOSS}\Longrightarrow w\text{ WIN and }z\text{ LOSS}.}
\]

Indeed, if \(t\) is WIN, then both children \(t,q\) of \(w\) are WIN, so
\(w\) is LOSS.  If \(t\) is LOSS, then \(w\) is WIN.  Since its parent
\(b\) is WIN as well, the other child \(z\) of \(b\) must be LOSS.

The required finiteness holds in both valuation-two returns that use the
equation of Section 54.  In the \(r=2\) branch, Section 47 gives

\[
t<\frac{81}{16}s<6s.
\]

In the contracting \(r=3\) branch, Section 49 gives

\[
t<\frac{243s+44}{96}<3s
\]

for every residual \(s\ge10\).  Since every positive state \(r\) has
coefficient source at most \((r-1)/6\), both inequalities place the
coefficient source of \(t\) below the globally minimum DRAW source \(s\).
Consequently \(t\) is WIN or LOSS, never DRAW.

The valuation-two return is therefore no longer an untyped \(A^2\) jump.
Off the four exceptional classes it first enters a B-selecting obligation
over a known finite source, while carrying the strict lower WIN token
\(q=B(A(b))\).  On the four exceptional classes it enters the A-selecting
obligation directly.  The remaining work is to transport \(q\) through
the B-source transfer or normalize the exceptional A-selecting row.

## 56. One B-transfer closes the ordinary valuation-two ambiguity

Continue with the nonexceptional valuation-two row of Section 55.  Thus

\[
t=A^2(b),\qquad e=1-g=1-\alpha(t),
\]

and the obligation over \(t\) is B-selecting.  Put

\[
w=A(b),\qquad q=B(w)=B(A(b)),
\]

so Section 55 retains

\[
q\text{ WIN},\qquad h(q)\le h(b)-2.
\]

Factor the B-selecting transition at \(t=A(w)\) as

\[
3J(t)+1-2e=2^jJ(y),\qquad y=B(t),\qquad j\ge2,
\]

and put \(f=1-e\).  Section 25 transfers the DRAW to the adjacent frame

\[
Q_j^f(J(y)),\qquad Q_{j-1}^f(J(y)).
\]

The first transfer has only two source-surviving forms.  Direct reduction
modulo \(64\) proves

\[
\boxed{
\begin{array}{c|c|c}
&j&y\\ \hline
w\text{ exceptional}&2&
Q_m^\delta(J(q))\text{ for some }m\ge1,\\
w\text{ nonexceptional}&\ge3&
y\in\operatorname{moves}(q).
\end{array}}
\]

For the first row, use the four exceptional formulas of Section 5:
\(q=B(w)=R(z)\) and \(y=B(A(w))=3z+1\) in every row.  The universal
\(3z+1\) identity of Section 53 gives the displayed constant-tail source
and shows that no factor of three occurs.

For the second row, the ordinary side relation at \(w\) makes
\(y=B(A(w))\) a child of \(q=B(w)\).  The residue calculation is used only
to distinguish valuation exactly two from valuation at least three:
the former occurs precisely when \(w\) is exceptional.

The numerical bound removes every valuation above three.  In the \(r=2\)
branch Section 55 gives \(t<81s/16\), and the contracting \(r=3\) branch
has the stronger \(t<3s\).  Hence in either branch

\[
j\ge4
\Longrightarrow
y\le\frac{3t+1}{16}<s
\]

for every residual \(s\ge10\).  A DRAW frame cannot have source below
\(s\), so a surviving nonexceptional row has exactly \(j=3\).
Substitution in its four residue classes gives the sharper identity

\[
\boxed{y=A(q),\qquad
b\bmod64\in\{4,25,38,59\}.}
\]

Moreover

\[
y\le\frac{3t+1}{8}<2s,
\]

and \(y\) is finite because already \(y<t<6s\) gives
\(\rho(y)<s\).

We have therefore proved the exact return graph

\[
\boxed{
\begin{array}{c|c}
w=A(b)\text{ exceptional}&
O(y,f),\quad y=Q_m^\delta(J(q)),\\
w=A(b)\text{ nonexceptional}&
\{Q_3^f(J(A(q))),Q_2^f(J(A(q)))\}
\text{ contains a DRAW},
\end{array}}
\]

where in both rows \(q\) is the already retained WIN with
\(h(q)\le h(b)-2\).  Thus valuation two cannot iterate as an unstructured
\(A^2\) source jump: after one B-transfer it is either an explicit lift
over the lower-height token \(q\), or a fixed exponent-three/two frame over
its ordinary A-child.  The remaining rank step is to transport that token
through these two displayed frame types.

## 57. Every canonical side return lowers its proof-tree token

The lower-height WIN retained in Sections 53 and 56 has a uniform next
return even when the ordinary side diamond is exceptional.  Let \(q\) be
WIN, choose a LOSS child \(\ell\) that realizes its canonical height, and
put

\[
y=A(q),\qquad r=B(q),\qquad p=B(A(q))=B(y).
\]

Thus

\[
h(q)=1+h(\ell),\qquad \ell\in\{y,r\}.
\]

If \(q\) is nonexceptional, the ordinary side relation makes \(p\) a
child of both \(y\) and \(r\), hence in particular a child of \(\ell\).
If \(q\) is exceptional but \(\ell=y\), the same conclusion follows
directly from \(p=B(y)\).  In both cases

\[
\boxed{p\text{ is WIN and }h(p)\le h(q)-2.}
\]

It remains only to treat an exceptional \(q\) whose height-realizing LOSS
child is \(\ell=r\).  The four formulas of Section 5 give

\[
\begin{array}{c|c|c}
q&r=\ell&p\\ \hline
16t+1&R(6t)&3(6t)+1\\
16t+3&R(6t+1)&3(6t+1)+1\\
16t+12&R(6t+4)&3(6t+4)+1\\
16t+14&R(6t+5)&3(6t+5)+1.
\end{array}
\]

Apply the universal identity from Section 53,

\[
3z+1=Q_m^{\,1-(z\bmod2)}(J(R(z)))\qquad(m\ge1).
\]

It shows in every exceptional row that \(p\) is an exact factor-free
constant-tail lift over \(\ell\), while

\[
\boxed{\ell\text{ is LOSS and }h(\ell)=h(q)-1.}
\]

Consequently a canonical side return always transports its finite
proof-tree token into one of exactly two typed forms:

1. an ordinary WIN token whose height has fallen by at least two; or
2. an exceptional exact lift over a LOSS token whose height has fallen by
   one.

This is a rank-transport lemma, not yet a boundary-descent theorem: the
returned state has not been proved to be a DRAW boundary endpoint.  The
arithmetic identities above are regression-tested for \(q<100000\).

## 58. The residual three/two frame has only one side escape

Return to the surviving nonexceptional row of Section 56 and write

\[
x=A(q),\qquad a=J(x),\qquad
D=Q_3^f(a),\qquad C=Q_2^f(a).
\]

At least one of \(D,C\) is DRAW, and Section 56 also gives

\[
s\le x<2s,
\]

where \(s\) is the globally minimum coefficient source of a DRAW.  Define

\[
Z=Q_2^f(3a),\qquad X=Q_1^f(3a),\qquad Y=B(C).
\]

The long-tail recurrence and the shared-child identity give the exact
diamond

\[
\boxed{
\operatorname{moves}(D)=\{Z,X\},\qquad
\operatorname{moves}(C)=\{X,Y\}.}
\]

The outcome recursion now has a useful consequence.  The common child
\(X\) cannot be LOSS, since then both \(D\) and \(C\) would be WIN.  If
\(X\) is DRAW, the factor frame \(\{Z,X\}\) already contains a DRAW.  If
\(X\) is WIN, every DRAW among \(D,C\) forces its other child to be DRAW.
Consequently

\[
\boxed{
\{D,C\}\text{ contains a DRAW}
\Longrightarrow
\{Z,X\}\text{ contains a DRAW}\quad\text{or}\quad Y\text{ is DRAW}.}
\]

The side alternative has an exact source type.  If \(f=\alpha(x)\), then
Section 24 makes \(Y\) an ordinary child of \(A(x)\).  Hence

\[
Y\le A^2(x)\le\frac{9x+5}{4}.
\]

Because \(x\le2s-1\), every positive such \(Y\) satisfies

\[
\rho(Y)\le\frac{Y-1}{6}
\le\frac{9s-4}{12}<s.
\]

The terminal case is also not DRAW.  Global source minimality therefore
excludes the side alternative in the A-selecting phase.

If \(f=1-\alpha(x)\), let \(j\ge2\) be the signed valuation selecting
\(B(x)\).  The source-boundary transition and deletion of the final bit of
its constant tail give

\[
\boxed{
Y=Q_{j-1}^{\,1-f}(J(B(x))).}
\]

Since \(x=A(q)\), the source in this exact factor-free lift is

\[
B(x)=B(A(q)),
\]

which is precisely the canonical side-return token typed in Section 57.
Thus the residual frame has the sharpened transition

\[
\boxed{
\begin{array}{l}
\{Q_2^f(3J(x)),Q_1^f(3J(x))\}\text{ contains a DRAW},\\
\text{or }f=1-\alpha(x)\text{ and a DRAW is an exact lift over }
B(A(q)).
\end{array}}
\]

There is no unmarked A-side restart.  The first row is now the sole factor
escape; the second retains either the lower WIN token or the exceptional
LOSS-lift token of Section 57.  The displayed arithmetic identities are
regression-tested in the four surviving residue families for \(b<100000\).

## 59. The factor-one escape reaches a signed boundary in two levels

The first row of Section 58 cannot climb through unbounded powers of three
before exposing another source.  Retain

\[
x=A(q),\qquad a=J(x),\qquad s\le x<2s,
\]

and for \(k=1,2\) define

\[
P_k=Q_2^f(3^ka),\qquad R_k=Q_1^f(3^ka),
\]

\[
S_k=B(P_k)=B(R_k),\qquad
R_{k+1}=A(P_k),\qquad T_k=A(R_k).
\]

The exact moves are

\[
\boxed{
\operatorname{moves}(P_k)=\{R_{k+1},S_k\},\qquad
\operatorname{moves}(R_k)=\{T_k,S_k\}.}
\]

Section 58 leaves the adjacent factor frame
\(\{P_1,R_1\}\) containing a DRAW.  Its common child \(S_1\) cannot be
LOSS, since that would make both frame members WIN.  If \(S_1\) is DRAW,
the factor frame has already exited.  If \(S_1\) is WIN, there are two
possibilities:

- if \(R_1\) is DRAW, then \(T_1\) is DRAW;
- otherwise \(P_1\) must be DRAW, so \(R_2\) is DRAW.

In the last case \(S_2\) cannot be LOSS.  It is either DRAW, or it is WIN
and forces \(T_2\) to be DRAW.  Therefore

\[
\boxed{\text{at least one of }S_1,T_1,S_2,T_2\text{ is DRAW}.}
\]

This conclusion uses only the outcome recursion; it does not impose a
fixed numerical search depth.

The four exits have finite exact arithmetic types.  Factor

\[
3^{k+1}J(x)+1-2f=2^{j_k}J(u_k),\qquad j_k\ge1.
\]

The signed exit and, when \(j_k\ge2\), its side sibling are

\[
\boxed{
T_k=Q_{j_k}^{\,1-f}(J(u_k)),\qquad
S_k=Q_{j_k-1}^{\,1-f}(J(u_k)).}
\]

When \(j_k=1\), \(T_k\) still has the first displayed exact lift form,
while \(S_k=R(T_k)\) is the single raw-side type.

Global source minimality bounds both signed scans.  Since

\[
J(x)\le3x+2\le6s-1,
\]

the two numerators satisfy

\[
9J(x)+1\le54s-8,\qquad
27J(x)+1\le162s-26.
\]

Whenever \(T_k\) is DRAW, its exact source \(u_k\) is at least \(s\).
The same is true when \(S_k\) is DRAW and \(j_k\ge2\).  Since
\(J(u_k)\ge3s+1\), comparison in the two displayed factorizations gives

\[
\boxed{j_1\le4,\qquad j_2\le5.}
\]

Thus the sole factor escape of Section 58 has no unbounded factor-power
counter and no unbounded valuation at its DRAW exit.  It reaches, after at
most one further factor level, one of:

- a factor-free lift or adjacent frame of exponent at most four from the
  \(9J(x)\) transition;
- a factor-free lift or adjacent frame of exponent at most five from the
  \(27J(x)\) transition;
- one of the two corresponding valuation-one raw-side states.

The remaining rank problem is finite at this immediate exit, but the
carried WIN/LOSS proof-height token must still be connected to these
returned types.  All arithmetic identities are regression-tested in the
four residual residue families for \(b<100000\).

## 60. The ninefold and twenty-sevenfold sources form one coupled switch

The two signed rows in Section 59 are not independent.  Put \(a=J(x)\)
and first factor

\[
9a+1-2f=2^vJ(t),\qquad v\ge1.
\]

Then

\[
27a+1-2f
=3\bigl(9a+1-2f\bigr)-2(1-2f).
\]

If \(v\ge2\), the right-hand side has valuation exactly one.  More
precisely, with

\[
u=Q_{v-1}^{\,1-f}(J(t)),
\]

the parity of \(u\) is \(1-f\), and direct substitution gives

\[
J(u)=3\cdot2^{v-1}J(t)-1+2f.
\]

Therefore

\[
\boxed{
v\ge2\Longrightarrow
27J(x)+1-2f=2J(u),\qquad
u=Q_{v-1}^{\,1-f}(J(t)).}
\]

Thus the second-level source is an exact factor-free lift over the
first-level source; the possibly large exponent \(v-1\) remains marked
rather than being discarded as an arbitrary numerical jump.

If \(v=1\), Section 54 gives

\[
\boxed{
t=3A(x)+1=Q_m^\delta(J(B(x)))
\quad\text{for some }m\ge1.}
\]

The same coupling identity becomes

\[
27J(x)+1-2f
=2\bigl(3J(t)+1-2(1-f)\bigr).
\]

Factor the bracket as

\[
3J(t)+1-2(1-f)=2^jJ(u).
\]

This is exactly the ordinary source-boundary transition at \(t\) in phase
\(1-f\).  Consequently

\[
\boxed{
v=1\Longrightarrow
w=j+1,\qquad
u=
\begin{cases}
A(t),&1-f=\alpha(t),\\
B(t),&1-f\ne\alpha(t).
\end{cases}}
\]

In words, the valuation-one ninefold row first produces the explicit lift
over the token \(B(x)\), and the twenty-sevenfold row then takes exactly
one ordinary selected-source step from that lifted state.  Conversely,
every \(v\ge2\) row makes the twenty-sevenfold transition a valuation-one
lift over its already typed ninefold source.

This couples every second-level exit of Section 59 to the Section 54
trichotomy and, in the \(v=1\) row, directly to the carried ordinary token
\(B(x)\).  What remains open is to turn these nested lift/source types into
a strictly well-founded proof-height transition.  The identities are
regression-tested in the residual families for \(b<100000\).

## 61. A LOSS factor source gives every exit a lower-height provenance

The orientation left open in Section 52 has a uniform rank interpretation
through the coupled switch.  Suppose the finite source \(x\) is LOSS and
put

\[
c_A=A(x),\qquad c_B=B(x).
\]

Both ordinary children are WIN, and

\[
\boxed{h(c_A),h(c_B)\le h(x)-1.}
\]

Keep the first factorization from Section 60,

\[
9J(x)+1-2f=2^vJ(t).
\]

If \(v=1\), Section 54 gives

\[
\boxed{
t=Q_m^\delta(J(c_B))\quad(m\ge1),}
\]

so the returned source is an exact factor-free lift over the lower-height
WIN token \(c_B\).

If \(v\ge2\), the same trichotomy gives

\[
t=
\begin{cases}
A(c_A),&v=2,\\
B(c_A),&v\ge3.
\end{cases}
\]

Thus \(t\) is one of the two ordinary children of the lower-height WIN
\(c_A\).  Choose a canonical LOSS child of \(c_A\) and put

\[
p=B(A(c_A)).
\]

Section 57 types this side return without assuming which child the signed
phase selected:

\[
\boxed{
\begin{array}{ll}
p\text{ is WIN},\quad h(p)\le h(c_A)-2\le h(x)-3,
&\text{or}\\
p\text{ is an exact factor-free lift over a canonical LOSS }\ell,
\quad h(\ell)=h(c_A)-1\le h(x)-2.
\end{array}}
\]

The second factor level preserves this provenance.  Section 60 says:

- for \(v\ge2\), its source \(u\) is an exact lift over \(t\), while the
  typed token \(p\) remains attached to the ordinary fork at \(c_A\);
- for \(v=1\), the source \(t\) is already the displayed lift over \(c_B\),
  and \(u\) is exactly one ordinary selected-source child of \(t\).

Consequently neither level of the factor escape creates an unmarked source
when \(x\) is LOSS.  Every returned type carries a WIN token lower than
\(x\) by at least one proof level, and the only exceptional orientation
instead carries a canonical LOSS token lower by at least two levels.

This is provenance and rank transport, not yet a descent theorem for DRAW
boundaries: an additional outcome diamond must expose the carried token as
the WIN endpoint of a DRAW edge.  It does, however, rule out treating the
LOSS-source factor fork as a fresh numerical restart.

## 62. A WIN factor source has only the valuation-two one-sided return

There is an analogous provenance statement in the other source
orientation.  Keep the residual setting

\[
q\text{ WIN},\qquad x=A(q)\text{ finite},
\qquad p=B(x)=B(A(q)).
\]

Suppose now that \(x\) is WIN.  Then the other child \(B(q)\) is necessarily
LOSS.  Section 57 therefore types \(p\) as either the lower-height ordinary
WIN token

\[
h(p)\le h(q)-2,
\]

or, only when \(q\) is exceptional, an exact factor-free lift over the
canonical LOSS \(B(q)\), whose height is \(h(q)-1\).

Factor the first signed exit as in Sections 54 and 60:

\[
9J(x)+1-2f=2^vJ(t).
\]

For \(v=1\), Section 54 immediately gives

\[
\boxed{t=Q_m^\delta(J(p))\quad(m\ge1).}
\]

Thus valuation one is an exact lift over the already carried token.

For \(v\ge3\),

\[
t=B(A(x)).
\]

If \(x\) is nonexceptional, the ordinary side relation makes this same
state a child of \(p=B(x)\):

\[
\boxed{x\text{ nonexceptional},\ v\ge3
\Longrightarrow t\in\operatorname{moves}(p).}
\]

If \(x\) is exceptional, write its formulas from Section 5 as

\[
p=R(z),\qquad t=3z+1.
\]

The universal identity of Section 53 then gives

\[
\boxed{x\text{ exceptional},\ v\ge3
\Longrightarrow t=Q_m^\delta(J(p))\quad(m\ge1).}
\]

Consequently every first factor exit from a WIN source is attached to
\(p=B(x)\), except for the single valuation-two source

\[
t=A^2(x).
\]

That exceptional one-sided valuation is exactly the row normalized in
Sections 55--60: off the four exceptions it returns through
\(B(A(x))\), which is the ordinary child of \(p\) displayed above, and
then enters the fixed three/two frame; on the exceptions it enters the
already typed A-selecting obligation.

Section 60 carries the same provenance through the possible
twenty-sevenfold exit.  Hence a WIN-source factor fork cannot reset to an
arbitrary source: valuation one and every valuation at least three are
direct lift/child forms over \(p\), while valuation two is the unique
recursive frame type already isolated by Sections 55--59.  Exposing this
carried \(p\)-token at a DRAW boundary remains the final rank step.

## 63. An ordinary valuation-two recycle becomes lower WIN or LOSS

The valuation-two recursive type from Section 62 has a universal
game-theoretic closure away from one more exception.  Let \(p\) and \(q'\)
be WIN, suppose \(q'\) is one of the two ordinary children of \(p\), and
assume that \(p\) is nonexceptional.  Put

\[
r=B(A(p)).
\]

Since \(p\) and \(q'\) are both WIN, the other child \(\ell\) of \(p\) is
LOSS.  The ordinary side relation at \(p\) makes \(r\) a child of both
\(q'\) and \(\ell\).  Hence

\[
\boxed{r\text{ is WIN},\qquad h(r)\le h(p)-2.}
\]

Now inspect which child of \(q'\) equals \(r\).  If
\(r=A(q')\), its next A-source is already the displayed lower-height WIN.
If \(r=B(q')\), then \(A(q')\) must be LOSS: the WIN state \(q'\) already
has the WIN child \(r\), so its required LOSS child can only be the other
one.  Thus

\[
\boxed{
A(q')=
\begin{cases}
r\text{ WIN with }h(r)\le h(p)-2,&r=A(q'),\\
\text{LOSS},&r=B(q').
\end{cases}}
\]

Apply this to the nonexceptional valuation-two row of Section 62.  There

\[
p=B(x),\qquad q'=B(A(x)),
\]

and the side relation at the nonexceptional \(x\) makes \(q'\) a child of
\(p\).  Section 55 makes \(q'\) WIN in the retained WIN-source
orientation.  Assume also that Section 57 supplied the ordinary token row,
so \(p\) is WIN.  After Sections 55--58, the recursive three/two frame has
ordinary source

\[
A(q').
\]

Therefore, whenever this WIN \(p\) is also nonexceptional, the new source is
exactly one of the two boxed rank types:

1. a WIN at least two proof levels below \(p\); or
2. a LOSS source, to which Section 61 applies.

Consequently an all-ordinary valuation-two recycle cannot return to an
unmarked WIN source.  Within this ordinary WIN-token row, the only
remaining failure of the closure is the explicit case

\[
\boxed{p=B(x)\equiv1,3,12,14\pmod {16},}
\]

where the ordinary side diamond at \(p\) must be replaced by the
exceptional exact-lift formulas of Section 57.  The arithmetic
two-sided-child identity used above is already regression-tested by the
canonical side-return test.  The separate exceptional lift-token row from
Section 57 remains marked rather than being silently included here.

## 64. The exceptional valuation-two token strictly lowers the source

The exceptional \(p\)-rows left by Section 63 have a strict numerical
return.  Let \(x\) be nonexceptional, put

\[
p=B(x),\qquad q'=B(A(x)),
\]

and suppose \(p\) is exceptional.  Retain the valuation-two condition for
the first factor exit,

\[
9J(x)+1-2f=4J(A^2(x)).
\]

Because \(x\) is nonexceptional, the alternating suffix of \(A(x)\) has
length one or two.  Direct reduction modulo \(256\) gives the complete
table

\[
\begin{array}{c|c|c|c}
p\bmod16&f&x\bmod256&q'\\ \hline
1&1&4,89,132,217&A(p)\\
3&1&9,52,137,180&B(p)\\
12&0&75,118,203,246&B(p)\\
14&0&38,123,166,251&A(p).
\end{array}
\]

Every row has alternating-suffix length exactly two at \(A(x)\).  This is
a bounded residue calculation only because the nonexceptional hypothesis
has already bounded that suffix length; no fixed modulus is being used to
decide an unbounded suffix.  In particular

\[
\boxed{p\le\frac{3x+1}{8}.}
\]

If \(p=1\) or \(14\pmod {16}\), then \(q'=A(p)\), and the next source in
the recursive frame is

\[
A(q')=A^2(p)
\le\frac{9p+5}{4}
\le\frac{27x+49}{32}<x
\]

for \(x\ge10\).  The only smaller table entry is \(x=4\), where
\(p=1,\ q'=2,\ A(q')=3<4\).

If \(p=3\) or \(12\pmod {16}\), then \(q'=B(p)<p\).  Hence

\[
A(q')\le\frac{3q'+1}{2}
\le\frac{3p-2}{2}
\le\frac{9x-13}{16}<x,
\]

with the possible terminal value handled directly.  Thus all sixteen rows
give

\[
\boxed{A(B(A(x)))<x.}
\]

Combine this with Section 63.  Along a valuation-two recursive chain:

- a nonexceptional ordinary WIN token sends the next factor source to a
  lower-height WIN or to LOSS;
- an exceptional token strictly decreases the current integer source
  \(x\).

Therefore valuation two cannot recycle indefinitely while avoiding both
rank alternatives: an all-exceptional tail would be a strictly descending
sequence of positive integers, while its first ordinary row enters the
height/LOSS dichotomy of Section 63.  The exact residue table and strict
inequality are regression-tested for \(x<100000\).

## 65. A canonical A-streak reaches a typed side return in four steps

The other potentially unbounded mechanism in Section 28 is the canonical
A-continuation.  It cannot run indefinitely without exposing the token of
Section 57.  Retain the globally minimum DRAW coefficient source \(s\) and
an A-selecting obligation

\[
O(x,e),\qquad e=\alpha(x),\qquad s\le x<2s.
\]

Suppose its exponent-one member is DRAW, so Section 28 takes the canonical
continuation.  Put

\[
x_i=A^i(x),\qquad e_i=e\mathbin{\mathsf{xor}}(i\bmod2),\qquad
P_i=L_{e_i}(x_i).
\]

As long as \(e_i=\alpha(x_i)\), the expanding child of \(P_i\) is
\(P_{i+1}\).  If the next phase is also A-selecting, then Section 24's
refined side formula simplifies to

\[
\boxed{B(P_i)=x_{i+2}.}
\]

Indeed, \(e_{i+1}=1-e_i=\alpha(x_{i+1})\), so \(e_i\) is the second
binary bit of \(x_{i+1}\).  Directly from
\(A(y)=\lceil3y/2\rceil\), its parity is the second binary bit of \(y\).
Thus \(A(x_{i+1})\bmod2=e_i\), and the first row of Section 24 gives the
box.  This is an exact two-bit identity, not a bounded-suffix assumption.

Section 28 makes \(B(P_0)=x_2\) WIN and hence \(P_1\) DRAW.  Continue only
while the phase remains A-selecting.  Whenever \(P_i\) is DRAW, its side
child \(x_{i+2}\) is non-losing.  If the first four such side children

\[
x_2,x_3,x_4,x_5
\]

were all WIN, they would contradict Section 5's theorem that no four
consecutive states on an A-ray are WIN.  Consequently one of
\(x_3,x_4,x_5\) is DRAW, unless an earlier phase has already become
B-selecting.  Let

\[
x_{j+2}\text{ be the first such DRAW},\qquad 1\le j\le3,
\]

and put

\[
q=x_{j+1},\qquad d=A(q)=x_{j+2},\qquad
\ell=B(q),\qquad p=B(d).
\]

Then \(q\) is a WIN child of the DRAW state \(P_{j-1}\), while \(d\) is
DRAW.  Therefore \(\ell\) is the unique LOSS child of \(q\), and it realizes
the canonical height of \(q\):

\[
h(\ell)=h(q)-1.
\]

The state \(p\) is non-losing because it is a child of \(d\).  Section 57
now gives an exact typed return.  If \(q\) is nonexceptional, \(p\) is also
a child of the LOSS state \(\ell\), and hence

\[
\boxed{d\to p\text{ is a DRAW-to-WIN boundary},\qquad
h(p)\le h(q)-2.}
\]

This is a descent relative to the actual preceding boundary endpoint
\(q\), not an illicit restart of the global minimum-height argument.

If \(q\) is exceptional, Section 57 instead makes \(p\) an exact
factor-free constant-tail lift over \(\ell\).  In this A-streak the retained
LOSS source also decreases numerically:

\[
\boxed{\ell<x.}
\]

To prove it, the four exceptional formulas of Section 5 give uniformly

\[
B(q)\le\frac{3q-3}{16}.
\]

Here \(q=A^{j+1}(x)\) with \(j\le3\), so

\[
q\le A^4(x)\le\frac{81x+65}{16}.
\]

For \(x\ge12\), these inequalities yield

\[
\ell\le\frac{243x+147}{256}<x.
\]

The only smaller residual possibilities are \(x=10,11\).  Their first four
A-iterates are respectively

\[
10,15,23,35,53\quad\text{and}\quad11,17,26,39,59;
\]

the sole exceptional returned WIN in the first row is \(q=35\), with
\(B(q)=3<10\), and the second row has none.  This completes the proof.

Thus a pure canonical A-streak has only three outcomes after at most four
side tests:

1. the phase becomes B-selecting, entering the universal transfer of
   Section 25 (Section 27 applies once its smaller source window is
   recovered);
2. an ordinary DRAW-to-WIN boundary lowers the height by at least two; or
3. an exceptional non-losing exact lift carries a LOSS token whose height
   is one lower and whose integer source is strictly below the initial
   \(x\).

In particular there is no unbounded unmarked canonical A-continuation.
The exact side identity, exceptional lift source, and strict source return
are regression-tested for \(10\le x<100000\).

## 66. A B-phase after the canonical streak has bounded length and exponent

The first outcome of Section 65 cannot create a new unbounded B-transfer
run merely because its source may temporarily exceed the \(2s\) window of
Section 27.  Let \(x_0\) be that section's original source,

\[
s\le x_0<2s.
\]

The phase can switch to B-selecting at one of
\(x_i=A^i(x_0)\), \(0\le i\le4\).  Repeated use of
\(A(u)\le(3u+1)/2\) gives

\[
\boxed{x_i\le A^4(x_0)\le\frac{81x_0+65}{16}
\le\frac{81s}{8}-1.}
\]

Suppose an obligation at a source \(u\) is B-selecting.  Factor its signed
source transition as

\[
3J(u)+1-2e=2^jJ(y),\qquad y=B(u),\qquad j\ge2.
\]

Section 25 transfers its DRAW to the adjacent frame over \(y\).  If
\(j=2\), this is again the exact obligation

\[
O(y,1-e),
\]

and

\[
y=B(u)\le\frac{3u+1}{4}.
\]

Consequently, after \(n\) consecutive valuation-two B-transfers,

\[
u_n\le1+\left(\frac34\right)^n(u_0-1).
\]

At \(n=9\), the preceding source window gives

\[
u_9\le
1+\frac{19683}{262144}\left(\frac{81s}{8}-2\right)<s
\]

for every residual \(s\ge10\).  A DRAW obligation cannot have coefficient
source below the globally minimum \(s\).  Hence

\[
\boxed{\text{at most eight consecutive valuation-two B-transfers survive}.}
\]

Before a ninth transfer, the phase becomes A-selecting or a transition has
\(j\ge3\).  The latter exit also has bounded exponent.  If its adjacent
frame contains a DRAW, its exact factor-free source \(y\) must satisfy
\(y\ge s\).  Since \(J(u)\le3u+2\),

\[
2^jJ(y)=3J(u)+1-2e
\le9u+7\le\frac{729s}{8}-2.
\]

But \(J(y)\ge3s+1\), so \(j\ge5\) would make the left side at least
\(32(3s+1)>729s/8-2\), a contradiction.  Therefore

\[
\boxed{3\le j\le4}
\]

at every source-surviving non-obligation exit.

Thus the phase switch left by Section 65 has only two finite destinations:
an A-selecting obligation after at most eight exact B-transfers, or an
adjacent factor-free frame of exponent three/two or four/three.  This does
not yet prohibit alternation with a nested exceptional lift, but it removes
an unbounded B counter from that alternation.  The nine-step contraction is
regression-tested for the extremal sources \(x_0=s,2s-1\), all
\(10\le s<5000\), and all five possible A-streak positions.

## 67. The total A/B phase horizon is genuinely unbounded

Section 66 bounds each consecutive B-run, not the total number of
alternations between A and valuation-two B transitions.  There are exact
arithmetic prefixes of arbitrary length

\[
A,B_2,A,B_2,\ldots,A,B_2.
\]

For any \(k\ge1\), choose

\[
m=
\begin{cases}
2,&k\text{ even},\\
4,&k\text{ odd},
\end{cases}
\qquad a_0=8^k m-1.
\]

Then \(a_0\) is positive, odd, and not divisible by three, so it has a
unique source \(x_0\) with \(a_0=J(x_0)\).  Start in phase zero.  More
generally, before pair \(i\), put

\[
a_i=9^i8^{k-i}m-1=8t_i-1,qquad
t_i=9^i8^{k-i-1}m
\]

for \(0\le i<k\).  Every \(t_i\) is even.  The phase-zero signed transition
therefore satisfies

\[
3a_i+1=2(12t_i-1),
\]

with valuation exactly one.  After the phase flip, the phase-one transition
is

\[
3(12t_i-1)-1=4(9t_i-1),
\]

with valuation exactly two, because \(9t_i-1\) is odd.  Its returned
coefficient is

\[
a_{i+1}=9t_i-1=9^{i+1}8^{k-i-1}m-1,
\]

and the phase has returned to zero.  Induction supplies all \(k\) pairs.

Thus no proof may replace Sections 63--64 by a fixed phase-only search
horizon.  These long prefixes are not DRAW paths or counterexamples: they
carry no outcome constraints, while Sections 63--64 prove that the retained
WIN/LOSS token prevents an infinite valuation-two recycle.  The construction
is regression-tested for \(1\le k<25\).

## 68. An exceptional side return exposes the lower LOSS as a DRAW source

The exceptional alternative of Sections 57 and 65 does not merely carry a
formal lift token.  One of two adjacent lifts over that token is an actual
DRAW.  Let \(q\) be exceptional and suppose

\[
q\text{ is WIN},\qquad d=A(q)\text{ is DRAW},\qquad
\ell=B(q)\text{ is LOSS}.
\]

Thus \(\ell\) is the unique LOSS child of \(q\), and

\[
h(\ell)=h(q)-1.
\]

Put

\[
p=B(d)=B(A(q)),\qquad v=A(d)=A^2(q).
\]

Section 57 gives exact factor-free coordinates

\[
p=Q_m^\delta(J(\ell))
\]

for some \(m\ge1\).  The four exceptional formulas of Section 5 sharpen
this to an adjacent pair.  Writing \(q=16t+c\), one has

\[
\begin{array}{c|c|c|c}
c&\ell&p&v\\ \hline
1&R(6t)&18t+1&36t+3=2p+1\\
3&R(6t+1)&18t+4&36t+8=2p\\
12&R(6t+4)&18t+13&36t+27=2p+1\\
14&R(6t+5)&18t+16&36t+32=2p.
\end{array}
\]

In the odd rows \(\delta=1\), so \(2p+1\) appends one more terminal one;
in the even rows \(\delta=0\), so \(2p\) appends one more terminal zero.
Consequently

\[
\boxed{
p=Q_m^\delta(J(\ell)),\qquad
v=Q_{m+1}^\delta(J(\ell)).}
\]

The DRAW state \(d\) has exactly the two children \(p,v\).  Neither can be
LOSS, and at least one must be DRAW.  Therefore

\[
\boxed{
\{Q_m^\delta(J(\ell)),Q_{m+1}^\delta(J(\ell))\}
\text{ contains a DRAW}.}
\]

If \(p\) itself is DRAW this is immediate.  If \(p\) is WIN, outcome
recursion forces \(v\) to be DRAW, so the token is not lost through the
other child of \(d\).

Thus every exceptional canonical side return produces an actual
factor-free DRAW lift/frame whose finite source is the canonical LOSS
\(\ell\), one proof level below the preceding boundary endpoint.  Combined
with Section 65, its source is also numerically below the source at the
start of that A-streak.  This closes the local boundary-exposure gap for
the exceptional orientation; the remaining global task is to order
successive ordinary and factor-frame exposures without restarting the
minimum-height endpoint.  The adjacent-coordinate identity is
regression-tested for every exceptional \(q<100000\).

## 69. A height-one boundary has three exact continuation types

The unresolved height-one orientation from Section 13 admits a sharper
normal form without making the invalid inference recorded in Pitfall 14.
Suppose

\[
D\text{ is DRAW},\qquad s=B(D)\text{ is WIN},\qquad
B(s)=0,qquad t=A(D)\text{ is DRAW}.
\]

First let \(D\) be nonexceptional.  The ordinary side relation makes

\[
p:=B(t)=B(A(D))
\]

one of the two children \(A(s),B(s)\) of \(s\).  Since \(p\) is a child of
the DRAW state \(t\), it cannot be the terminal LOSS \(B(s)=0\).  Hence

\[
\boxed{D\text{ nonexceptional}\Longrightarrow B(t)=A(s).}
\]

This common child is non-losing.  If \(A(s)\) is DRAW, then \(s\) is an
exceptional WIN whose A-child is DRAW and whose unique LOSS child is zero.
Section 68 applies legitimately and gives an adjacent factor-free DRAW
frame over source zero.  If instead \(A(s)\) is WIN, outcome recursion at
the DRAW state \(t\) forces its other child to be DRAW:

\[
\boxed{A(s)\text{ WIN}\Longrightarrow A(t)=A^2(D)\text{ DRAW}.}
\]

Thus the latter row is a new boundary whose WIN endpoint is exactly
\(A(s)\); no outcome has been assigned to \(A(s)\) merely from the old
boundary.

Now let \(D\) be exceptional.  The arithmetic part of Section 68 did not
use the outcome of \(D\).  With

\[
p=B(t),\qquad v=A(t),
\]

it gives, for some \(m\ge1\) and \(\delta\in\{0,1\}\),

\[
\boxed{
p=Q_m^\delta(J(s)),\qquad
v=Q_{m+1}^\delta(J(s)).}
\]

Because \(t\) is DRAW, at least one member of this adjacent factor-free
frame over the height-one WIN source \(s\) is DRAW.

Consequently every minimum-height-one boundary enters exactly one of three
typed rows:

1. an adjacent zero-source DRAW frame, when the ordinary common child
   \(A(s)\) is DRAW;
2. a new boundary with WIN endpoint \(A(s)\), when that common child is
   WIN; or
3. an adjacent DRAW frame over the height-one WIN source \(s\), when the
   original parent \(D\) is exceptional.

This is not yet an exclusion of height one: the second endpoint can have
larger proof height, and the two adjacent-frame rows still require the
global marked rank.  It does remove the raw B-predecessor family from the
base case.  All arithmetic identities are regression-tested for
\(D<100000\).

## 70. The A-child of every height-one WIN is an adjacent zero-source gate

The explicit endpoint \(A(s)\) in Section 69 retains the same zero-source
geometry even when it is WIN.  Let

\[
B(s)=0,qquad q=A(s),qquad L=\lfloor\log_2q\rfloor+1.
\]

The equality \(B(s)=R(A(s))=0\) says exactly that the whole binary word for
\(q\) is alternating.  Its leading bit is one.  Hence

\[
3q=
\begin{cases}
2^{L+1}-1,&L\text{ odd},\\
2^{L+1}-2,&L\text{ even}.
\end{cases}
\]

Put \(\delta=0\) for odd \(L\) and \(\delta=1\) for even \(L\).  Directly
from \(A(q)=\lceil3q/2\rceil\),

\[
A(q)=Q_L^\delta(1).
\]

This is a constant binary word of length \(L\).  Its maximal alternating
suffix consists of the final bit alone, so

\[
B(q)=Q_{L-1}^\delta(1).
\]

Thus

\[
\boxed{
\operatorname{moves}(A(s))
=\{Q_L^\delta(J(0)),Q_{L-1}^\delta(J(0))\}.}
\]

The two children are an adjacent factor-free frame over source zero.  This
has an exact outcome interpretation:

- if \(A(s)\) is DRAW, the frame contains a DRAW and no LOSS;
- if \(A(s)\) is WIN, the frame contains at least one LOSS witness of that
  WIN (the other member can be WIN or DRAW).

Consequently the ordinary successor in Section 69 does not discard the
height-one provenance.  It converts the terminal LOSS child of \(s\) into
an adjacent zero-source child frame of \(A(s)\), marked either by a DRAW or
by a LOSS witness according to the endpoint outcome.  The exact coordinates
are regression-tested for every height-one endpoint \(s<100000\).

## 71. A zero-source DRAW frame has one explicit factor boundary

The arbitrarily long exponent in the zero-source DRAW frame of Sections
69--70 does not create an arbitrary boundary valuation.  Write

\[
S_{k,r}^\delta:=Q_r^\delta(3^k),qquad
k\ge0,\qquad r\ge1,\qquad\delta\in\{0,1\}.
\]

For \(r\ge3\), Section 14 gives

\[
\operatorname{moves}(S_{k,r}^\delta)
=\{S_{k+1,r-1}^\delta,S_{k+1,r-2}^\delta\}.
\]

If a zero-source adjacent frame contains a DRAW, choose a DRAW member and,
while its exponent is at least three, choose a DRAW child.  A DRAW has no
LOSS child and at least one DRAW child, so this is always possible.  The
tail exponent decreases by one or two at each move.  Hence after finitely
many steps there is a DRAW state.  The two zero-source base states with
coefficient exponent zero and tail exponent one or two are resolved
explicitly in Section 15, so neither can be DRAW.  Consequently at least
one long-tail move has occurred, which proves the coefficient exponent
below is at least one.  Thus there is a DRAW state

\[
S_{k,r}^\delta,qquad r\in\{1,2\},qquad k\ge1.
\]

For any positive integer \(n\), factor

\[
3^n+1-2\delta=2^j b,qquad b\text{ odd}.
\]

The states \(S_{n-1,1}^\delta\) and \(S_{n-1,2}^\delta\) have the common
contracting child

\[
C_{n,\delta}:=R(3^n-\delta),
\]

while the expanding child of \(S_{n-1,1}^\delta\) is

\[
E_{n,\delta}:=Q_j^{1-\delta}(b).
\]

If the reached DRAW has exponent one, put \(n=k+1\).  Its children are
exactly \(C_{n,\delta}\) and \(E_{n,\delta}\), so the pair contains a
DRAW.

If the reached DRAW has exponent two, first put \(n_0=k+1\).  Its children
are

\[
C_{n_0,\delta}\quad\text{and}\quad S_{k+1,1}^\delta.
\]

If \(C_{n_0,\delta}\) is DRAW, take \(n=n_0\).  Otherwise it is WIN and
forces \(S_{k+1,1}^\delta\) to be DRAW.  The latter is an exponent-one
state with coefficient \(3^{k+1}\), so now take \(n=n_0+1=k+2\); its two
children are \(C_{n,\delta}\) and \(E_{n,\delta}\).  Therefore for some

\[
n\in\{k+1,k+2\}
\]

one has

\[
\boxed{\{C_{n,\delta},E_{n,\delta}\}\text{ contains a DRAW}.}
\]

The signed exponent \(j\) is exact:

\[
\boxed{
\begin{array}{c|cc}
&n\text{ odd}&n\text{ even}\\ \hline
\delta=0&j=2&j=1\\
\delta=1&j=1&j=2+v_2(n).
\end{array}}
\]

For \(3^n+1\), reduction modulo eight gives valuation two for odd \(n\)
and valuation one for even \(n\).  For \(3^n-1\), odd \(n\) gives valuation
one modulo four, while the standard factorization induction

\[
3^{2m}-1=(3^m-1)(3^m+1)
\]

gives \(v_2(3^n-1)=2+v_2(n)\) for even \(n\).

Thus the long zero-source factor descent has only one raw side and one
signed exit.  Three of the four parity/phase rows have exponent at most two;
the sole unbounded row is controlled exactly by the integer counter
\(v_2(n)\).  This is a finite arithmetic normalization, not yet a rank:
the raw side can still carry the DRAW, and the source of the signed odd
coefficient \(b\) can be large.  The boundary identities and valuation table
are regression-tested for \(1\le n<100\).

## 72. The raw and signed zero-source exits have one common source

The two exits of Section 71 are not independent.  Retain

\[
3^n+1-2\delta=2^j b
\]

and write the factor-free odd coefficient uniquely as

\[
b=J(y).
\]

If \(j\ge2\), then the raw and signed exits are exactly the adjacent
factor-free frame

\[
\boxed{
C_{n,\delta}=Q_{j-1}^{\,1-\delta}(J(y)),\qquad
E_{n,\delta}=Q_j^{\,1-\delta}(J(y)).}
\]

There are only two such rows.  If \(\delta=0\), then \(n\) is odd and
\(j=2\).  Since \(3^n\) ends in two one bits, its maximal alternating
suffix has length one, and

\[
R(3^n)=\frac{3^n-1}{2}=2b-1.
\]

If \(\delta=1\), then \(n\) is even and \(j=2+v_2(n)\ge3\).
The integer \(3^n-1=2^jb\) ends in at least three zero bits, so again its
maximal alternating suffix has length one, and

\[
R(3^n-1)=2^{j-1}b.
\]

These are precisely the two boxed identities.

If \(j=1\), both rows instead share the explicit ordinary source

\[
\boxed{y=\frac{3^{n-1}-1}{2}.}
\]

For \(\delta=0\), \(n\) is even, \(y\) is odd, and direct substitution
gives

\[
\boxed{C_{n,0}=A(y),\qquad E_{n,0}=Q_1^1(J(y)).}
\]

For \(\delta=1\), \(n\) is odd and \(A(y)\) is even.  Appending the final
one in \(J(y)=2A(y)+1\), and then the final zero in \(2J(y)\), extends the
same alternating suffix without changing its remainder.  Therefore

\[
\boxed{C_{n,1}=B(y),\qquad E_{n,1}=Q_1^0(J(y)).}
\]

This coupling sharpens the outcome conclusion of Section 71.  In the
\(j=2\) row, its construction gives the exact obligation
\(O(y,1)\): either the lower exponent-one member is DRAW, or a DRAW parent
has the exponent-two/one pair as its children.  In the \(j\ge3\) row it
gives an adjacent factor-free DRAW frame over \(y\), with the sole
remaining exponent

\[
j=2+v_2(n).
\]

In either \(j=1\) row, if the signed exit is DRAW then it is already an
exponent-one factor-free DRAW lift over \(y\).  Otherwise the ordinary
exit \(A(y)\) or \(B(y)\) is DRAW.  Its coefficient source is strictly
less than \(y\): for every positive state \(q\),

\[
\rho(q)\le\frac{q-1}{6},
\]

while \(B(y)<y\) and \(A(y)\le(3y+1)/2\).  Thus the valuation-one raw
alternative is a genuine numerical source descent, not an untyped restart.

Consequently the raw zero-source side has been eliminated as an independent
type.  What remains is an exponent-one obligation, a strict source descent,
or the single even-minus adjacent frame whose exponent is
\(1+v_2(n)\) on its lower member.  The identities and strict source
descent are regression-tested for \(2\le n<100\).

## 73. A zero-source LOSS token reaches the same boundary with lower height

The LOSS-marked zero-source frame of Section 70 has a stronger transition
than the DRAW-marked frame: its proof-tree height falls while the long tail
is removed.  Retain

\[
S_{k,r}^\delta=Q_r^\delta(3^k).
\]

Suppose \(S_{k,r}^\delta\) is LOSS and \(r\ge4\).  Its expanding child

\[
U=S_{k+1,r-1}^\delta
\]

is WIN and satisfies

\[
h(U)\le h(S_{k,r}^\delta)-1.
\]

The long-tail recurrence applies once more at \(U\), giving

\[
\operatorname{moves}(U)=
\{S_{k+2,r-2}^\delta,S_{k+2,r-3}^\delta\}.
\]

Choose a canonical LOSS child \(L'\) of the WIN state \(U\).  The height
recursion gives

\[
\boxed{
L'\in\{S_{k+2,r-2}^\delta,S_{k+2,r-3}^\delta\},\qquad
h(L')\le h(S_{k,r}^\delta)-2.}
\]

Thus each two-ply block preserves an actual LOSS token, adds exactly two
factors of three, lowers the tail exponent by two or three, and lowers its
finite proof height by at least two.

Starting from a LOSS member of the zero-source frame, iteration terminates
at

\[
\boxed{
S_{2m,r}^\delta\text{ LOSS},\qquad
r\in\{1,2,3\},\qquad
h(S_{2m,r}^\delta)\le h(L_0)-2m,}
\]

where \(L_0\) is the original LOSS witness.  In particular the accumulated
factor exponent is even; the long tail cannot discard the proof-height
mark.

The three terminal exponents have only two boundary orientations.  If
\(r=1\), the two children of the LOSS token are the Section 71 pair with

\[
n=2m+1\quad\text{odd}.
\]

Both children are WIN, their heights are at most one below the terminal
LOSS, and the signed valuation is bounded:

\[
j=
\begin{cases}
2,&\delta=0,\\
1,&\delta=1.
\end{cases}
\]

If \(r=2\), its expanding child is
\(S_{2m+1,1}^\delta\); if \(r=3\), its contracting child is that same
state.  In either case this exponent-one state is WIN, and a canonical
LOSS child of it belongs to the Section 71 pair with

\[
n=2m+2\quad\text{even}.
\]

That new LOSS has height at most two below the terminal LOSS.  Section 72
now types the pair exactly:

- for \(\delta=0\), it is the valuation-one ordinary/lift pair over one
  source;
- for \(\delta=1\), it is the adjacent factor-free pair
  \[
  Q_{1+v_2(n)}^0(J(y)),\qquad
  Q_{2+v_2(n)}^0(J(y)).
  \]

Hence the sole unbounded even-minus exponent from Sections 71--72 is never
unmarked when it comes from the height-one LOSS witness: one of its two
members is an actual LOSS whose proof height has strictly fallen.  This is
rank transport, not yet a contradiction, because the accompanying DRAW
boundary still has to be coupled to that lower LOSS token.  All displayed
arithmetic identities and parity/valuation rows are regression-tested for
the indicated small parameter ranges.

## 74. An ordinary DRAW spine exposes the adjacent LOSS token in two steps

There is a direct boundary-exposure diamond for the marked adjacent frames
of Sections 70 and 73.  Suppose

\[
T\text{ is DRAW},\qquad q=B(T)\text{ is WIN},\qquad
d=A(T)\text{ is DRAW},
\]

and suppose the two children of \(q\) form an adjacent constant-tail frame

\[
\operatorname{moves}(q)=
\{Q_{r+1}^e(a),Q_r^e(a)\}
\]

containing a LOSS.  Assume that both \(T\) and \(d\) are nonexceptional.

Put

\[
p=B(d)=B(A(T)).
\]

The ordinary side relation at \(T\) makes \(p\) one of the two children of
\(q\).  Since it is also a child of the DRAW state \(d\), it is non-losing.
Therefore the other frame member, call it \(\ell\), is the unique LOSS
child of \(q\), and

\[
h(\ell)=h(q)-1.
\]

Every adjacent constant-tail frame has exactly one common child \(u\).  For
\(r\ge2\) it is explicitly

\[
u=Q_{r-1}^e(3a);
\]

for \(r=1\) it is the common contracting child from Section 14.  Because
\(u\) is a child of the LOSS state \(\ell\),

\[
\boxed{u\text{ is WIN},\qquad h(u)\le h(q)-2.}
\]

If \(p\) is DRAW, then \(p\to u\) is already a boundary edge with the
displayed lower endpoint height.

If \(p\) is WIN, its other child is LOSS because its common child \(u\) is
WIN.  The DRAW state \(d\), whose contracting child is the WIN state \(p\),
must then have

\[
v=A(d)\text{ DRAW}.
\]

The ordinary side relation at \(d\) makes

\[
B(v)=B(A(d))
\]

a child of \(p=B(d)\).  It is also a child of the DRAW state \(v\), so it
cannot be the LOSS child of \(p\); hence \(B(v)=u\).  Thus \(v\to u\) is
the required boundary edge.  In both cases

\[
\boxed{\text{there is a boundary WIN }u\text{ with }h(u)\le h(q)-2.}
\]

Apply this to the ordinary successor row of Section 69.  There
\(q=A(s)\), its children are the adjacent zero-source frame of Section 70,
and the preceding DRAW has children \(q\) and its DRAW continuation.
Consequently the height-one successor cannot pass through two consecutive
nonexceptional DRAW-spine states without exposing a boundary endpoint two
proof levels below \(q\).  The only local obstruction is now an explicit
exception at one of those two DRAW states, not the length of the
zero-source tail.  The common-child identity is regression-tested for odd
coefficients below \(200\), both phases, and lower exponents below \(12\).

## 75. Only four suffix lengths can obstruct the height-one spine descent

The exceptional alternative left by Section 74 is automatically absent
when the predecessor suffix is long.  In the ordinary successor row of
Section 69, write

\[
T=A(D),\qquad R(T)=s,\qquad q=B(T)=A(s).
\]

Let \(L\) be the length of the maximal alternating suffix deleted from
\(T\).  If \(L\ge5\), the last four bits of \(T\) are alternating, so

\[
T\bmod16\in\{5,10\}.
\]

Neither residue is exceptional.  The last five bits give the sharper
alternatives

\[
T\equiv21\pmod {32}\quad\text{or}\quad
T\equiv10\pmod {32}.
\]

In the first row \(T\) is odd and

\[
A(T)=\frac{3T+1}{2}\equiv0\pmod {16};
\]

in the second it is even and

\[
A(T)=\frac{3T}{2}\equiv15\pmod {16}.
\]

Thus both consecutive DRAW-spine states \(T\) and \(A(T)\) are
nonexceptional whenever \(L\ge5\).  Section 74 applies and exposes a new
boundary WIN whose height is at least two below \(q=A(s)\).

Consequently

\[
\boxed{\text{a height-one ordinary successor can avoid the Section 74
descent only when }L\in\{1,2,3,4\}.}
\]

This is a legitimate finite suffix split: the long case is decided by the
actual suffix length before residues are used.  It does not assume that a
fixed modulus detects an unbounded alternating suffix.  The two residue
conclusions are regression-tested for every positive state below
\(100000\) whose alternating suffix has length at least five.

## 76. The height-one ordinary successor has no exceptional row

The four short suffix lengths left by Section 75 collapse completely once
the original parent is required to be ordinary.  Keep the notation of
Sections 69 and 75:

\[
D\text{ nonexceptional},\qquad s=B(D),\qquad B(s)=0,
\]

\[
T=A(D),\qquad q=A(s),\qquad B(T)=q.
\]

For a nonexceptional \(D\), Section 5 says that the alternating suffix of
\(T=A(D)\) has length only one or two.  Moreover the last equality says
that the ordinary side relation at \(D\) selects \(A(s)\), rather than the
terminal state \(B(s)=0\).

If the suffix length is one, the side relation selects \(A(s)\) exactly
when

\[
s\bmod4\in\{0,3\}.
\]

Intersecting with the four height-one residues
\(\{1,3,12,14\}\pmod {16}\) leaves \(s\equiv3,12\pmod {16}\).
If the suffix length is two, the selecting residues are instead
\(s\bmod4\in\{1,2\}\), leaving \(s\equiv1,14\pmod {16}\).

Appending the corresponding one- or two-bit maximal suffix to \(s\), and
then applying \(A\), gives the complete table

\[
\boxed{
\begin{array}{c|c|c|c}
s\bmod16&L&T\bmod16&A(T)\bmod16\\ \hline
3&1&7&11\\
12&1&8&4\\
1&2&6&9\\
14&2&9&6.
\end{array}}
\]

None of the last two columns contains an exceptional residue.  Therefore
the two consecutive DRAW-spine states \(T\) and \(A(T)\) always satisfy
the hypotheses of Section 74.  We obtain

\[
\boxed{\text{every height-one ordinary successor exposes a boundary
WIN at least two proof levels below }q=A(s).}
\]

Thus the ordinary parent row of Section 69 has no residual exceptional
case and no unbounded suffix case.  The still-open height-one orientation
is the row where the original parent \(D\) itself is exceptional and
Section 69 produces an adjacent DRAW frame over \(s\).  The four-row table
and the absence of exceptional spine residues are regression-tested for
all parent states below \(100000\).

## 77. A height-one source has one dyadic signed transition

The source arithmetic in the exceptional row of Section 69 has only two
phases.  Let

\[
B(s)=0,\qquad q=A(s),\qquad
L=\lfloor\log_2q\rfloor+1,
\]

and retain the phase \(\delta\) of Section 70:

\[
\delta=
\begin{cases}
0,&L\text{ odd},\\
1,&L\text{ even}.
\end{cases}
\]

The all-alternating formula for \(q\) is

\[
3q=2^{L+1}-1-\delta.
\]

Since \(J(s)=2q+1\), it follows immediately that

\[
\boxed{3J(s)=2^{L+2}+1-2\delta.}
\]

The A-selecting source phase is exactly

\[
\boxed{\alpha(s)=\delta.}
\]

One way to see this without a residue table is to factor the two signed
transitions.  In phase \(1-\delta\),

\[
3J(s)+1-2(1-\delta)=2^{L+2}.
\]

Its odd coefficient is \(1=J(0)\), so this phase selects \(B(s)=0\), with
exact valuation \(L+2\).  The other phase must select \(A(s)=q\), and
indeed

\[
3J(s)+1-2\delta=2J(q).
\]

Thus

\[
\boxed{
\begin{array}{c|c|c}
\text{phase}&\text{valuation}&\text{returned source}\\ \hline
\delta&1&A(s)=q\\
1-\delta&L+2&B(s)=0.
\end{array}}
\]

Consequently the exceptional adjacent DRAW frame over the height-one
source \(s\) has only two source-boundary orientations: a valuation-one
lift over the explicit alternating state \(q\), or a possibly long but
purely dyadic return to source zero.  This does not yet control factors of
three accumulated while a long frame descends, but it removes any
untyped signed transition at its original source.  The identities, phases,
valuations, and selected sources are regression-tested for every
height-one source below \(100000\).

## 78. Accumulated factors have one height-one valuation resonance

The factors of three left open by Section 77 have an exact valuation
filter.  Retain its notation

\[
3J(s)=2^M+\sigma,\qquad
M=L+2,\qquad \sigma=1-2\delta,
\]

and suppose \(k\ge1\) factors of three have accumulated after the first
factor layer.  At the next signed boundary the numerator is

\[
N_{k,e}=3^{k+1}J(s)+1-2e
=3^k(2^M+\sigma)+1-2e.
\]

In the A-selecting phase \(e=\delta\),

\[
N_{k,\delta}
=3^k2^M+\sigma(3^k+1).
\]

Since \(M\ge4\) and

\[
v_2(3^k+1)=
\begin{cases}
2,&k\text{ odd},\\
1,&k\text{ even},
\end{cases}
\]

the high dyadic term cannot affect the valuation.  Hence

\[
\boxed{
v_2(N_{k,\delta})=
\begin{cases}
2,&k\text{ odd},\\
1,&k\text{ even}.
\end{cases}}
\]

In the B-selecting phase \(e=1-\delta\), put

\[
h=v_2(3^k-1)=
\begin{cases}
1,&k\text{ odd},\\
2+v_2(k),&k\text{ even}.
\end{cases}
\]

Now

\[
N_{k,1-\delta}=3^k2^M+\sigma(3^k-1).
\]

The two summands have valuations \(M\) and \(h\).  If they differ, the
smaller one is the exact valuation:

\[
\boxed{h\ne M\Longrightarrow
v_2(N_{k,1-\delta})=\min\{h,M\}.}
\]

If \(h=M\), both quotients are odd and their signed sum is even, so

\[
\boxed{h=M\Longrightarrow v_2(N_{k,1-\delta})>M.}
\]

The resonance condition is itself exact:

\[
h=M\quad\Longleftrightarrow\quad v_2(k)=L.
\]

Thus the arbitrarily long exceptional frame has no unbounded valuation in
its A phase.  Its B phase is also explicit except for one resonant row,
where the factor counter \(k\) is divisible by \(2^L\) but not
\(2^{L+1}\).  This is still not a rank: the resonant quotient and the
outcomes of the raw/signed siblings must be coupled.  The full filter is
regression-tested for every height-one source below \(10000\) and
\(1\le k\le256\).

## 79. Every pair of consecutive factor levels is coupled

The switch of Section 60 is not restricted to its original ninefold and
twenty-sevenfold rows.  Let \(a=J(x)\), fix a phase \(e\), and for any
\(k\ge0\) factor

\[
N_k:=3^{k+1}a+1-2e=2^vJ(t).
\]

The next factor level satisfies the universal recurrence

\[
N_{k+1}=3N_k-2(1-2e).
\]

If \(v\ge2\), put

\[
u=Q_{v-1}^{\,1-e}(J(t)).
\]

Direct substitution in the definition of \(J\) gives

\[
J(u)=3\cdot2^{v-1}J(t)-1+2e,
\]

and therefore

\[
\boxed{v\ge2\Longrightarrow N_{k+1}=2J(u).}
\]

Thus the next valuation is exactly one and its source is the displayed
factor-free lift over \(t\).

If \(v=1\), then

\[
N_{k+1}
=2\bigl(3J(t)+1-2(1-e)\bigr).
\]

Factor the bracket as

\[
3J(t)+1-2(1-e)=2^jJ(u).
\]

For \(t>0\), it is precisely the ordinary source-boundary transition at
\(t\) in phase \(1-e\).  Hence

\[
\boxed{
v=1\Longrightarrow
v_2(N_{k+1})=j+1,\quad
u\in\{A(t),B(t)\}
}
\]

with the selected letter determined by that source phase.

For the terminal source \(t=0\), the bracket is instead \(2+2e\);
direct factorization leaves returned source zero and gives bracket
valuation one for \(e=0\), two for \(e=1\).  No ordinary move from the
terminal state is being asserted.

Consequently no two consecutive factor levels can both have valuation at
least two.  In particular the high resonant valuation of Section 78 is
immediately followed by a valuation-one exact lift over its returned
source; it cannot form an unmarked high-valuation run.  This is a complete
arithmetic coupling, not yet an outcome descent, because a DRAW may choose
between side and signed exits.  It is regression-tested for all sources
below \(100\), both phases, and nine consecutive factor levels.

## 80. A DRAW factor frame exits at the current or next level

The outcome part of Section 59 is also universal.  Let \(a\) be positive
and odd, fix a phase \(e\), and for any \(k\ge0\) put

\[
P_k=Q_2^e(3^ka),\qquad R_k=Q_1^e(3^ka),
\]

\[
C_k=B(P_k)=B(R_k),\qquad
R_{k+1}=A(P_k),\qquad T_k=A(R_k).
\]

The exact moves are

\[
\operatorname{moves}(P_k)=\{R_{k+1},C_k\},\qquad
\operatorname{moves}(R_k)=\{T_k,C_k\}.
\]

Suppose the adjacent frame \(\{P_k,R_k\}\) contains a DRAW.  Its common
child \(C_k\) cannot be LOSS, since that would make both frame members WIN.
If \(C_k\) is DRAW, the scan has already exited at the current level.  If
it is WIN and \(R_k\) is DRAW, outcome recursion forces \(T_k\) to be
DRAW.

The only remaining case has \(P_k\) DRAW and \(R_k\) not DRAW.  Then
\(R_{k+1}\) is DRAW.  Its children are exactly \(T_{k+1}\) and
\(C_{k+1}\).  Neither is LOSS, and at least one is DRAW.  Therefore

\[
\boxed{\{C_k,T_k,C_{k+1},T_{k+1}\}\text{ contains a DRAW}.}
\]

This conclusion is independent of \(a,e,k\), the size of the frame before
it reached exponents two/one, and all residue classes.

Combine it with Section 79.  The two signed exits \(T_k,T_{k+1}\) have
coupled sources: a valuation at least two at one level is followed by a
valuation-one exact lift at the other, while a valuation-one source is
followed by one selected-source step.  Hence the high resonance of Section
78 cannot be bypassed by continuing through further factor levels: every
DRAW-marked scan exposes a raw or signed exit at the resonant level or its
immediate successor.

This is still a four-exit outcome normal form, not a proof-height descent;
the two raw exits must be attached to the carried terminal/lower-height
token.  The three displayed move identities are regression-tested for odd
base coefficients below \(200\), both phases, and seven factor levels.

## 81. Every raw factor exit is adjacent or strictly source-lowering

The two raw exits in Section 80 are not untyped.  Consider either factor
level and write its signed numerator as

\[
3a+1-2e=2^vJ(t).
\]

The signed and raw exits are

\[
T=Q_v^{\,1-e}(J(t)),\qquad C=R(T).
\]

If \(v\ge2\), the final constant block of \(T\) has length at least two,
so its maximal alternating suffix is only its last bit.  Therefore

\[
\boxed{C=Q_{v-1}^{\,1-e}(J(t)).}
\]

The raw and signed exits are an adjacent factor-free frame over the same
source \(t\).  If either is DRAW, that frame contains a DRAW.

If \(v=1\), put \(g=1-e\).  Then

\[
T=Q_1^g(J(t))=2J(t)-g.
\]

Suppose its raw exit \(C=R(T)\) is positive, and let \(\rho(C)\) be its
coefficient source.  Deleting a nonempty binary suffix gives

\[
C\le\left\lfloor\frac{T}{2}\right\rfloor\le J(t).
\]

The universal coefficient-source bound yields

\[
\rho(C)\le\frac{C-1}{6}
\le\frac{J(t)-1}{6}
\le\frac{3t+1}{6}<t
\qquad(t\ge1).
\]

For \(t=0\), one has \(T\in\{1,2\}\) and \(R(T)=0\), so the raw exit is
terminal.  Thus a positive valuation-one raw DRAW
is always a strict numerical source descent:

\[
\boxed{v=1,\ C\text{ DRAW}\Longrightarrow \rho(C)<t.}
\]

Combining Sections 79--80 now gives a three-type outcome normal form for
an arbitrary DRAW factor frame:

1. an adjacent factor-free DRAW frame over the returned source of the
   valuation-at-least-two level;
2. an exponent-one DRAW lift over the returned source of the
   valuation-one level;
3. a positive raw DRAW whose coefficient source is strictly smaller than
   that returned source.

The first two sources are coupled by Section 79 as an exact lift or one
ordinary selected-source step.  Hence neither raw exit creates an
unmarked restart.  This still does not compare the coupled returned source
with the proof-height token carried into the factor frame.  The strict raw
source inequality is regression-tested for every source below \(10000\)
and both phases.
