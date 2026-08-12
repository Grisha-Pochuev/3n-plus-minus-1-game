# D=2 loss-anchored obligation

Status: **LOCALLY CLOSED — THE SHARED HIGH-RETURN TOKEN-LIFECYCLE AUDIT
REMAINS RED**.

The source-only candidate rank has been falsified: the exact equal-source
state graph contains `1 -> 2 -> 1` with canonical source `1`.  This cycle is
not outcome-compatible with a retained LOSS anchor, so it does not disprove
the desired module.  It does prove that the eventual rank must use the LOSS
outcome/proof-tree provenance and not merely equality of canonical sources.
See `docs/rank-candidate-falsification-2026-08-12.md`.

## Bounded hostile search for a purely local closure

**COMPUTATIONALLY VERIFIED (discovery evidence only).**  The command

```text
set PYTHONPATH=src
python scripts/search_boundary_obstructions.py \
  --d2-loss-lifts --minimum-boundary-height --limit 12 --depth 10
```

tests the exact marked outcomes `b,q WIN`, `y LOSS`, and the direct returned
lift `w DRAW`.  It additionally forbids every DRAW parent visible in the
depth-ten forward neighbourhood from having either child of `y`; this is the
local consequence that would be required if `b` were a globally
minimum-height DRAW-boundary endpoint.  Of the 24 parameter/phase rows, 19
are locally inconsistent but five survive.  Increasing to depth twelve on
sources at most four leaves both phases of `t=3` locally consistent:

```text
python scripts/search_boundary_obstructions.py \
  --d2-loss-lifts --minimum-boundary-height --limit 4 --depth 12

rejected: 6; survivors: 2
first survivors:
  (t,g)=(3,0), (3,1)
```

This is not a counterexample and does not assert that those states are DRAW
in the infinite game.  It does rule out treating one fixed shallow outcome
diamond as the missing proof.  A symbolic unbounded rank or carry theorem is
still required; no finite search depth may be promoted to that theorem.

The short marked row `D=2` carries an actual retained `LOSS` token `y` and
enters an exact lift

\[
w=Q_m^{\delta}(J(y)),\qquad m\ge2.
\]

This exact source identity is proved.  It is not yet a proof that the whole
attached raw/signed/factor normalization is well-founded at fixed outer
token `y`.

## Phase check and one strict subcase

The phase of the returned lift is always B-selecting.  Indeed
`w=Q_m^delta(J(y))` with `m>=2`, so the two final bits of `w` both equal
`delta`, whereas the A-selecting phase is the complement of the second
binary bit.  Thus

```text
sourceTransition(w, delta) = (B, j, B(w)),  j >= 2,
```

and `B(w)<w`.  Exact examples are

- `t=1, g=0`: `y=6`, `w=Q_7^1(J(y))`, `B(w)=1823`;
- `t=1, g=1`: `y=202`, `w=Q_2^0(J(y))`, `B(w)=227`.

The reproducible diagnostic is

```text
set PYTHONPATH=src
python scripts/inspect_d2_rows.py --limit 64
```

This closes the branch in which the original exponent-three/two frame first
enters its two/one factor pair.  In that branch, the current/next-level scan
has four exits: the valuation-one raw exit has coefficient source below `w`;
the valuation-one signed exit is the first alternative of `O(w,delta)` and
Section 25 transfers it to the adjacent frame over `B(w)`; the two next-level
exits already form that adjacent frame.  Every one of these is strict in the
active numerical source `w`.

It does not by itself close the other outcome of the initial three/two diamond.  Its
common side is `w` itself, so that branch may give `w DRAW` directly.  The
fact that phase `delta` is B-selecting is a statement about the signed
transition of the coefficient `J(w)`; it is not a game move from `w` and
cannot be used to replace `w` by `B(w)`.  The remaining unbounded obligation
is therefore exactly the direct-DRAW lift

```text
w = Q_m^delta(J(y)) DRAW,  m >= 2,
```

with retained pair `(q WIN, y LOSS)`.

There is no untyped outcome at this direct exit.  If `w` is DRAW,
then its contracting child `B(w)` is non-losing.  If `B(w)` is DRAW, this is
a strict numerical exit because `B(w)<w`.  Otherwise `B(w)` is WIN and
`A(w)` must be DRAW, so `w -> B(w)` is an actual DRAW-to-WIN boundary and
the continuing DRAW is `A(w)`.

The decisive exact split is

```text
B(w) is one of {A^2(q), B(A(q))}.
```

It follows by direct substitution in the two phases, equivalently by the
appended-suffix calculation used for the marked `D=2` row.  When the result is
`B(A(q))`, Section 57 applies to the retained WIN token `q`: it gives a WIN
descendant at least two proof levels below `q`, or an exact lift over the
canonical LOSS child one level below `q`.  This half is strictly ranked.

The other half is genuinely one-sided:

```text
B(w)=A^2(q).
```

If the canonical LOSS child of `q` is `A(q)`, this is again a certified WIN
descendant.  But if the canonical LOSS child is `B(q)`, no common-child
identity places `A^2(q)` below that witness.  It is invalid to infer a height
drop merely because `A^2(q)` is two moves from `q`; this is Pitfall 10 in an
exact new guise.  The remaining local obligation is to use the additional
marked LOSS token `y`, the outcome of `A^2(q)`, or the following factor
diamond to eliminate or rank precisely this orientation.

Thus `D=2` is substantially narrowed but not closed.  The global high-return
lifecycle must additionally prove that the marked pair `(q,y)` is installed
and carried legally between successive high-return episodes.

## Closure of the one-sided family

The remaining `B(w)=A^2(q)` orientation has a sharper exact form.  Recall
that the marked row has

\[
b,q\text{ WIN},\qquad y\text{ LOSS},\qquad q=A(b),\quad y=B(b).
\]

If `b` is ordinary, the ordinary side identity places `B(q)=B(A(b))` among
the two children of `y=B(b)`.  Since `y` is LOSS, `B(q)` is WIN.  Therefore
the other child `A(q)` is the canonical LOSS child of the WIN state `q`, and

\[
A^2(q)\text{ is WIN},\qquad h(A^2(q))\le h(q)-2.
\]

The identity `B(w)=A^2(q)` selects exactly the two exceptional orientations

\[
b\equiv12\pmod {16}\quad(g=0),\qquad
b\equiv3\pmod {16}\quad(g=1).
\]

Section 68's arithmetic formula, now applied to `b`, gives an integer
`r>=1`, a phase `epsilon`, and a common child `c` such that

\[
B(q)=Q_r^\epsilon(J(y)),\qquad
A(q)=Q_{r+1}^\epsilon(J(y)),\qquad
c\in\operatorname{moves}(B(q))\cap\operatorname{moves}(A(q)).
\]

Put `p=B(q)`, `v=A(q)`, and `x=A^2(q)=B(w)`.  Since `w` is DRAW, `x` is
not LOSS.  There are now two exhaustive cases.

1. If `p` is not LOSS, then the finite WIN state `q` must use `v` as its
   LOSS child.  It is the only LOSS child, so `h(v)=h(q)-1`.  Since `x` is
   a child of `v`,

   \[
   x\text{ is WIN},\qquad h(x)\le h(q)-2.
   \]

2. Suppose `p` is LOSS.  The outcome `v` cannot be WIN: because `x` is
   non-LOSS, a WIN state `v` would need its other child `c` to be LOSS,
   whereas `c` is a child of the LOSS state `p` and therefore is WIN.
   If `v` is DRAW, then `p` is the unique LOSS child of `q`, hence
   `h(p)=h(q)-1`.  If `v` is LOSS, choose the lower-height member of
   `{p,v}`; its height is `h(q)-1`.  When that member is `p`, replace `q`
   by `p`; when it is `v`, replace `q` by its child `x`, for which
   `h(x)<=h(v)-1=h(q)-2`.

Thus in every one-sided row the already retained occurrence of the WIN
token `q` has a certified proper proof-tree descendant, namely `x`, `p`, or
`x` after choosing the canonical member of `{p,v}`.  The arithmetic form and
the required common-child incidence are regression-tested by
`test_d2_a2_orientation_has_a_lower_common_child`.

Together with the already ranked `B(w)=B(A(q))` orientation, this closes the
local direct-DRAW `D=2` lift **provided the incoming occurrence of `q` is
actually installed in the ranked configuration**.  That proviso is exactly
the shared long high-return provenance/lifecycle obligation; the local
argument does not install `q` by itself.

## Forbidden shortcut

It is invalid to argue:

> every later state has coefficient source `y`, therefore the same token is
> preserved and a tail counter decreases.

A later factor boundary can move to an exact lift over an ordinary child of
`y`, and a new tail exponent may be larger than the previous one.  The proof
must identify the actual retained token occurrence and the rank payment
before any such reset.

## Superseded residual exit partition

The earlier audit required the following full exit partition starting from
`w=Q_m^delta(J(y))`:

1. `m=2`;
2. `m=3`;
3. `m>=4` canonical three-bit recurrence;
4. first raw exit DRAW;
5. first signed exit DRAW;
6. no-first-exit obligation;
7. every factor-boundary valuation `j=1`, `j=2`, and `j>=3`;
8. ordinary versus exceptional ordinary child of `y`;
9. terminal source zero.

The two-orientation proof above supersedes that expansion: it pays the
incoming `q` occurrence at the direct DRAW exit before any such inner reset.
The list remains recorded as an audit guard in case a future proof attempts
to normalize the direct lift without using that strict token payment.  Such
a proof would still have to record, for every nonempty row:

- the exact DRAW carrier;
- the exact retained incoming token occurrence;
- the exact outgoing token occurrence, if it changes;
- a parent/child proof that the new token is a proper proof-tree descendant;
- otherwise an explicit natural counter that strictly decreases and cannot
  be reset while the token is fixed;
- the exact next control type.

## Remaining global formulation

The global certificate must carry the exact occurrence of `q` from the
marked high-return pair into this row and prohibit a new pair installation
until the strict replacement proved above is registered.

## Acceptance test

The one-sided `A^2(q)` orientation is now covered for the full unbounded
parameter range, so the separate orange item is closed.  The unconditional
theorem remains red/open until the shared high-return carry/no-reseed
lifecycle proves that the incoming `q` occurrence is legally installed and
preserved to this edge.  Finite cutoffs remain regression evidence only.
