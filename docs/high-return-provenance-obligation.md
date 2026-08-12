# High-return token-provenance obligation

Status: **OPEN — RED UNTIL THE SHARED TOKEN-LIFECYCLE THEOREM IS PROVED**.

Two tempting substitutes for the missing lifecycle proof have been
falsified computationally on states with exact finite proof certificates:
successive arithmetic side-WIN heights can increase, and the observed binary
outcome language has maximal empirical `2`-kernel growth through depth eight.
Neither observation affects the local componentwise descent proved below;
they show only that it cannot be replaced by a source-free scalar side height
or by a small suffix automaton.  See
`docs/rank-candidate-falsification-2026-08-12.md`.

This note isolates the one transition that the current human no-DRAW
assembly does not justify.  Arithmetic finiteness is not enough: every
height used by a multiset decrease must belong to a retained token
occurrence before the transition.

## Local high-return geometry already proved

For a high-return row with `v >= 7`, source `t`, and phase `g`, define

\[
u=Q_{v-1}^g(J(t)),\qquad
c=Q_{v-3}^g(3J(t))=B(u),
\]

\[
p=B(A(u))=A(c),\qquad b=B(p).
\]

The local outcome argument proves

\[
u,c,p,b\text{ are WIN},\qquad A(u),B(c)\text{ are LOSS},
\]

and therefore

\[
h(p)\le h(u)-2,\qquad h(b)\le h(c)-2.
\]

If the re-entry obligation takes the marked factor branch, it further
constructs `q WIN` and `y LOSS` with

\[
h(q)<h(p),\qquad h(y)<h(b).
\]

These inequalities are **PROVED LOCAL GEOMETRY**.  They do not by themselves
prove a rank transition.

## Required retained-token statement

Let a macro configuration carry exact token occurrences, not only their
numeric heights.  A long high-return entry is admissible only if one of the
following disjoint alternatives is proved.

1. **Retained pair.**  The incoming configuration already contains exact
   occurrences of both states `u` and `c` in one ranked multiset.  The
   transition removes those occurrences and inserts `p,b` (or `q,y`).

2. **Prepaid installation.**  A named earlier rank coordinate has just
   strictly decreased, and the formal transition relation explicitly permits
   one initialization of a fresh later multiset with the exact pair `u,c`.
   The proof must show that this initialization cannot recur while all
   earlier coordinates are fixed.

3. **Different parent replacement.**  The incoming configuration contains a
   named retained token `z`, and both `u,c` are certified proper descendants
   of that same occurrence (or of two named incoming occurrences).  The
   transition first replaces those incoming occurrences by `u,c`; only then
   may the local high-return descent be used.

It is forbidden to use a fourth alternative of the form “`u,c` have finite
outcomes, so mark them.”

There is a potentially simpler version of alternative 2 which should be
tested before trying to derive `u,c` from an older token.  Index only the
visits to the long high-return control.  The first visit in a routing episode
may initialize its temporary pair without being compared to an earlier pair;
every *later* visit must be preceded either by a strict source/token payment
or by a proved same-token return module.  The marked-tail table already pays
the retained LOSS token for `D>=3`.  Moreover, the formally possible
valuation-one `D=1` lift over `q` is empty: direct substitution makes its
valuation at least two, so `D=1` always pays an actual child of the retained
LOSS token.  The remaining `D=2` module now has a local strict payment from
its retained `q` occurrence.  Thus a high-return-to-high-return lifecycle
theorem would reduce the red item to legal installation and carry of the
marked pair, provided it also proves:

1. an episode with only finitely many high returns cannot have an infinite
   equal-rank tail in the generic normalizer;
2. no transition can re-enter high return without either the intervening
   strict payment or a proved same-token carry;
3. the temporary `u,c` pair is removed at the end of the visit and is never
   compared with a pair from a different episode.

This subsequence formulation is an **UNVERIFIED LEAD**.  It does not by
itself authorize the high-return descent in the current certificate.

The `D=2` direct-DRAW lift supplies a natural candidate for the token handed
to this lifecycle.  For `w=Q_m^delta(J(y)) DRAW`, either `B(w)` is DRAW and
the active integer source drops from `w` to `B(w)`, or `B(w)` is WIN and
`w -> B(w)` is a concrete DRAW boundary while the continuing DRAW is
`A(w)`.  Thus the old LOSS token `y` need not itself rank every subsequent
factor edge if the normalizer can prove that this newly exposed boundary WIN
is carried without reseeding up to the next high return.  Establishing that
carry is exactly the unresolved identity/lifecycle obligation; merely knowing
that `B(w)` is finite is not enough.

## Lifecycle obligations

Any proposed repair must prove all of the following.

- **Entry:** every game-semantic edge into the `v >= 7` high-return control
  satisfies one of the three alternatives above.
- **Identity:** the exact state identities of retained occurrences survive
  every zero-rank raw/signed/factor routing edge.
- **Exit:** the high-return temporary pair is either converted into the exact
  marked pair `q,y`, inherited by the canonical obligation at `p`, or removed
  only after an earlier rank coordinate strictly decreases.
- **No reseed:** no path at fixed earlier rank can install a second unrelated
  high-return pair.
- **Re-entry:** every later high return uses retained descendants of the
  previous pair or occurs after a separately identified earlier-coordinate
  decrease.
- **Outcome compatibility:** the DRAW carrier is always an actual DRAW state;
  finite tokens are carried alongside it and are never substituted for it.

## Acceptance test for the article

The red status may be removed only when the manuscript provides:

1. a precise macro-configuration type containing token identities;
2. an exhaustive table of all edges entering and leaving long high return;
3. for every table row, the incoming occurrence(s), outgoing occurrence(s),
   and the first strictly decreasing rank coordinate;
4. a proof that equal-rank routing preserves the actual token multiset;
5. a concrete semantic refinement from every relevant DRAW configuration to
   one table row.

Finite regression tests may support the arithmetic identities, but cannot
discharge these five proof obligations.
