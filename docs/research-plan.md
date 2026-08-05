# Prioritized research plan

## Goal

Exclude draw positions in the infinite directed graph with moves

\[
A(q)=\left\lceil\frac{3q}{2}\right\rceil,
\qquad
B(q)=R(A(q))<q.
\]

## Priority 1: characterize a hypothetical draw kernel

Let `S` be the set of draw positions. Game recursion imposes:

- no position in `S` may have a losing child;
- every position in `S` must have at least one child in `S`;
- if a position has a losing child, it is winning;
- if both children are winning, it is losing.

Derive stronger closure properties using the strict descent of `B` and the predecessor structure of `A` and `B`.

Questions:

1. Can every nonempty draw kernel be shown to contain a forbidden minimal configuration?
2. Can one assign a secondary order so that a draw-preserving edge always descends lexicographically?
3. Does repeated use of `B` force a contradiction with minimality after a bounded symbolic pattern rather than a bounded numerical horizon?

Current sharp reduction: Section 12 of `docs/verified-results.md` shows that
a boundary edge with minimum `WIN` proof height must have an exceptional
vertex among its `DRAW` parent and the two children.  The immediate task is
therefore to close those exceptional boundary triples using the explicit
four formulas of Section 5, while retaining the forced `LOSS` witness.  A
rank on the coarser arithmetic return graph is known to be insufficient.
Section 14 additionally reduces every generated family `a*2^r-1` with
`r>=3` to the three boundary exponents `0,1,2`; exponents `1` and `2` have
an exact shared contracting child.  The remaining rank problem is therefore
concentrated at exponent zero and at the two shared-child boundary states,
where the coefficient map contains the `5 <-> 7` arithmetic cycle.
The symmetric constant-tail form shows that the same reduction covers long
zero tails and closes every expanding transition by alternating the signed
coefficient maps `3a+1` and `3a-1`.
Section 15 gives a strict coefficient drop at the common `r=1,2` contracting
child.  In particular a DRAW with globally minimum constant-tail coefficient
can leave `r=1` only through a valuation-one signed transition.  The next
target is to show that repeated valuation-one growth and long-tail reduction
must either create a smaller-coefficient DRAW or create a lower-height
DRAW/WIN boundary.
Section 16 closes the next step to a three-way fork and proves a reverse
division-by-three lemma for every exponent at least two.  The surviving
arithmetic obstruction is now an adjacent `r=1,2` pair with coefficient
less than `9a/8`, whose shared child is already known to be WIN, plus the
valuation-two growth branch.
Section 17 replaces raw odd coefficients by unique source coordinates
`a=3^k J(s)`.  Long-tail moves preserve `s`, and the three-free signed
boundary is exactly one `A/B` move of the original transformed game.  The
remaining exponent-one transition with `k>0` is expressed by
`3^(k+1) J(s) +/- 1 = 2^j J(t)`.  Section 18 now shows that the first two
three-free lifted steps return exactly to the ordinary source side branch
`B(A(s))`; at the four exceptional residues the source instead drops
strictly.  The surviving case is therefore a nondecreasing ordinary side
return `B(A(s))>=s`.  Section 19 classifies it exactly as
`s=0,5,10,15 mod 16`.  In the four phase-mismatch subclasses modulo 32, the
adjacent lifted pair forces a smaller-source LOSS sibling, a shared WIN
child, and a new DRAW `Q_1^e(3J(B(A(s))))`.  Section 20 identifies the
competing child of this DRAW with the forced LOSS branch of a larger diamond,
excluding all four mismatch classes.  Only the phase-match classes
`s=0,10,21,31 mod 32` remain.  There the side child is another canonical
minimum-source lift at the larger source `B(A(s))`.  Section 21 excludes the
four long-returned-suffix subclasses `21,63,64,106 mod 128`.  In every other
phase-match class, the returned common child is numerically larger than `s`
but has coefficient source below `s`; the next adjacent pair has source equal
to that larger integer.  Section 22 restores the proof-height component: a
returned suffix of length at least three always creates a new boundary whose
WIN height drops by at least two.  Therefore only the eight suffix-length-two
classes modulo 128 can persist without an immediate source contradiction or
height drop.  Section 23 puts those eight classes in one exact outcome normal
form: a DRAW must continue either through a lift whose phase selects a forced
ordinary WIN child `r`, or through the opposite adjacent pair whose phase
selects the forced ordinary LOSS child `ell`.  The immediate target is to
show that the LOSS-source fork creates a lower-height boundary and that the
WIN-source fork cannot repeat without entering it.  Section 24 proves the
universal two-bit diamond for an `A`-selecting lift and thereby closes the
LOSS-source fork in the four `31,53,74,96 mod 128` rows by a strict height
drop.  The remaining local cases are the `B`-selecting LOSS-source fork in
the other four rows and the two WIN-source continuations.  Section 25
unifies exactly those cases: the universal factor-three diamond transfers
either kind of surviving `B`-selecting fork to an adjacent frame over the
ordinary source `B(c)`.  The immediate target is now to normalize arbitrary
adjacent exponents in that transferred frame without losing the source
outcome or the minimum boundary height.  Section 26 completes that
normalization in the actual residual rows: a source-nondecreasing transfer
has valuation exactly two, so its frame already has exponents one and two.
Only eight classes modulo 256 survive, and their next `A`/`B` source phase
is split exactly by eight classes modulo 512.  The remaining task is to
iterate this boundary-pair transfer while proving that a visit to the
retained LOSS branch lowers the globally minimum WIN proof height.  Section
27 shows that the `B` part cannot iterate indefinitely: after the first
transfer its source is below `2s`, and at most two further valuation-two
`B` transfers can stay above `s`.  The obstruction is now an exact
`A`-selecting exponent-one/two obligation with source in `[s,2s)`.  Section
28 forces its common side node to be WIN.  Either the DRAW continues through
the canonical lift of `A(x)`, or a retained LOSS sibling and factor-three
DRAW produce an adjacent frame over the WIN side node.  A source-surviving
factor frame has lower exponent only `1`, `2`, or `3`.  The immediate target
is to control alternation between the canonical `A(x)` continuation and
these three factor frames; treating only the last two exponent values would
leave the canonical branch open.  Section 29 identifies the retained LOSS
child's expanding move as the exact opposite-tail twin of the lower factor
child.  Section 30 takes the first coupled recurrence step: both members of
the factor frame share one child, while at exponents two and three the
retained WIN has the exact opposite-tail twin of that child.  If the common
child remains DRAW, the next level therefore contains a forced LOSS on the
opposite tail side.  The next proof must close this DRAW/LOSS twin switch at
the signed exponent-one boundary and feed any surviving boundary WIN back
into the proof-height descent; neighboring integers cannot simply be
assigned the same outcome.  Section 31 supplies a first rank component at
that boundary: an A-selecting common DRAW returns below the source that made
the factor fork, while a source-surviving B-selection has valuation only two
or three and stays in an explicit bounded multiple of the global minimum
source.  Section 32 bounds the first signed transitions after the r=2,3
twin alternatives as well: at most four after r=2, and at most three then
four in the two r=3 continuations.  The remaining automaton is therefore
finite at every immediate factor exit.  Section 33 further collapses the
whole high-valuation r=3 class to one B-selecting lift at a source
below 16s, retaining two WIN side states below s.  Section 34 turns those
states into the exact ordinary return W=B(A(u)) and proves that its WIN
height is at least two below the preceding boundary endpoint.  Section 35
transfers the returned B-selecting lift with valuation two to an obligation
whose selected child is exactly W.  For every first valuation v>=6 the
A-selecting side diamond then exposes a still lower boundary endpoint, so
the whole unbounded class is a strict height descent.  Section 36 makes the
two remaining cases finite: v=4 leaves lower exponent at most four over the
lower-height WIN source W, while v=5 leaves exponent at most three over the
forced LOSS source M.  The immediate target is to close these WIN/LOSS
frames together with the low-valuation r=1,2,3 exits and their possible
alternation with canonical A-continuations.  Section 37 identifies the
v=4, j=3,4,5 cases as three finite same-phase ladders: an upper adjacent
DRAW frame and the exact lower WIN states supplied by the retained ordinary
LOSS.  The next local target is to close these ladders and the separate j=2
boundary.  Section 38 reduces a surviving v=5 DRAW still further: the side
state must come from the exceptional rows Z=3 or 12 modulo 16 and has only
exponent two or three over the explicit LOSS source M.  The next local
target is sharpened by Section 39: if this side state is DRAW, its next
contracting boundary endpoint lies at least two WIN-height levels below W.
Thus only its WIN-boundary alternative can recycle; the next task is to
couple that alternative to the v=4 ladders and the low-valuation factor
exits.  Section 40 removes the outcome ambiguity inside the three v=4
ladders: each one forces a LOSS witness among the four explicit states
C, D, T1, T2.  The immediate symbolic target is the common WIN child below
these witnesses.  Section 41 supplies it uniformly: every nonexceptional
row either exposes a new boundary WIN or strictly lowers boundary height.
Only S1=1,14 and S2=3,12 modulo 16 survive as exceptional DRAW
continuations.  These four rows, the v=4 j=2 exponent-zero boundary, and
the recycling WIN-boundary alternatives are now the immediate targets.
Section 42 eliminates the S1 exceptions outright and converts every S2
exception into a lift of exponent at most four over the explicit LOSS
source C.  Thus the remaining v=4 DRAW continuation is finite; its
constant-tail children should now be coupled to the two WIN children of C.
Section 43 also normalizes the separate j=2 row: it returns to an obligation
at a WIN source W<10s with an explicit LOSS sibling, and reaches an
A-selecting phase, a source drop, or an exponent-two/three frame after at
most eight preserving B transfers.  The next rank must retain that LOSS
sibling across these bounded transfers and the recycling WIN-boundary
alternative.  In the immediate A-selecting half, Section 44 already gives
the boundary/strict-descent dichotomy and leaves only an exceptional WIN
source R.  The unresolved B half and that exceptional R row should be
merged with the bounded exceptional lifts of Section 42.  Section 45 shows
that the r=2 valuations three and four are not new cases whenever E is
nonexceptional: either orientation of its forced LOSS supplies the same
j=3 or j=4 ladder.  Only E=3,12 modulo 16 and the already known lower
S1/S2 exceptions survive.  Those rows and valuations one/two are the next
local targets.  Section 46 converts the E=3,12 orientation itself into an
exponent-at-most-three lift over an explicit LOSS source below 81s/16.
Thus valuations three/four are finite in every orientation; valuations
one/two and the common treatment of these bounded LOSS-source lifts are the
next local targets.  Section 47 now normalizes valuations one/two as well:
valuation two is an exact obligation below 81s/16, while valuation one is
either an obligation below 81s/8 or a raw-side DRAW with coefficient source
below about 2.54s.  Thus every r=2 exit is bounded; the next task is to show
that repeated bounded returns cannot recycle without a strict height or
source descent.  Section 48 also normalizes r=1 completely: it gives either
a strict source return, an obligation below 27s/8, or one exponent-two
DRAW below 27s/16 whose next side source lies below about 1.27s (unless its
explicit exponent-one factor sibling carries the DRAW).  The remaining
local arithmetic is now concentrated in low r=3; after that the core task is
to synthesize a well-founded rank for the finite return types.  Section 49
handles the contracting-DRAW half of low r=3: it returns either to an
obligation below about 2.54s or to a Q2/raw-side DRAW below about 1.27s.
Section 50 handles the expanding-DRAW half as well: it produces only
obligations or adjacent frames of exponent at most four with explicit
constant source windows, or a raw-side return below about 3.80s.  All local
factor exits are now finite.  The central remaining task is to synthesize
and prove a well-founded rank for their possible recycling, retaining the
explicit LOSS witnesses and boundary-WIN heights.  Section 51 isolates the
height component precisely: when the factor endpoint P itself realizes the
global minimum boundary height, both WIN children of its unique LOSS witness
form a barrier that no DRAW parent may touch.  The next abstraction must
therefore distinguish a boundary endpoint whose minimum-height provenance is
known from an arbitrary later endpoint.  Merely carrying the label LOSS for
the witness, without this provenance, is insufficient.
Section 52 adds the first type-sensitive rank edge.  The ordinary source x
of the A-selecting obligation is never DRAW.  For factor exponents two and
three, a WIN orientation of x makes the factor boundary endpoint
B(A(x)) a child of either possible LOSS witness of x and hence lowers
height by two.  Rank synthesis can therefore restrict the r=2,3 recycling
problem to obligations whose ordinary source is LOSS; exponent one remains
the separate one-sided return A^2(x).
Section 53 removes most of that one-sided ambiguity.  Its A-selecting
continuation cannot carry a DRAW and instead lowers the boundary height.
Every B-selecting continuation selects an ordinary LOSS source and carries
a hidden state c=B(A(x)) with the same outcome as x and height lower by two.
The nonexceptional row has valuation three and an ordinary parent-child
link between c and the returned LOSS source; the exceptional row has
valuation two and is an exact constant-tail lift over c.  The next rank
state should therefore remember a lower-height finite predecessor, not
only the outcome and height of the returned obligation source itself.
Section 54 supplies the analogous type edge after the exponent-two and
three switches.  Their next signed source is not arbitrary: valuation one
is a lift over B(b), valuation two is A^2(b), and every valuation at least
three is the two-sided return B(A(b)).  For a nonexceptional factor endpoint
b, the last source is WIN and lower than b by two proof levels.  Rank
synthesis can now treat only valuation two as a genuinely one-sided source
and valuation one as an explicit lower-source lift type.
Section 55 types the valuation-two row further.  Its source A^2(b) is
finite in the r=2 and contracting r=3 occurrences.  The returned phase is
A only when b is exceptional; otherwise it is B and carries the strict
lower-height WIN q=B(A(b)).  The next local target is now precise: prove
that the first B-transfer over A^2(b) exposes a descendant of q, or isolate
the finite exceptional residue rows where that common-child link fails.
Section 56 completes that local target.  After the first B-transfer, the
exceptional row is an exact lift over q, while the ordinary row is the
single exponent-three/two frame over A(q); every larger valuation is below
the minimum source.  Both successors retain the same strict token
h(q)<=h(b)-2.  Rank synthesis should now use two marked frame states,
\"lift over a lower WIN\" and \"3/2 frame over its A-child\", rather than
another numerical source window.
Section 57 shows that the next ordinary side return always spends this
proof-tree token: it produces either a WIN of height lower by two, or the
single exceptional lift type over a canonical LOSS of height lower by one.
The remaining local target is to expose the carried WIN/LOSS token at an
actual DRAW boundary before any unmarked factor restart.
Section 58 removes the unmarked side restart from the residual three/two
frame.  Its A-selecting side child has source below the global minimum; its
B-selecting side child is an exact lift over the Section 57 token.  The sole
remaining escape is therefore the marked factor-one two/one frame over the
same finite source.  Rank synthesis should close that factor frame without
discarding whether the carried token is a lower WIN or an exceptional lift
over a canonical LOSS.

## Priority 2: finite transducer plus numerical potential

A fixed residue class is insufficient, but `R` is naturally read by a finite transducer scanning bits from right to left until the first repeated bit.

Search for a certificate with state:

- parity / carry data for multiplication by `3`;
- whether the alternating suffix is still open;
- a small phase describing whose game-theoretic obligation is being certified;
- a numerical component such as bit length, affine weight, or a short vector of potentials.

The desired certificate should show that over every allowed block of optimal-response moves, the vector decreases lexicographically.

## Priority 3: predecessor-tree analysis

The inverse of `A=F` is unique when it exists. Predecessors through `B` correspond to attaching alternating binary suffixes before applying `F^{-1}`.

Tasks:

1. derive an exact symbolic parameterization of all `B`-predecessors;
2. examine whether a closed draw set would need impossible density or branching;
3. determine whether every infinite draw path would force a forbidden 2-adic limit.

## Priority 4: search for ordinal ranks

Ordinary size cannot decrease on every move. Candidate ranks may be:

- lexicographic pairs `(bit_length, suffix_state)`;
- weighted binary digit sums;
- ordinals below `omega^k` attached to transducer states;
- ranks assigned to game-theoretic pairs or blocks rather than individual edges.

Any proposed rank must be checked against adversarial long alternating suffixes.

## Priority 5: computational discovery, not brute force

Use the bounded retrograde solver to:

- extract minimal local proof trees;
- test candidate residue or suffix rules;
- find the smallest counterexample to proposed lemmas;
- measure long runs of side-branch outcomes;
- synthesize small automata or decision trees, then prove their rules symbolically.

Do not spend most effort merely increasing the cutoff.

## Suggested first local session

1. Run all tests.
2. Run retrograde analysis at a laptop-safe cutoff.
3. Add a script that extracts the proof tree of a selected `WIN` or `LOSS` position.
4. Parameterize `B`-predecessors symbolically.
5. Search for a two-component potential over short move blocks.
6. Record every failed candidate in the ledger.
