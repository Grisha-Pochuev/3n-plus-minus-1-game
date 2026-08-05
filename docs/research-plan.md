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
Section 59 proves that this factor frame cannot climb indefinitely: a DRAW
reaches a signed or side exit after at most one more factor level, and every
source-surviving valuation is at most four in the 9J(x) row and at most five
in the 27J(x) row.  The next target is now a finite typed return table for
these two rows, with the Section 57 token attached to every edge; a purely
numerical window would again lose the rank information.
Section 60 couples the two rows without a residue table.  A first valuation
of at least two makes the 27J(x) source an exact lift over the 9J(x) source;
a first valuation of one makes that source a lift over B(x), followed by
one ordinary selected-source step.  The remaining rank state therefore
needs one nested-lift flag plus the WIN/LOSS token orientation, not two
independent signed-transition counters.
Section 61 supplies the LOSS-source height component: the valuation-one
row is marked by the lower WIN B(x), while every higher valuation is marked
by A(x) and then by its canonical side-return token.  The token height
strictly falls, but a completion still has to prove that the nested
lift/source exit exposes this token at a DRAW boundary before another
factor switch.  This boundary-exposure lemma is now the immediate target.
Section 62 supplies the WIN-source half.  Its valuation-one and
valuation-at-least-three exits are respectively an exact lift over, or an
ordinary child of, the retained token B(x); only valuation two recurses
through the already normalized three/two frame.  Thus both finite source
outcomes now preserve explicit provenance.  The unresolved theorem is
sharply concentrated in showing that an indefinitely recycled
valuation-two/nested-lift path must expose one of these strictly lower
tokens as a DRAW-boundary endpoint.
Section 63 closes the all-ordinary valuation-two recycle at the source
level.  If the retained p and the returned q' are WIN and p is
nonexceptional, the next A-source is either a WIN two height levels below p
or a LOSS source.  Only the exceptional p rows and the already marked
exceptional lift-token orientation can avoid this dichotomy.  These
explicit exceptional rows are now the immediate target; another generic
factor analysis is unnecessary.
Section 64 closes those exceptional p rows numerically: valuation two
forces a length-two suffix and the next recursive source is strictly
smaller.  Hence an indefinitely pure valuation-two recycle is impossible;
it must terminate in the lower-WIN/LOSS rank types of Sections 61 and 63.
The remaining proof obligation is no longer the valuation-two loop itself,
but boundary exposure for the finite nested-lift exits that terminate it.
Section 65 also removes the other unbounded-looking local mechanism.  Four
consecutive A-selecting lift sides would be four consecutive WIN states on
one A-ray, which Section 5 forbids.  At the first DRAW side, the preceding
WIN is an actual boundary endpoint.  Its ordinary return lowers boundary
height by two; its exceptional return is an exact lift over the unique LOSS
child, whose height is lower by one and whose source is strictly below the
source at the start of the A-streak.  Therefore neither a pure valuation-two
loop nor a pure canonical A-streak remains.  The immediate target is now a
single global rank that proves their finite typed exits cannot alternate
forever through the exceptional nested-lift orientation.
Section 66 bounds the intervening B-phase even when the A-streak has left
the original 2s window.  Its source is still below 81s/8; nine consecutive
valuation-two B-transfers fall below s, while any source-surviving larger
valuation is only three or four.  Thus the entire A/B phase alternation has
bounded local counters.  The remaining issue is genuinely the rank carried
by the exceptional nested lift, not an omitted long phase run.
Section 67 records the necessary qualification: the *total* number of
alternations has no fixed arithmetic horizon.  Exact prefixes
`A,B2,A,B2,...` exist at every length.  Hence the final rank must spend the
retained proof-height token on each valuation-two macrocycle; multiplying
the separate local counter bounds is not a valid completion.
Section 68 closes the exceptional local exposure itself.  If the side lift
over the unique LOSS child is WIN rather than DRAW, the other child of the
same DRAW parent is exactly the next adjacent lift over that identical
LOSS source and is forced DRAW.  Hence an exceptional token always becomes
the genuine coefficient source of a DRAW frame, one proof level lower than
the preceding boundary endpoint.  The remaining task is global bookkeeping:
choose a marked-configuration rank that compares these exposed LOSS-source
frames with the ordinary lower-height boundary endpoints and the factor
returns of Sections 61--64 without assuming that a later endpoint reattains
the original minimum height.
The height-one family of Section 13 remains a separate base orientation.
Its DRAW continuation is the sibling \(A(D)\) of the WIN endpoint
\(s=B(D)\), not the state \(A(s)\).  Section 68 applies only after an
actual DRAW A-child of a WIN token has been established, so it cannot be
used to skip this distinction.  The marked-configuration rank must include
the orientation of the boundary edge as well as the token height.
Section 69 supplies that orientation for height one.  An ordinary parent
either reaches a genuine zero-source DRAW frame or transfers the boundary
to the explicit endpoint A(s); an exceptional parent reaches an adjacent
DRAW frame over s itself.  The raw infinite set of B-predecessors is
therefore replaced by the same two marked frame types used in the
positive-height analysis plus one oriented boundary successor.  The next
rank must show that repeated A(s) successors cannot alternate indefinitely
with the adjacent height-one frames.
Section 70 shows that this successor is not unmarked: both children of
A(s) form an adjacent source-zero frame.  A DRAW A(s) marks that frame by
DRAW, while a WIN A(s) marks it by a required LOSS witness.  Thus the
height-one base can be represented by a finite outcome flag on one
zero-source adjacent-frame type; the next local target is the transition of
that marked frame through its first factor-three boundary.
Section 71 performs that transition for a DRAW-marked frame.  Following a
DRAW child strictly lowers the tail exponent until one/two, after which the
only possible DRAW exits are the raw state R(3^n-delta) and the signed
3^n+1-2delta state.  LTE makes the signed exponent explicit; only the minus
row at even n retains the counter 2+v2(n).  The next target is to couple the
raw state to that signed source, as Section 60 coupled the ninefold and
twenty-sevenfold exits, and to retain the LOSS-marked zero-source frame from
Section 70 through the same boundary.
Section 72 supplies the requested coupling.  At valuation at least two the
raw and signed exits are the two adjacent lifts over one source y.  At
valuation one, the raw side is exactly A(y) or B(y); if it rather than the
signed exponent-one lift carries DRAW, its own coefficient source is
strictly below y.  Thus only the even-minus row retains a tail counter,
namely 1+v2(n) on the lower frame member.  The next target is a descent for
that row, preferably by halving the exponent parameter n, together with the
parallel propagation of the LOSS witness in the zero-source frame.
Section 73 supplies that parallel propagation.  Every two-ply long-tail
block turns the marked LOSS into another genuine LOSS, adds two factors of
three, and lowers its proof height by at least two.  The terminal factor
exponent is therefore even.  Exponent one reaches only bounded odd-n
valuations; exponents two and three reach the even-n boundary, where the
unbounded minus frame now contains a strictly lower-height LOSS token.
The remaining height-one task is an outcome diamond coupling the adjacent
DRAW boundary to this lower LOSS member; the arithmetic tail counter itself
is no longer unmarked.
Section 74 gives that coupling whenever the next two DRAW-spine states are
ordinary.  Their side diamonds force the common child of the adjacent
LOSS/non-losing frame to become a genuine boundary WIN at least two proof
levels below the current endpoint.  Thus neither the DRAW-marked nor the
LOSS-marked zero-source tail is an ordinary obstruction.  The remaining
height-one rows must place an exceptional residue on one of two consecutive
DRAW-spine states; those explicit exceptional returns are the next finite
case split.
Section 75 makes that split finite without a fixed-modulus shortcut.
An actual alternating suffix of length at least five forces the two
DRAW-spine residues to 5/10 and 0/15 modulo 16, so Section 74 applies.
Only suffix lengths one through four remain; these can now be expanded as
exact affine predecessor rows with the adjacent LOSS orientation retained.
Section 76 closes those short rows.  Nonexceptionality of the original
parent already restricts its suffix to length one or two, and the
outcome-compatible side choice leaves four residue rows; in all four, both
DRAW-spine states are ordinary, so Section 74 forces the height descent.
The only remaining height-one orientation is therefore the exceptional
original-parent row, whose adjacent DRAW frame over the height-one WIN
source s must be coupled to the terminal LOSS child of s.
Section 77 reduces that exceptional frame to two exact source phases.  The
A phase has valuation one and returns the explicit alternating state A(s);
the B phase is the pure power 2^(L+2) and returns source zero.  What remains
is to control the factors of three accumulated while the adjacent frame
descends before reaching this signed boundary; its starting transition is
now dyadic rather than an arbitrary source jump.
Section 78 filters every later signed boundary.  The A phase alternates
between valuations two and one with the parity of the accumulated factor
counter k.  The B phase is the minimum of the dyadic exponent L+2 and the
LTE counter v2(3^k-1), except only when v2(k)=L; exactly there cancellation
raises the valuation further.  The next target is therefore the single
resonant quotient and its raw sibling, rather than an arbitrary long-frame
transition.
Section 79 shows that even this resonance cannot repeat: every valuation at
least two is followed by valuation one whose source is an exact lift over
the resonant source, while every valuation-one row takes one ordinary
selected-source step next (or remains at the directly factored terminal
source zero).  The remaining proof obligation is now an
outcome diamond forcing a DRAW-marked factor scan to expose the carried
height-one terminal token before it can restart through that ordinary
source step.
Section 80 supplies the bounded outcome scan: every DRAW exponent-two/one
frame exposes a raw or signed DRAW exit at its current or next factor
level.  Together with Section 79, the resonant level and its valuation-one
successor are the complete local horizon.  The remaining task is now to
attach both raw exits in this four-state diamond to the terminal token
B(s)=0 (or prove a strict source/height return).
Section 81 types both raw exits.  At higher valuation they are simply the
lower member of the signed adjacent frame; at valuation one, every positive
raw DRAW has coefficient source strictly below the signed returned source
(and source zero gives the terminal raw state).  The four-exit diamond is
therefore reduced to an adjacent frame, an exponent-one lift, or strict
source descent.  The remaining global step is to compare the two coupled
signed sources with the carried proof-height token.

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
