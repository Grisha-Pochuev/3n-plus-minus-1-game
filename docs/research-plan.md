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
`A`-selecting exponent-one/two obligation with source in `[s,2s)`.

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
