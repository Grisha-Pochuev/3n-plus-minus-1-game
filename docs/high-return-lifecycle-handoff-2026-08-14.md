# High-return lifecycle handoff — 14 August 2026

Status: **OPEN — RED**.  This file is a research handoff, not a proof of the
no-DRAW theorem.  It records the strongest results and falsifications reached
in the August 12–14 investigation so that work can continue in another chat
without reconstructing the frontier.

Base repository state reviewed during this work: `main` at
`eedeb8dced3d19fa7046626828cab608876fca32` (the repository may advance after
this handoff).

## 1. Decisive remaining obligation

The red gap is the long high-return lifecycle in Section 136.

For `v >= 7`, Sections 100–103 prove local finite-outcome geometry of the
form

\[
u=Q_{v-1}^g(J(t)),\qquad
c=Q_{v-3}^g(3J(t)),
\]

followed by

\[
(u,c)\longmapsto(p,b)\longmapsto(q,y),
\]

with the relevant states finite and with componentwise proof-height drops.
Those inequalities are **local**.  They do not by themselves justify a
multiset-rank transition, because Section 129 permits a token decrease only
for exact retained proof-token occurrences already present in the incoming
configuration.

The forbidden shortcut is

> `u,c` are finite, therefore insert them into the token multiset and compare
> them with `p,b` or `q,y`.

That is precisely the reseeding problem.

The separate direct `D=2` marked-tail module is locally closed: once the
incoming occurrence of `q WIN` is legally retained, every orientation of the
direct DRAW lift replaces that occurrence by a certified proper proof-tree
descendant.  This does **not** install `q`; it therefore shares the same
lifecycle obligation.

Read first:

- `docs/high-return-provenance-obligation.md`
- `docs/d2-loss-anchored-obligation.md`
- Sections 79–103 and 129–136 of `docs/verified-results.md`

## 2. Repairs already falsified

Do not reuse any of these.

### 2.1 Returned source need not decrease

A returned arithmetic source may increase.  One explicit path already found
is

\[
16573\longrightarrow22399.
\]

Thus source monotonicity cannot be the global rank.

### 2.2 A natural arithmetic path need not be the chosen proof-tree path

It is invalid to infer that because a later finite state is reachable from an
old finite state, it is automatically a descendant of the **retained
canonical proof occurrence**.  A WIN proof chooses one LOSS child; a different
arithmetic continuation may use the other child.

### 2.3 No fixed local depth can close the gap

The configuration around

\[
49,710,269\longrightarrow136,202,515
\]

survives a depth-six hostile neighbourhood test, and a parameterized example
above `3*10^18` survives depth eight.  Fixed-depth contradiction search is
therefore evidence only, not a proof strategy.

### 2.4 Source-only and side-height ranks are false

The equal-canonical-source state graph already contains `1 -> 2 -> 1`.
Successive arithmetic side-WIN heights are also not monotone (see
`docs/rank-candidate-falsification-2026-08-12.md`).

## 3. First-exit lemma for proof trees

A useful general lemma survives the audit.

Let `T` be a finite proof tree for a retained finite token `z`, and let

\[
z=z_0\to z_1\to\cdots\to z_m
\]

be any directed game path.

Either the whole path lies in `T`, or consider the first edge that leaves
`T`.  It cannot leave at a LOSS node, because a LOSS proof contains both
children.  Hence first exit occurs at a WIN node.  The proof tree contains a
chosen LOSS child there, and that child is a certified strict descendant of
the incoming token occurrence.

Therefore a path that diverges from a retained proof tree does expose a real
lower proof-tree token at the first divergence.

Important limitation: this lemma does **not** permit that lower token to be
forgotten and an unrelated pair to be installed later.  Either the lower
occurrence must remain in the ranked configuration, or some earlier rank
coordinate must already have decreased before the reset.

## 4. Factor-free two-level high-return shadow

For a factor-free WIN source `b` and phase `f`, define

\[
N_1=9J(b)+1-2f,\qquad
N_2=27J(b)+1-2f.
\]

The consecutive-factor identity gives

\[
N_2=3N_1-2(1-2f),
\]

so

\[
v_2(N_1)\ge2\Longrightarrow v_2(N_2)=1.
\]

Thus a valuation at least seven in this two-level horizon occurs either at
the first exposed level, or after a valuation-one first level.

The corresponding residue classes modulo 128 are finite and, in the
factor-free two-level situation, exclude the four exceptional ordinary-side
classes `1,3,12,14 (mod 16)`.  In those rows the ordinary common child

\[
r=B(A(b))
\]

is a child of either ordinary child of `b`.  If `b` is a retained WIN
occurrence and `ell` is its canonical LOSS child, then `r` is a WIN child of
`ell`, hence

\[
h(r)\le h(b)-2.
\]

This is a genuine strict token replacement **when the incoming occurrence
`b` is actually retained**.

This does not by itself solve arbitrary factor level: exceptional sources can
occur at higher factor levels.  The explicit example found during this work
was

\[
b=62,\qquad f=1,\qquad k=4,
\]

for which

\[
3^5J(62)-1=45440=2^7\cdot355=2^7J(118),
\]

while `62 == 14 (mod 16)` is exceptional.  Thus one cannot globally replace
the arbitrary-factor induction by the ordinary common-child identity.

## 5. Reverse factor normalization remains essential

Sections 87–89 / the Althöfer repair predecessor reduction give the correct
way to treat arbitrary factor exponent.

For an exponent-one factor state

\[
R_k=Q_1^e(3^kJ(s))
\]

that is DRAW, the reverse analysis gives either:

1. a pullback to a factor-free DRAW over the same source; or
2. a marked `LOSS/DRAW` gate.

In the gate, the predecessor is either DRAW (allowing legitimate factor
removal at exponent two) or WIN, in which case its other child is an actual
LOSS proof token.  The nonexceptional branch exposes a lower WIN descendant;
the exceptional branch returns an exact adjacent frame over that LOSS token.

Hence arbitrary factor level cannot simply be called an unmarked reset.  The
remaining difficulty is to turn this reverse normalization into one global
**occurrence-preserving** induction that reaches the next long high return
without reseeding.

## 6. Canonical source-shadow rank is false

A major negative result of this chat is that a state lying on a useful
alternating WIN/LOSS shadow path need not use that path in its canonical
minimum-height WIN proof.

A concrete computationally obtained finite example is:

\[
C=313813,\qquad e=0,
\]

with

\[
3C+1=941440=2^7\cdot7355=2^7J(2451).
\]

For the associated shadow states,

\[
z_1=Q_1^1(C)=627625,
\]

and

\[
d=Q_5^1(J(2451))=235359.
\]

The finite retrograde calculation used in this chat gave

\[
z_1\text{ WIN},\quad h(z_1)=31,
\]

\[
d\text{ LOSS},\quad h(d)=54.
\]

The other LOSS child of `z_1` has height 30, so the canonical WIN proof for
`z_1` chooses that other child.  The useful high-return shadow path through
`d` is therefore a valid finite proof path but not the canonical one.

The marked LOSS state later on that path was computed as

\[
y=595754,\qquad h(y)=50,
\]

so

\[
h(y)=50>31=h(z_1).
\]

This refutes the shortcut

> the canonical height of the shadow-source state automatically decreases to
> the later marked token.

Before promoting these particular numerical heights into the formal proof
record, re-run the finite certificate computation and commit the reproducer.
The logical lesson does not depend on using canonical height as a new rank:
canonical state height is insufficient for the desired shadow transport.

## 7. Compatible noncanonical proof paths exist

The failure above does **not** mean the useful shadow path is invalid.

If a finite directed path has alternating finite outcomes

\[
\text{WIN},\text{LOSS},\text{WIN},\text{LOSS},\ldots,
\]

then there exists a finite proof tree for its first WIN state containing the
whole path:

- at every LOSS node the proof contains both children automatically;
- at every WIN node choose the next LOSS node on the desired path as the
  proof child;
- attach any finite proof tree below the last finite state.

Therefore the high-return shadow can be embedded in a finite proof
certificate.  The problem is that this certificate can be taller than the
canonical certificate already retained for the same numerical state.  In the
example above the compatible certificate through `d` starts with height at
least `1+h(d)=55`, whereas the canonical state height is 31.

So silently changing

\[
(z,\text{canonical certificate})
\]

to

\[
(z,\text{branch-compatible certificate})
\]

would be a hidden rank increase / reseed, even though the numerical state is
unchanged.

## 8. Current sharp frontier: preinstalled compatible shadow forest

The remaining promising theorem is no longer about numerical source descent.
It is about **proof-certificate choice before branching**.

A sufficient theorem would be:

### Preinstalled compatible shadow-forest theorem

At entry into the factor alternative of Section 91, the macro configuration
contains exact retained occurrences such as

\[
b^*\text{ WIN},\qquad V^*\text{ LOSS}.
\]

Before any raw/signed branch is selected, construct a finite occurrence-tagged
proof forest covering every outcome-compatible factor/high-return path until
the next certified strict source/token payment.

The forest must satisfy:

1. **Finiteness.**  It is finite by symbolic factor/tail counters, not by a
   numerical search cutoff.
2. **Coverage.**  Every legal zero-rank raw/signed/factor transition before
   the next payment follows an edge represented in the forest.
3. **WIN choice preinstallation.**  If a future path requires a noncanonical
   LOSS child of a WIN state, that choice is already present in the incoming
   forest; it is not installed after seeing the future branch.
4. **LOSS completeness.**  Both children of every retained LOSS occurrence
   are present, as required by finite outcome recursion.
5. **Strict exit.**  Every maximal forest branch reaches either a genuine
   source decrease or a certified proper descendant of an already retained
   occurrence before any new high-return pair is installed.
6. **No reseed.**  With all earlier rank coordinates fixed, no transition may
   discard this forest and build a different taller forest for the same
   numerical state.
7. **DRAW separation.**  The actual DRAW carrier is separate from the finite
   proof forest throughout.

If this theorem is proved, the fresh `u,c` states of Sections 100–103 can be
reclassified as **temporary arithmetic cursors**, not proof-token rank
components.  Their local height inequalities remain useful but are no longer
needed to justify their installation.

## 9. What has NOT been proved

Do not claim any of the following on the basis of this handoff:

- that the red Section 136 lifecycle gap is closed;
- that the preinstalled shadow forest is finite for all arbitrary factor
  routes;
- that canonical proof height is monotone along the shadow path;
- that equality of numerical state or coefficient source identifies the same
  proof-token occurrence;
- that any finite computation proves absence of DRAW.

The global theorem remains open until the forest/lifecycle theorem (or a
different global rank) is proved.

## 10. Recommended continuation order

For the next research chat:

1. Read this file.
2. Read `docs/high-return-provenance-obligation.md` and
   `docs/d2-loss-anchored-obligation.md`.
3. Re-read Sections 79–90, 91–103, and 129–136 of
   `docs/verified-results.md`.
4. Treat Sections 87–89 predecessor normalization as the induction step for
   arbitrary factor exponent.
5. Attempt to define the preinstalled forest recursively on the factor level
   and the exact tail exponent, with occurrence identities part of the state.
6. Prove a symbolic bound showing every zero-rank branch reaches one of the
   strict payments of Sections 57–64, 87–89, 94–96, or 130–135 before the
   forest must be rebuilt.
7. If the forest theorem is false, produce the smallest exact configuration
   in which two future DRAW-compatible branches require incompatible WIN
   proof choices whose least common preinstalled forest cannot be ranked.

## 11. Acceptance criterion for removing RED

The red status may be removed only after the manuscript has all of:

- an exact macro-configuration type containing occurrence-tagged proof
  certificates (not only state numbers/heights);
- an exhaustive entry/exit table for arbitrary-factor long high return;
- a proof that every zero-rank edge preserves the same certificate forest;
- a proof that every later high-return visit occurs only after a strict
  earlier-coordinate payment;
- a well-founded ordinal/rank for the resulting forest relation;
- a semantic refinement showing every actual DRAW continuation enters one of
  those table rows.

Until then the correct project status is **OPEN — RED**, with the local
arithmetic and local token-payment lemmas retained as proved components.
