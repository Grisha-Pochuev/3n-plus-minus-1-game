# Long Pro research session: high-return provenance frontier — 14 August 2026

Status: **OPEN — RED**.

This note records the long Pro research session of 14 August 2026 (about 122 minutes as recorded in the chat) and the immediately following analysis. It is a research handoff, not a proof of the no-DRAW theorem. Its purpose is to preserve both the strongest positive results and the repairs that were explicitly falsified, so that a future clean restart does not repeat the same work.

This note should be read together with:

- `docs/high-return-lifecycle-handoff-2026-08-14.md`;
- `docs/high-return-provenance-obligation.md`;
- `docs/d2-loss-anchored-obligation.md`;
- `docs/certificate-transport-shadow-lemma-2026-08-14.md`;
- Sections 79--103 and 129--136 of `docs/verified-results.md`.

The branch also contains the arithmetic regression

```text
scripts/verify_high_return_shadow_words.py
```

which checks the shadow-word identities described below. The script is supporting arithmetic evidence only and does not prove token provenance.

## 1. Exact red gap at the beginning of the session

For a long high return with `v >= 7`, Sections 100--103 provide local finite-outcome geometry

\[
(u,c)\longmapsto(p,b)\longmapsto(q,y),
\]

with the relevant WIN/LOSS states finite and with strict local proof-height inequalities.

This is not yet a legal Section 129 token-rank transition. A token decrease is legal only when an exact incoming retained proof occurrence is replaced by certified descendants of that same occurrence. The states `u,c` are produced arithmetically at the high return, but the proof has not established that the corresponding occurrences were already present in the incoming ranked configuration.

The forbidden repair is therefore:

> `u,c` are finite, so insert them now, and then use the local inequalities to compare them with `p,b,q,y`.

That is a reseed, not a rank decrease.

The direct `D=2` module has the same logical proviso. It is locally correct once an incoming occurrence `q*` is already retained, but it does not install `q*`.

## 2. Positive result: finite arithmetic shadow words from the retained LOSS occurrence

At the Section 91 factor alternative retain the exact finite LOSS occurrence `V*`. Put

\[
E=A(V)=Q_r^e(a),\qquad g=1-e.
\]

The long-tail recurrence implies that every boundary exponent reached from `E` occurs at one of the finitely many factor levels

\[
K(r)=\left\{k:\left\lceil\frac{r-2}{2}\right\rceil\le k\le r-1\right\}.
\]

Equivalently,

```text
k = floor((r-1)/2), ..., r-1.
```

For `k <= r-2`, define

\[
\alpha=2k-r+2,\qquad \beta=r-k-2.
\]

Then `alpha,beta >= 0`, `alpha+beta=k`, and the fixed word

\[
W(r,k)=A^\alpha B^\beta
\]

sends

\[
E\longmapsto Q_2^e(3^k a).
\]

At the final level `k=r-1`, the word

\[
W(r,r-1)=A^{r-1}
\]

sends

\[
E\longmapsto Q_1^e(3^{r-1}a).
\]

Thus the arbitrary factor exponent does not produce an arbitrary collection of arithmetic paths: before the boundary it is covered by a finite symbolic family determined by `r`.

## 3. Positive result: universal terminal words for current- and next-level high return

Put `C=3^k a`.

If

\[
3C+1-2g=2^vT,\qquad v\ge 4,
\]

then for either boundary exponent `d=1,2`,

\[
B(Q_d^e(C))=Q_{v-2}^e(T)
\]

and hence

\[
BA(Q_d^e(C))=Q_{v-3}^e(3T).
\]

This is exactly the returned long-high state `c`.

If the current valuation is one,

\[
3C+1-2g=2T,
\]

and the next factor level is high,

\[
9C+1-2g=2^vS,\qquad v\ge4,
\]

then the exact terminal words are

\[
BAA(Q_1^e(C))=Q_{v-3}^e(3S),
\]

and

\[
ABA(Q_2^e(C))=Q_{v-3}^e(3S).
\]

Together with Sections 79--80, these words cover the current exposed factor level and the immediately following level, which is sufficient because the consecutive-factor scan cannot postpone the relevant high event beyond that two-level horizon.

The resulting finite family of paths from `V` is therefore:

- `A W(r,k) BA` for a current-level high return;
- `A W(r,k) ABA` for a next-level high return from exponent two;
- `A W(r,r-1) BAA` for a next-level high return from exponent one.

The leading `A` is the retained edge `V -> E`.

## 4. Regression for the arithmetic lemma

The branch script

```text
python scripts/verify_high_return_shadow_words.py
```

was run at the default source limit. The recorded output was

```text
HIGH_RETURN_SHADOW_WORDS_OK
factor entries checked: 100000
canonical boundary paths checked: 166670
current-level long returns checked: 2597
next-level long returns checked: 2601
scope: arithmetic identities only; no proof-token theorem inferred
```

The important scope restriction is the last line. This checks exact arithmetic identities, not the global no-DRAW theorem and not occurrence provenance.

## 5. Positive result: first-divergence payment from a fixed proof tree

Let `T(V*)` be the fixed finite proof tree of the retained occurrence `V*`, and compare one of the fixed arithmetic shadow paths

\[
V=z_0\to z_1\to\cdots\to z_m=c
\]

with that proof tree.

There are two cases.

1. The whole path is contained in the tree. Then the endpoint occurrence is a certified proper descendant of `V*`.
2. The path first leaves the tree at an edge out of a WIN occurrence. It cannot first leave at a LOSS occurrence, because the finite proof of a LOSS node contains both children. At the first WIN divergence the proof tree already contains its selected LOSS child, which is a certified proper descendant of `V*`.

Therefore every selected long arithmetic shadow path exposes a genuine strict descendant of `V*` without changing the proof choice after the branch has been seen.

This is a real provenance theorem and should be retained.

## 6. Critical correction: this still does not close the lifecycle

An initially tempting conclusion was that the strict `V* -> descendant` payment could simply be used to install the later high-return pair `(q,y)`. That is incorrect.

The `V*` payment and the later `(q,y)` pair currently live in the same inner token/rank component. A strict decrease in a rank component does **not** permit that same component to be arbitrarily reset to a freshly inserted incomparable pair immediately afterward.

Thus the following implication is invalid:

> a strict descendant of `V*` was found earlier on the route, therefore the later finite pair `(q,y)` may now be installed freely.

To make such a reset legal, one needs either:

- a strict decrease in a genuinely earlier rank coordinate, so that a later coordinate is allowed to reinitialize; or
- a proof that the required outgoing occurrences are already present inside a retained occurrence-tagged certificate forest and are therefore descendants/carried occurrences rather than newly created tokens.

This is the same logical obstruction identified by the lifecycle handoff. The shadow-word lemma narrows it but does not remove it.

## 7. Structural asymmetry discovered in the long-high pair

The local Section 103 geometry has an important asymmetry that should guide future work.

The intended chain includes

\[
c\text{ WIN},\qquad B(c)\text{ LOSS},
\]

and later a WIN state `b` which is a child of `B(c)`, with `y` the LOSS child selected from `b`. Therefore there is a proof-compatible alternating route from the `c` side to `y`:

```text
c WIN -> B(c) LOSS -> b WIN -> y LOSS.
```

By contrast the `q` branch uses `p=A(c)` with both `c` and `p` WIN in the local geometry. A finite proof certificate for a WIN occurrence follows a selected LOSS child; it does not automatically contain an arbitrary WIN child. Therefore `q` is not naturally a descendant of the same `c*` proof occurrence.

This explains why attempts to carry `(q,y)` symmetrically are structurally unnatural.

## 8. Computational discovery: `V -> y` is much more natural than `V -> q`

A local bounded retrograde computation was used for discovery only. It is not part of the proof.

In resolved high-return examples satisfying the expected finite outcomes (`V LOSS`, `c/p/b/q WIN`, `y LOSS`), compatible certificate-tree paths from `V` to `y` were repeatedly found, while compatible paths from `V` to `q` were not.

At a larger local bound the same pattern persisted in all checked resolved rows: `V -> y` had a compatible path; `V -> q` did not.

This should not be promoted to a theorem without a symbolic proof, but it strongly suggests that a future rank should be anchored on the LOSS side `y`, not on a symmetric pair `(q,y)`.

A separate discovery BFS over the first several thousand arithmetic high-return rows found direct game words from `V` to the later numerical state `y` in every tested row. Many word patterns occurred (dozens, not one fixed bounded word), so the phenomenon appears recursively structured rather than fixed-depth.

The correct future question is therefore not "is there one bounded word from V to y?" but "is there a symbolic family of proof-compatible `V -> y` words generated by the tail/factor recursion?"

## 9. Concrete examples of the `V -> y` phenomenon

Examples observed during the discovery computation included paths such as

```text
35042 LOSS
 -> 52563 WIN
 -> 78845 LOSS
 -> 118268 WIN
 -> 11087 LOSS
 -> 16631 WIN
 -> 12473 LOSS
```

with word `AAABAB`.

The high-return arithmetic path to `c` from the same starting area was different. This is important: the proof-compatible path to `y` need not be the actual arithmetic high-return route to `c`; it may run through the opposite certificate branch.

Other rows produced different but still alternating compatible words. This reinforces the idea that the proof object may need to contain a preinstalled branching forest rather than one canonical arithmetic route.

The numerical examples above are exploratory evidence only. Reproduce and independently commit any example that is later used in a formal lemma.

## 10. `D=2`: most rows look `y`-anchorable, exceptional rows remain the sharp local obstruction

For the marked tail after a high return:

- `D>=3` is already paid locally from the retained LOSS side `y` by Section 135;
- `D=1` also pays from `y` by an actual-child replacement;
- `D=2` is the difficult short row.

For ordinary `D=2` orientations, the existing side relation suggests that the WIN endpoint used by the short-lift analysis is itself a proper child/descendant of the retained LOSS occurrence `y*`. If formalized, this would make ordinary `D=2` another `y`-anchored payment and would remove the need for a separately installed `q*` in those rows.

The remaining exceptional orientations are exactly the familiar congruence rows

```text
b == 12 (mod 16), g = 0
b ==  3 (mod 16), g = 1.
```

There the ordinary common-child identity fails. The current direct module uses the WIN token `q*`, and that is precisely the occurrence whose provenance is not supplied by the `y`-anchored picture.

This makes the exceptional `D=2` rows a much sharper local target than the entire previous Section 136 lifecycle.

## 11. Promising next attack on exceptional `D=2`

The exceptional formulas produce adjacent lifts over the actual LOSS state `y`:

\[
p=B(q)=Q_r^\varepsilon(J(y)),
\]

\[
v=A(q)=Q_{r+1}^\varepsilon(J(y)),
\]

with an exact common child in the exceptional side diamond.

Because `y` is LOSS, both of its ordinary children are finite WIN descendants. Sections 57--64 of the supplement contain earlier LOSS-source transport lemmas and should be re-audited specifically against this exceptional lift.

A successful theorem of the following form would be enough to eliminate the most obvious need for `q*`:

> every exceptional `D=2` direct DRAW lift over retained `y* LOSS` exposes a certified proper descendant of `y*` before any new high-return witness must be installed.

This has not yet been proved.

## 12. Candidate repairs explicitly rejected during this session

The following ideas should not be reintroduced without new mathematics.

### 12.1 Source rank

Returned coefficient sources can increase. The lifecycle handoff already records an explicit increase `16573 -> 22399`. Source alone cannot rank high returns.

### 12.2 Canonical proof height of the numerical shadow state

A useful compatible high-return proof path need not be the canonical minimum-height proof path of the same WIN state. A previously recorded counterexample has a canonical WIN height much smaller than the compatible branch required by the high-return shadow.

Thus silently replacing a canonical proof occurrence by a taller branch-compatible proof occurrence is itself a hidden rank increase.

### 12.3 Mere numerical reachability

If a finite state `z'` is reachable from a retained finite state `z`, it does not follow that the retained proof occurrence of `z` contains `z'`. At WIN nodes the chosen proof child matters.

### 12.4 Fixed local depth

No fixed small-depth neighbourhood search can replace the unbounded symbolic factor/tail argument.

### 12.5 A free one-shot reseed inside the same token coordinate

A control bit can justify initialization of a *later* coordinate after an earlier strict decrease. It cannot turn an arbitrary insertion into a token descendant inside the very coordinate that is supposed to be decreasing.

## 13. Preinstalled occurrence-tagged forest remains the strongest completion theorem for the old architecture

The old architecture would become sound if one could prove a preinstalled compatible shadow-forest theorem.

At the Section 91 factor entry, begin with exact finite occurrences (at least the retained `V* LOSS`, and any other genuinely inherited finite occurrence supplied by the prior macro configuration). Before future DRAW branching is observed, construct a finite occurrence-tagged forest such that:

1. every equal-rank arithmetic/factor route until the next strict payment is represented;
2. each WIN occurrence has its needed LOSS choice already installed before branching;
3. each LOSS occurrence contains both children;
4. every maximal branch reaches a genuine source decrease or a proper descendant of an incoming retained occurrence;
5. equal-rank routing preserves the same forest identity;
6. no branch may discard the forest and rebuild a taller incompatible certificate for the same numerical state;
7. the actual DRAW carrier remains separate from the finite proof forest.

The new shadow-word lemma contributes to item 1 by proving a finite symbolic family of boundary paths. It does not yet prove items 4--6.

## 14. Why the old pair rank now looks structurally suspect

The long session changed the qualitative assessment of the proof architecture.

Repeated audits have not found merely isolated arithmetic slips. The recurrent failure mode is the same: local finite states are correct, but the global rank silently changes which proof occurrence is being carried.

The asymmetry between `q` and `y` strengthens this concern. The local arithmetic naturally produces a pair, but the proof-tree ancestry appears to prefer a single LOSS-anchored thread.

Therefore a future proof should not assume that the symmetric pair `(q,y)` is the right fundamental ranked object merely because Section 103 supplies convenient local height inequalities for that pair.

## 15. Strategic conclusion after the session

The project should now split into two conceptual tracks.

### Track A: preserve the old architecture as a bounded research problem

Do not rewrite the whole manuscript again. Keep the old proof frozen with status **OPEN — RED** and attack only the precise lifecycle theorem:

- either prove the occurrence-preserving forest theorem;
- or reduce it to a sharper `y`-anchored theorem plus the exceptional `D=2` rows;
- or produce a structural counterexample showing that incompatible future WIN choices make a finite ranked forest impossible.

If this track succeeds, the existing large body of local lemmas may still yield a complete proof.

### Track B: start a clean proof architecture from the verified local library

Independently restart the global no-DRAW argument from the reliable local components only:

- the binary conjugation;
- `B(q)<q`;
- constant-tail identities;
- embedded source/factor identities;
- finite WIN/LOSS proof recursion;
- locally verified diamonds and reverse-factor normalization.

The clean proof should search for a global well-founded object that is native to DRAW dynamics rather than repeatedly attaching and reseeding auxiliary proof tokens.

Promising families include:

- a rank directly on typed DRAW configurations;
- a minimal infinite DRAW path with a structural shortening argument;
- a finite/tree automaton of tail/factor types whose transition relation is itself well-founded;
- a single inherited proof forest whose identity is part of the state from the beginning.

## 16. Falsification track

In parallel, continue trying to falsify the theorem/architecture computationally.

The goal of computation is not to prove no DRAW by a finite bound. Instead search for:

- large strongly connected structures;
- paths that force incompatible proof choices;
- repeated high-return episodes with no identifiable inherited descendant;
- exceptional `D=2` configurations that defeat every `y`-anchored repair;
- candidate cycles in any proposed new abstract rank.

A counterexample to a rank candidate is a success: it prevents another manuscript-sized false closure.

## 17. Recommended next reading order for a clean restart

Before starting a new proof attempt:

1. read this note;
2. read `docs/high-return-lifecycle-handoff-2026-08-14.md`;
3. treat `docs/certificate-transport-shadow-lemma-2026-08-14.md` as a proved arithmetic/provenance partial result, not closure;
4. re-audit Sections 57--64 for exceptional `D=2` LOSS-source transport;
5. re-audit Sections 79--90 for the exact finite symbolic factor horizon;
6. use Sections 91--103 only as a library of local geometry, not as a globally ranked proof;
7. use Section 129 only with exact occurrence identities.

## 18. Acceptance rule

No future manuscript should state that the no-DRAW theorem is proved until an adversarial audit can answer all of the following without an implicit reseed:

- What exact proof occurrences enter each macro?
- Which exact incoming occurrence is replaced at every strict token step?
- Is every outgoing ranked occurrence a certified descendant of an incoming occurrence, or does an earlier rank coordinate strictly decrease before reinitialization?
- If the numerical state repeats, is the proof occurrence/forest literally the same ranked object?
- Can two future DRAW-compatible branches demand incompatible WIN proof choices?
- Is the equal-rank relation well-founded after occurrence identity is included in the state?

Until those questions are answered, the correct global status is **OPEN — RED**.

## 19. Commits preceding this handoff on the research branch

The long-session work was developed on branch

```text
agent/high-return-shadow-prepayment
```

with the following preceding commits:

```text
3d9e3078a76309595bfebbb9e000873d7d4176e4  Add high-return shadow-word regression
68359d8d8b41d4b6eb86ec1c3370e3e1469755f4  Add shadow transport note
45ab7e3ebecfb769400374943a6d3da81c366b22  Add note
```

The last of these corrected an overclaim in the intermediate note: the shadow payment is a partial provenance result and does **not** by itself authorize later `(q,y)` reseeding.

That correction is essential and should not be reverted.
