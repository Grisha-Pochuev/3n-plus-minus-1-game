# Proof ledger

Update this table whenever the status of a substantial claim changes.

| Claim | Status | Location / evidence |
|---|---|---|
| Original game is exactly represented by `F(m), F(R(m))` in `m=(n-1)/2` coordinates | **PROVED** | `docs/normal-form.md`; finite regression tests in `tests/test_game.py` |
| Conjugated game is `A(q)=F(q)`, `B(q)=R(F(q))` | **PROVED** | `docs/normal-form.md` |
| `B(q)<q` for every `q>0` | **PROVED** | `docs/normal-form.md` |
| `D(D(n))<n` unless `D(n)=1` | **PROVED** | `docs/verified-results.md` |
| `D(U(D(n)))<n` unless the game already ended | **PROVED** | `docs/verified-results.md` |
| One chosen player always choosing `D` forces finite termination | **DISPROVED** | `5 -> 7 -> 5` with the opponent choosing `U`; `docs/verified-results.md`, Section 3 |
| Always choosing `D` forces a win | **FALSE** | The same `5 -> 7 -> 5` response already prevents termination |
| Minimal draw implies the entire chain `d,A(d),A^2(d),...` is drawn | **DISPROVED AS AN ARGUMENT** | `docs/pitfalls.md` |
| A fixed small horizon of side branches always contains a losing node | **DISPROVED for several proposed small constants** | inherited exploratory counterexamples; see `docs/unverified-leads.md` |
| A fixed modulus `2^K` determines `R` | **FALSE** | `docs/normal-form.md` |
| In Gray coordinates, `R` deletes the trailing ones and the preceding zero via `G(R(x))=G(x)>>(v2(G(x)+1)+1)` | **PROVED** | `docs/normal-form.md`; `alternating_suffix_remainder_via_gray` |
| The Gray-coordinate expanding move `Gamma` is recognized exactly by an eight-state LSB-first transducer | **PROVED** | `docs/normal-form.md`; `src/optimal_3n1/transducer.py`; exhaustive regression in `tests/test_game.py` |
| Bounded retrograde labels and extracted proof DAGs are sound | **PROVED FOR THE IMPLEMENTATION LOGIC** | `src/optimal_3n1/retrograde.py`; `scripts/extract_proof.py`; `tests/test_retrograde.py` |
| Outside `q=1,3,12,14 mod 16`, consecutive side branches satisfy `B(A(q))=A(B(q))` or `B(A(q))=B(B(q))` | **PROVED** | `docs/verified-results.md`, Section 5; `side_branch_relation` |
| All four exceptional side branches have the explicit affine/reduced formulas in Section 5 | **PROVED** | `docs/verified-results.md`, Section 5; `exceptional_side_branch_values` |
| Every long exceptional suffix has the uniform `(r,k,e)` formula of Section 5 | **PROVED** | `docs/verified-results.md`, Section 5; `long_side_branch_value` |
| Four consecutive positions on one `A`-ray cannot all be `WIN` | **PROVED** | `docs/verified-results.md`, Section 5 |
| All predecessors through `B` are parameterized by attached alternating words | **PROVED** | `docs/verified-results.md`, Section 6; `transformed_B_predecessors` |
| Every length-three word with one `A` and two `B` moves is smaller than its input | **PROVED** | `docs/verified-results.md`, Section 7; `transformed_BBA`, `transformed_BAB`, `transformed_ABB` |
| A nonexceptional three-vertex `WIN` path has endpoint `B(A(q))` and decreases finite proof height by at least two | **PROVED** | `docs/verified-results.md`, Section 9; finite regression in `tests/test_retrograde.py` |
| Every infinite path consisting only of `WIN` positions visits the exceptional classes infinitely often | **PROVED** | `docs/verified-results.md`, Section 9 |
| Every hypothetical DRAW set has a canonical base-draw skeleton; skeleton steps with two or more `B` moves strictly decrease | **PROVED** | `docs/verified-results.md`, Section 10 |
| A smallest DRAW has the exact local `BB`/`BAB` outcome fingerprint of Section 10 | **PROVED** | `docs/verified-results.md`, Section 10 |
| Away from exceptional classes, canonical base-DRAW transitions obey the size-change table of Section 11 | **PROVED** | `docs/verified-results.md`, Section 11 |
| A minimum-proof-height DRAW-to-WIN boundary edge must touch an exceptional residue class | **PROVED** | `docs/verified-results.md`, Section 12 |
| Height-one WIN positions are exactly the positive `s` with `B(s)=0`, and all are exceptional | **PROVED** | `docs/verified-results.md`, Section 13 |
| If `A(q)` is a height-one WIN, then `B(q)` is also a height-one WIN and `q` is LOSS | **PROVED** | `docs/verified-results.md`, Section 13 |
| For odd `a` and `r>=3`, the children of `X_r(a)=a*2^r-1` are `X_(r-1)(3a)` and `X_(r-2)(3a)` | **PROVED** | `docs/verified-results.md`, Section 14; `dyadic_minus_one_children` |
| The boundary states `X_1(a)` and `X_2(a)` have the same `B`-child | **PROVED** | `docs/verified-results.md`, Section 14; regression in `tests/test_game.py` |
| Both constant-tail families `Q_r^epsilon(a)=a*2^r-epsilon` obey the same closed recurrence for `r>=3` | **PROVED** | `docs/verified-results.md`, Section 14; `constant_tail_children` |
| At `r=1`, the expanding move flips the tail bit and uses the exact signed coefficient map `oddpart(3a+1-2epsilon)` | **PROVED** | `docs/verified-results.md`, Section 14; regression in `tests/test_game.py` |
| The common `B`-child of `Q_1^epsilon(a),Q_2^epsilon(a)` has canonical coefficient at most `(3a+1)/4`, with one resolved equality case | **PROVED** | `docs/verified-results.md`, Section 15; `constant_tail_coordinates`; regression in `tests/test_game.py` |
| A minimum-coefficient DRAW at constant-tail exponent one must take the valuation-one signed transition | **PROVED CONDITIONAL REDUCTION** | `docs/verified-results.md`, Section 15 |
| The second signed transition of a minimum-coefficient exponent-one DRAW has the `v=2`, adjacent-pair `v=3`, or impossible `v>=4` trichotomy | **PROVED CONDITIONAL REDUCTION** | `docs/verified-results.md`, Section 16; arithmetic regression in `tests/test_game.py` |
| A DRAW with coefficient divisible by three and exponent at least two forces a DRAW with coefficient divided by three | **PROVED CONDITIONAL REDUCTION** | `docs/verified-results.md`, Section 16; frame identities in `tests/test_game.py` |
| Every odd coefficient is uniquely `3^k J(s)`, and at `k=0,r=1` the signed transition selects exactly `A(s)` or `B(s)` | **PROVED** | `docs/verified-results.md`, Section 17; `constant_tail_coefficient_source`; `source_boundary_transition` |
| A minimum-source DRAW at `k=0,r=1` must use the phase selecting `A(s)` | **PROVED CONDITIONAL REDUCTION** | `docs/verified-results.md`, Section 17 |
| For odd `w`, the canonical coefficients of `3w` and `3w-1` are `J(R(w))` and `J(R(2w-1))` | **PROVED** | `docs/verified-results.md`, Section 18; regression in `tests/test_game.py` |
| Two exponent-one source lifts return to source `B(A(s))` outside the four exceptional classes; an exceptional return has strictly smaller source | **PROVED** | `docs/verified-results.md`, Section 18; `constant_tail_source_coordinates`; regression in `tests/test_game.py` |
| A minimum-source lifted DRAW can escape its second side child only through a nondecreasing ordinary source return `B(A(s))>=s` | **PROVED CONDITIONAL REDUCTION** | `docs/verified-results.md`, Section 18 |
| The ordinary side return is nondecreasing exactly for `s=0,5,10,15 mod 16`, with the four affine formulas of Section 19 | **PROVED** | `docs/verified-results.md`, Section 19; regression in `tests/test_game.py` |
| In the four phase-mismatch subclasses modulo 32, a minimum-source lifted DRAW forces the exact `LOSS/WIN/DRAW` adjacent-pair fingerprint of Section 19 | **PROVED CONDITIONAL REDUCTION** | `docs/verified-results.md`, Section 19 |
| The ensuing factor-three DRAW has valuation-one expanding child with exact source `3A(B(A(s)))+1` | **PROVED ARITHMETIC IDENTITY; DRAW CONTINUATION OPEN** | `docs/verified-results.md`, Section 19; regression in `tests/test_game.py` |
| The competing child of that factor-three DRAW closes a larger diamond and contradicts the forced LOSS sibling | **PROVED** | `docs/verified-results.md`, Section 20; regression in `tests/test_game.py` |
| A globally minimum-source DRAW lift can make a nondecreasing side return only in the phase-match classes `0,10,21,31 mod 32` | **PROVED CONDITIONAL REDUCTION** | `docs/verified-results.md`, Sections 18--20 |
| In every phase-match return, the common child's coefficient source is below `s`, while the factor-three state's children are adjacent lifts with source equal to that common child | **PROVED** | `docs/verified-results.md`, Section 21; regression in `tests/test_game.py` |
| A long returned suffix occurs exactly for `s=21,63,64,106 mod 128`, and all four classes contradict the minimum-source DRAW hypothesis | **PROVED CONDITIONAL EXCLUSION** | `docs/verified-results.md`, Section 21; regression in `tests/test_game.py` |
| A nonempty result from `certified_finite_draw_kernel` is a genuine finite DRAW countercertificate | **PROVED FOR THE IMPLEMENTATION LOGIC** | `docs/verified-results.md`, Section 8; `scripts/find_finite_draw_kernel.py` |
| Every starting value is `WIN` or `LOSS`, with no `DRAW` | **OPEN** | main problem |
| All odd starts below a large bound have been solved by the current code | **UNVERIFIED UNTIL REPRODUCED** | run scripts locally and record exact output |
| A finite-state transducer plus rank can prove the theorem | **CONJECTURAL PROGRAM** | `docs/research-plan.md` |
| A numerical rank on the coarse two-step exceptional-return abstraction suffices | **DISPROVED** | Exact cycle in `docs/pitfalls.md`, Section 9; regression in `tests/test_game.py` |
