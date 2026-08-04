# Proof ledger

Update this table whenever the status of a substantial claim changes.

| Claim | Status | Location / evidence |
|---|---|---|
| Original game is exactly represented by `F(m), F(R(m))` in `m=(n-1)/2` coordinates | **PROVED** | `docs/normal-form.md`; finite regression tests in `tests/test_game.py` |
| Conjugated game is `A(q)=F(q)`, `B(q)=R(F(q))` | **PROVED** | `docs/normal-form.md` |
| `B(q)<q` for every `q>0` | **PROVED** | `docs/normal-form.md` |
| `D(D(n))<n` unless `D(n)=1` | **PROVED** | `docs/verified-results.md` |
| `D(U(D(n)))<n` unless the game already ended | **PROVED** | `docs/verified-results.md` |
| Always choosing `D` forces finite termination | **PROVED** | `docs/verified-results.md` |
| Always choosing `D` forces a win | **FALSE AS AN INFERENCE** | The descent argument does not determine who makes the terminal move |
| Minimal draw implies the entire chain `d,A(d),A^2(d),...` is drawn | **DISPROVED AS AN ARGUMENT** | `docs/pitfalls.md` |
| A fixed small horizon of side branches always contains a losing node | **DISPROVED for several proposed small constants** | inherited exploratory counterexamples; see `docs/unverified-leads.md` |
| A fixed modulus `2^K` determines `R` | **FALSE** | `docs/normal-form.md` |
| In Gray coordinates, `R` deletes the trailing ones and the preceding zero via `G(R(x))=G(x)>>(v2(G(x)+1)+1)` | **PROVED** | `docs/normal-form.md`; `alternating_suffix_remainder_via_gray` |
| Bounded retrograde labels and extracted proof DAGs are sound | **PROVED FOR THE IMPLEMENTATION LOGIC** | `src/optimal_3n1/retrograde.py`; `scripts/extract_proof.py`; `tests/test_retrograde.py` |
| Outside `q=1,3,12,14 mod 16`, consecutive side branches satisfy `B(A(q))=A(B(q))` or `B(A(q))=B(B(q))` | **PROVED** | `docs/verified-results.md`, Section 5; `side_branch_relation` |
| Four consecutive positions on one `A`-ray cannot all be `WIN` | **PROVED** | `docs/verified-results.md`, Section 5 |
| All predecessors through `B` are parameterized by attached alternating words | **PROVED** | `docs/verified-results.md`, Section 6; `transformed_B_predecessors` |
| The block `B(B(A(q)))` is smaller than `q` for every `q>0` | **PROVED** | `docs/verified-results.md`, Section 7; `transformed_BBA` |
| A nonempty result from `certified_finite_draw_kernel` is a genuine finite DRAW countercertificate | **PROVED FOR THE IMPLEMENTATION LOGIC** | `docs/verified-results.md`, Section 8; `scripts/find_finite_draw_kernel.py` |
| Every starting value is `WIN` or `LOSS`, with no `DRAW` | **OPEN** | main problem |
| All odd starts below a large bound have been solved by the current code | **UNVERIFIED UNTIL REPRODUCED** | run scripts locally and record exact output |
| A finite-state transducer plus rank can prove the theorem | **CONJECTURAL PROGRAM** | `docs/research-plan.md` |
