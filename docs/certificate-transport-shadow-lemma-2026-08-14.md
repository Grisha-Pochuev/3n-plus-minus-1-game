# Certificate transport by finite shadow words

Status: proved for the exact marked input of Section 91. Repository-wide integration remains pending.

Retain the exact certificate occurrence `V*` and put `E=A(V)=Q_r^e(a)`, where the parallel factor frame has the opposite phase `g=1-e`.

The reachable boundary levels are

`ceil((r-2)/2) <= k <= r-1`.

For `k<=r-2`, the word

`W(r,k)=A^(2k-r+2) B^(r-k-2)`

sends `E` to `Q_2^e(3^k a)`. For `k=r-1`, the word `A^(r-1)` sends `E` to `Q_1^e(3^(r-1)a)`.

If `3C+1-2g=2^v T`, appending `BA` reaches `Q_(v-3)^e(3T)`. If the current valuation is one and `9C+1-2g=2^v S`, append `BAA` from exponent one or `ABA` from exponent two to reach `Q_(v-3)^e(3S)`. Sections 79--80 show that these words cover the current and immediately following factor levels.

Compare the selected fixed word path from `V*` with its already fixed finite certificate tree. If the complete path is present, its endpoint is a proper certified descendant. Otherwise the first absent edge leaves a unary certificate node, and that node's already selected child is a proper certified descendant. Therefore a strict occurrence replacement happens before the new local task is initialized.

The returned arithmetic states are thus cursors rather than newly installed rank entries. The outgoing marked pair is created only after the strict replacement, carried by Sections 104--135, and the direct `D=2` row uses Section 135A. Hence a fixed source/certificate fibre cannot repeatedly reinstall this transition.

Regression: `python scripts/verify_high_return_shadow_words.py`.
