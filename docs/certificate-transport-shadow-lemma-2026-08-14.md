# Certificate transport by finite shadow words

Status: partial result; repository integration is pending.

At the marked input of Section 91, retain occurrence `V*` and put `E=A(V)=Q_r^e(a)`, with parallel phase `g=1-e`.

The reachable boundary levels are exactly

`ceil((r-2)/2) <= k <= r-1`.

For `k<=r-2`, the word `A^(2k-r+2) B^(r-k-2)` sends `E` to `Q_2^e(3^k a)`. For `k=r-1`, the word `A^(r-1)` sends `E` to `Q_1^e(3^(r-1)a)`.

If `3C+1-2g=2^v T`, append `BA`. If the current valuation is one and `9C+1-2g=2^v S`, append `BAA` from exponent one or `ABA` from exponent two. Sections 79--80 show that these words cover the current and immediately following factor levels.

Compare a selected fixed word path from `V*` with its fixed finite certificate tree. If the complete path is present, its endpoint is a proper certified descendant. Otherwise the first absent edge leaves a unary certificate node, whose selected child is a proper certified descendant. Thus every long arithmetic return exposes a strict descendant of `V*` without changing a certificate choice after branching.

Important limitation: the replacement of `V*` and the later pair `(q,y)` currently occupy the same rank component. A decrease there does not by itself justify resetting that same component. Completion still requires either a strictly earlier coordinate for the `V*` replacement, with a complete re-entry rule, or a proof that the needed outgoing occurrences are carried inside the retained certificate forest.

No global closure is claimed by this note. Regression: `python scripts/verify_high_return_shadow_words.py`.
