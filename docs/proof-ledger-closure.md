# Proof-ledger closure overlay — 10 August 2026

This file supersedes only the final `OPEN` status rows in
[`proof-ledger.md`](proof-ledger.md) that were written during the conservative
9 August Althöfer repair. The detailed historical ledger is intentionally not
rewritten: an auditor should be able to see that the theorem was withdrawn
before the missing entry bridge was supplied.

The authoritative new proof of that bridge is
[`althoefer-audit-closure.md`](althoefer-audit-closure.md).

| Claim | Current status | Evidence / dependency |
|---|---|---|
| Corrected Section 136 is well-founded for provenance-preserving typed entries and does not treat temporary `A(x)` growth as retained-source descent | **PROVED FOR TYPED ENTRIES** | Corrected §136; §§91--135; §132 |
| Every arbitrary `Q_1^epsilon(3^k J(s))`, `k>0`, DRAW has the universal two-level arithmetic normalization | **PROVED** | §§79--81; corrected §137 |
| The unbounded factor exponent can be removed or accompanied by an actual strict finite-token descendant | **PROVED** | §16 at exponent >=2; §§68, 87; corrected §137 predecessor reduction |
| The factor-free exponent-two base satisfies `9J(x)+1-2e=2^v J(b)` for its common boundary endpoint `b` | **PROVED** | §§14, 18; corrected §137 |
| B-selecting factor-free exponent-two base entry has next factor valuation exactly `v=1`, with the raw child an actual ordinary child of `b` | **PROVED IN CLOSURE ADDENDUM** | `althoefer-audit-closure.md`, §3.1; finite regression `tests/test_althoefer_closure.py` |
| In the exceptional B-child raw-DRAW orientation, the returned coefficient source is strictly below the old base source | **PROVED IN CLOSURE ADDENDUM** | explicit inequality in closure §3.1 |
| A-selecting factor-free exponent-two base entry has `v>=2`; `v>=4` strictly lowers source; `v=2` is an exact obligation | **PROVED IN CLOSURE ADDENDUM** | closure §3.2 |
| The `v=3` A-selecting constructor automatically satisfies the additional congruence required by Section 89 | **PROVED IN CLOSURE ADDENDUM** | reduction of `9J(x)+1-2e=8J(b)` mod 3 in closure §3.2 |
| A returned inner source may be initialized once even when larger than the outer retained source, without permitting an unranked later reset | **PROVED ORDER-THEORETICALLY** | one-shot entry bit `eta:1->0`; §§129,132; closure §§2,5 |
| Arbitrary factorful exponent-one provenance/rank attachment to the typed Section 136 relation | **PROVED IN CLOSURE ADDENDUM** | corrected §137 + closure §§3--5 |
| Every hypothetical DRAW yields an infinite marked route, while the augmented marked rank is well-founded | **PROVED AS HUMAN ASSEMBLY** | §§129,132,136; closure §6; `global-proof.md` |
| Every odd positive start is WIN or LOSS and optimal play reaches original state 1 in finite time | **HUMAN-PROOF CLAIM RESTORED** | `global-proof.md`; closure §6 |
| Existing JSON global-routing certificate checks the complete one-shot bridge | **NOT CLAIMED** | current JSON predates explicit `eta`; certificate remains `CONDITIONAL_MACHINE_CHECK` for the typed assembly |
| End-to-end Lean formalization of the global theorem | **NOT CLAIMED** | see `formal/COVERAGE.md` |
| Independent external re-audit of the repaired proof | **PENDING** | recommended before a new proof release |

## Interpretation

The final `OPEN — ARBITRARY EXPONENT-ONE ATTACHMENT LEMMA` and
`OPEN IN THIS MANUSCRIPT` rows in `proof-ledger.md` are accurate for the
intermediate 9 August repair revision. They are **superseded on the current
repair branch** by the corresponding `PROVED IN CLOSURE ADDENDUM` and
`HUMAN-PROOF CLAIM RESTORED` rows above.

This overlay does not change the trust boundary: a human proof claim is not a
fully machine-checked proof, and independent mathematical review remains
pending.