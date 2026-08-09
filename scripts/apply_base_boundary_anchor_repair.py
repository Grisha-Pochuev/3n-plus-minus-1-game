from pathlib import Path
import hashlib
import re


LEMMA = r'''### The first factor signed exit is anchored at the common boundary endpoint

The factor-free exponent-two base entry has a stronger identity than the
preceding general normalization records.  Let \(a\) be any positive odd
integer, let \(e\in\{0,1\}\), and put

\[
P=Q_1^e(a),\qquad U=Q_2^e(a),\qquad
b=B(P)=B(U),\qquad F=A(U)=Q_1^e(3a).
\]

Factor

\[
9a+1-2e=2^v c,\qquad c\text{ odd}.
\]

Then the odd coefficient is not an unrelated returned source:

\[
\boxed{c=J(b).}
\]

Equivalently,

\[
\boxed{9a+1-2e=2^vJ(b)}
\]

and the signed child of the first factor-one state is exactly

\[
\boxed{A(F)=Q_v^{1-e}(J(b)).}
\]

There is a short proof using only Sections 14 and 18.  If \(e=0\), then

\[
P=2a,\qquad A(P)=3a,\qquad b=R(3a).
\]

The integer \(9a\) is odd, so its canonical constant-tail coefficient is

\[
\kappa(9a)=\operatorname{oddpart}(9a+1).
\]

Apply the first identity of Section 18 with the positive odd integer
\(w=3a\):

\[
\kappa(3w)=J(R(w)).
\]

It gives

\[
\operatorname{oddpart}(9a+1)=J(R(3a))=J(b).
\]

If \(e=1\), then

\[
P=2a-1,\qquad A(P)=3a-1,\qquad b=R(3a-1).
\]

Now \(9a-1\) is even, and its canonical coefficient is
\(\operatorname{oddpart}(9a-1)\).  The second identity of Section 18,
again with \(w=3a\), gives

\[
\kappa(9a-1)=J(R(6a-1)).
\]

The shared-child identity of Section 14 is

\[
R(6a-1)=R(3a-1),
\]

so

\[
\operatorname{oddpart}(9a-1)=J(R(3a-1))=J(b).
\]

This proves the box in both phases.  The final formula for \(A(F)\) follows
from the signed exponent-one boundary formula of Section 14.

Now specialize to the globally minimum DRAW source \(s\), put \(a=J(s)\),
and suppose

\[
U=Q_2^e(J(s))\text{ is DRAW}.
\]

Section 15 gives \(\kappa(b)<J(s)\) (apart from the already resolved
terminal small cases).  Writing \(\kappa(b)=3^hJ(t)\), one has
\(J(t)\le\kappa(b)<J(s)\), hence \(t<s\).  Thus \(b\) cannot be DRAW.
As a child of the DRAW state \(U\), it cannot be LOSS either, and therefore

\[
\boxed{b\text{ is WIN}.}
\]

Outcome recursion at \(U\) forces

\[
\boxed{F=Q_1^e(3J(s))\text{ is DRAW}.}
\]

The first factor exit is consequently anchored at an already certified
finite boundary endpoint:

\[
\boxed{
F\text{ DRAW},\qquad b\text{ WIN},\qquad
A(F)=Q_v^{1-e}(J(b)).
}
\]

If \(v\ge2\), Section 81 gives the raw sibling

\[
B(F)=Q_{v-1}^{1-e}(J(b)),
\]

so the two children of \(F\) are an adjacent factor-free frame over this
same finite WIN state \(b\).  If \(v=1\), the signed child is already the
factor-free exponent-one lift over \(b\), while a positive DRAW on the raw
side has the strict source comparison of Section 81.

Thus the first factor-one transition from a factor-free exponent-two
minimum-source DRAW does **not** initialize an arbitrary source \(t\): its
returned source is exactly the previously exposed finite WIN endpoint
\(b\).  The residual attachment problem is correspondingly narrower: one
must normalize the possible long adjacent factor-free frame over this
carried WIN token without resetting its provenance.

The identity is regression-tested independently in
``tests/test_althoefer_repair.py``; the finite test is supporting evidence,
not the proof above.

'''


def main() -> None:
    proof = Path("docs/verified-results.md")
    text = proof.read_text(encoding="utf-8")
    marker = "### The remaining attachment obligation\n"
    if marker not in text:
        raise SystemExit("Section 137 attachment marker not found")
    title = "### The first factor signed exit is anchored at the common boundary endpoint"
    if title not in text:
        proof.write_text(text.replace(marker, LEMMA + marker, 1), encoding="utf-8")

    cert_path = Path("certificates/global-routing.json")
    cert_text = cert_path.read_text(encoding="utf-8")
    digest = hashlib.sha256(proof.read_bytes()).hexdigest()
    cert_text, count = re.subn(
        r'("sha256"\s*:\s*")[0-9a-f]{64}("\s*,)',
        rf'\g<1>{digest}\2',
        cert_text,
        count=1,
    )
    if count != 1:
        raise SystemExit("certificate proof hash field not found")
    cert_path.write_text(cert_text, encoding="utf-8")


if __name__ == "__main__":
    main()
