#!/usr/bin/env python3
"""Finite regression for the audited closure of the two-player 3n+-1 proof.

This script checks exact arithmetic identities used in the repaired human
proof. It is supporting verification only; finite testing is not a proof of
the infinite no-DRAW theorem.

Usage:
    python verify_closure.py
    python verify_closure.py --limit 1000000
"""

from __future__ import annotations

import argparse

EXCEPTIONAL = {1, 3, 12, 14}


def v2(n: int) -> int:
    if n <= 0:
        raise ValueError("v2 expects a positive integer")
    return (n & -n).bit_length() - 1


def A(q: int) -> int:
    if q < 0:
        raise ValueError(q)
    return (3 * q + 1) // 2


def alt_suffix_length(n: int) -> int:
    if n < 0:
        raise ValueError(n)
    if n == 0:
        return 0
    length = 1
    bit = n & 1
    n >>= 1
    while n:
        nxt = n & 1
        if nxt == bit:
            break
        length += 1
        bit = nxt
        n >>= 1
    return length


def R(n: int) -> int:
    return n >> alt_suffix_length(n)


def B(q: int) -> int:
    return R(A(q))


def J(s: int) -> int:
    return 2 * A(s) + 1


def Q(a: int, r: int, e: int) -> int:
    if a <= 0 or a % 2 == 0 or r < 0 or e not in (0, 1):
        raise ValueError((a, r, e))
    return (a << r) - e


def alpha(s: int) -> int:
    if s <= 0:
        raise ValueError(s)
    return 1 - ((s >> 1) & 1)


def inverse_A(y: int) -> int | None:
    if y < 0:
        raise ValueError(y)
    if y % 3 == 0:
        return 2 * y // 3
    if y % 3 == 2:
        return (2 * y - 1) // 3
    return None


def coefficient_source(odd_coefficient: int) -> tuple[int, int]:
    if odd_coefficient <= 0 or odd_coefficient % 2 == 0:
        raise ValueError(odd_coefficient)
    k = 0
    reduced = odd_coefficient
    while reduced % 3 == 0:
        reduced //= 3
        k += 1
    source = inverse_A((reduced - 1) // 2)
    if source is None or J(source) != reduced:
        raise AssertionError((odd_coefficient, reduced, source))
    return source, k


def state_source(q: int) -> tuple[int, int]:
    if q <= 0:
        raise ValueError(q)
    e = q & 1
    shifted = q + e
    r = v2(shifted)
    coeff = shifted >> r
    return coefficient_source(coeff)


def check_source(source: int, e: int) -> None:
    a = J(source)
    p = Q(a, 1, e)
    u = Q(a, 2, e)
    b = B(p)

    # Shared boundary child.
    assert B(u) == b

    # Exact first-factor anchor identity.
    numerator = 9 * a + 1 - 2 * e
    v = v2(numerator)
    assert numerator == (1 << v) * J(b)

    g = 1 - e
    f = Q(3 * a, 1, e)
    signed = A(f)
    assert signed == Q(J(b), v, g)

    if e == alpha(source):
        # A-selecting source boundary has valuation one; factor boundary >=2.
        assert v2(3 * a + 1 - 2 * e) == 1
        assert v >= 2

        if v >= 4:
            assert b < source
            assert b <= (9 * source + 1) // 16

        if v == 3:
            # Constructor congruence needed by the typed hidden-parent lemma.
            assert J(b) % 3 == (1 + g) % 3
    else:
        # B-selecting source boundary has valuation >=2; next factor is exactly 1.
        assert v2(3 * a + 1 - 2 * e) >= 2
        assert v == 1
        assert b == 3 * A(source) + 1

        raw = R(Q(J(b), 1, g))
        assert raw in (A(b), B(b))

        # The only exceptional raw B-child orientation in the closure is a
        # strict source return. This is checked only when raw is positive.
        if b % 16 in EXCEPTIONAL and raw == B(b) and raw > 0:
            raw_source, _ = state_source(raw)
            assert raw_source < source


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=200_000)
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("--limit must be positive")

    counts = {"A-v2": 0, "A-v3": 0, "A-v4+": 0, "B-v1": 0}
    for source in range(1, args.limit + 1):
        for e in (0, 1):
            check_source(source, e)
            a = J(source)
            v = v2(9 * a + 1 - 2 * e)
            if e == alpha(source):
                if v == 2:
                    counts["A-v2"] += 1
                elif v == 3:
                    counts["A-v3"] += 1
                else:
                    counts["A-v4+"] += 1
            else:
                counts["B-v1"] += 1

    print("AUDITED CLOSURE ARITHMETIC REGRESSION PASSED")
    print(f"sources checked: 1..{args.limit}")
    for key, value in counts.items():
        print(f"{key}: {value}")
    print("Scope: finite arithmetic regression only; not an infinite-game proof.")


if __name__ == "__main__":
    main()
