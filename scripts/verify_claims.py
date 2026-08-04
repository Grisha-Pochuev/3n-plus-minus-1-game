#!/usr/bin/env python3
"""Verify exact identities and descent lemmas over a finite range."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.game import (  # noqa: E402
    decreasing_move,
    increasing_move,
    m_coordinates_children,
    normal_form_children,
    transformed_B,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=100000)
    args = parser.parse_args()
    if args.limit < 1:
        raise SystemExit("--limit must be positive")

    for m in range(1, args.limit + 1):
        actual = sorted(m_coordinates_children(m))
        normal = sorted(normal_form_children(m))
        if actual != normal:
            raise AssertionError(("normal form", m, actual, normal))

        if not transformed_B(m) < m:
            raise AssertionError(("B descent", m, transformed_B(m)))

    original_limit = 2 * args.limit + 1
    checked_descent = 0
    terminal_decreases = 0
    for n in range(3, original_limit + 1, 2):
        d = decreasing_move(n)
        if d == 1:
            terminal_decreases += 1
            continue
        if not decreasing_move(d) < n:
            raise AssertionError(("D(D(n))", n, d, decreasing_move(d)))
        if not decreasing_move(increasing_move(d)) < n:
            raise AssertionError(
                ("D(U(D(n)))", n, d, increasing_move(d), decreasing_move(increasing_move(d)))
            )
        checked_descent += 1

    print(f"verified m-space normal form for 1 <= m <= {args.limit:,}")
    print(f"verified B(q) < q for 1 <= q <= {args.limit:,}")
    print(f"verified descent blocks for odd 3 <= n <= {original_limit:,}")
    print(f"nonterminal descent cases: {checked_descent:,}")
    print(f"D(n)=1 cases: {terminal_decreases:,}")


if __name__ == "__main__":
    main()
