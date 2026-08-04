#!/usr/bin/env python3
"""Explore outcome regularity by low binary suffixes."""

from __future__ import annotations

import argparse
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.retrograde import bounded_retrograde  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=1000000)
    parser.add_argument("--suffix-bits", type=int, default=12)
    args = parser.parse_args()
    if not 1 <= args.suffix_bits <= 24:
        raise SystemExit("--suffix-bits must be between 1 and 24")

    result = bounded_retrograde(args.limit)
    modulus = 1 << args.suffix_bits
    counts: dict[int, list[int]] = defaultdict(lambda: [0, 0, 0])

    for q, raw in enumerate(result.outcomes):
        counts[q % modulus][raw] += 1

    pure = []
    mixed = []
    for residue, triple in counts.items():
        unknown, loss, win = triple
        known_types = int(loss > 0) + int(win > 0)
        row = (residue, loss, win, unknown)
        if known_types <= 1:
            pure.append(row)
        else:
            mixed.append(row)

    print(f"limit={args.limit:,}, modulus=2^{args.suffix_bits}={modulus:,}")
    print(f"resolved prefix end={result.resolved_prefix_end():,}")
    print(f"suffix classes with only one known outcome: {len(pure):,}")
    print(f"suffix classes containing both known outcomes: {len(mixed):,}")
    print("first mixed classes (residue, LOSS, WIN, UNKNOWN):")
    for row in mixed[:20]:
        print(row)
    print("Interpretation: purity in a finite window is evidence only, not a residue theorem.")


if __name__ == "__main__":
    main()
