#!/usr/bin/env python3
"""Run sound bounded retrograde analysis and print a compact summary."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.retrograde import bounded_retrograde  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=1000000)
    args = parser.parse_args()

    result = bounded_retrograde(args.limit)
    print(f"limit: {result.limit:,}")
    print(f"counts: {result.counts()}")
    print(f"first unknown: {result.first_unknown()}")
    print(f"resolved prefix end: {result.resolved_prefix_end():,}")
    print(
        "original odd starts covered by that contiguous transformed prefix: "
        f"n <= {2 * result.resolved_prefix_end() + 1:,}"
    )
    print("WARNING: unknown positions are not draws or counterexamples.")


if __name__ == "__main__":
    main()
