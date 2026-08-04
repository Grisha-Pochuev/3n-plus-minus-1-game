#!/usr/bin/env python3
"""Look for a genuine finite DRAW trap in a bounded retrograde graph.

A nonempty result is stronger than an ordinary UNKNOWN report: every node in
the returned finite set has a move inside the set, and every other move is
already proved WIN. An empty result remains only finite computational evidence.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.retrograde import (  # noqa: E402
    bounded_retrograde,
    certified_finite_draw_kernel,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=1_000_000)
    args = parser.parse_args()

    result = bounded_retrograde(args.limit)
    kernel = certified_finite_draw_kernel(result)
    print(f"cutoff: {args.limit:,}")
    print(f"outcomes: {result.counts()}")
    print(f"first unknown: {result.first_unknown()}")
    print(f"certified finite DRAW kernel size: {len(kernel):,}")
    if kernel:
        print("first kernel nodes:", list(kernel[:100]))
        raise SystemExit(2)
    print("No isolated finite DRAW kernel was found at this cutoff.")
    print("This does not exclude a boundary-connected or unbounded DRAW kernel.")


if __name__ == "__main__":
    main()
