#!/usr/bin/env python3
"""Extract a finite proof DAG for one bounded-retrograde position."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.retrograde import Outcome, bounded_retrograde  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--limit", type=int, default=1000000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    if not 0 <= args.q <= args.limit:
        raise SystemExit("q must lie in 0..limit")

    result = bounded_retrograde(args.limit)
    root_outcome = result.outcome(args.q)
    if root_outcome == Outcome.UNKNOWN:
        raise SystemExit(f"q={args.q} is UNKNOWN at limit={args.limit}")

    nodes: dict[int, dict[str, object]] = {}
    stack = [args.q]
    while stack:
        q = stack.pop()
        if q in nodes:
            continue
        children = result.proof_children(q)
        nodes[q] = {
            "outcome": result.outcome(q).name,
            "rank": int(result.resolved_at[q]),
            "proof_children": list(children),
        }
        stack.extend(children)

    payload = {
        "schema_version": 1,
        "certificate_kind": "finite-outcome-proof-dag",
        "game": "conjugated-3n-plus-minus-1",
        "claim_scope": "one finite WIN/LOSS proof; not the global theorem",
        "limit": args.limit,
        "root": args.q,
        "root_outcome": root_outcome.name,
        "node_count": len(nodes),
        "nodes": {str(q): nodes[q] for q in sorted(nodes)},
    }
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
        print(f"wrote {args.output} ({len(nodes)} proof nodes)")
    else:
        print(text)


if __name__ == "__main__":
    main()
