#!/usr/bin/env python3
"""Small independent checker for finite WIN/LOSS proof-DAG certificates.

The checker deliberately does not import the project implementation.  It
reimplements only the exact conjugated moves and validates every proof edge.
A valid certificate proves the stated finite root outcome, not the global
absence of DRAW positions.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any


class CertificateError(ValueError):
    """Raised when a certificate fails a local proof obligation."""


def alternating_suffix_remainder(value: int) -> int:
    """Delete the maximal alternating suffix from a nonnegative integer."""
    if value < 0:
        raise ValueError("value must be nonnegative")
    if value == 0:
        return 0
    length = 1
    previous = value & 1
    prefix = value >> 1
    while prefix:
        bit = prefix & 1
        if bit == previous:
            break
        previous = bit
        length += 1
        prefix >>= 1
    return value >> length


def expanding_move(q: int) -> int:
    return (3 * q + 1) // 2


def moves(q: int) -> tuple[int, ...]:
    if q < 0:
        raise ValueError("q must be nonnegative")
    if q == 0:
        return ()
    expanded = expanding_move(q)
    return expanded, alternating_suffix_remainder(expanded)


def _integer(value: Any, label: str, *, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise CertificateError(f"{label} must be an integer >= {minimum}")
    return value


def verify_certificate(payload: Any) -> dict[str, int | str]:
    """Validate a parsed JSON certificate and return a short summary."""
    if not isinstance(payload, dict):
        raise CertificateError("top level must be a JSON object")
    if payload.get("schema_version") != 1:
        raise CertificateError("unsupported schema_version")
    if payload.get("certificate_kind") != "finite-outcome-proof-dag":
        raise CertificateError("unsupported certificate_kind")
    if payload.get("game") != "conjugated-3n-plus-minus-1":
        raise CertificateError("wrong game identifier")

    root = _integer(payload.get("root"), "root")
    limit = _integer(payload.get("limit"), "limit")
    if root > limit:
        raise CertificateError("root exceeds generator limit")
    root_outcome = payload.get("root_outcome")
    if root_outcome not in {"WIN", "LOSS"}:
        raise CertificateError("root_outcome must be WIN or LOSS")

    raw_nodes = payload.get("nodes")
    if not isinstance(raw_nodes, dict) or not raw_nodes:
        raise CertificateError("nodes must be a nonempty JSON object")
    if _integer(payload.get("node_count"), "node_count", minimum=1) != len(raw_nodes):
        raise CertificateError("node_count does not match nodes")

    nodes: dict[int, tuple[str, int, tuple[int, ...]]] = {}
    for key, raw_node in raw_nodes.items():
        if not isinstance(key, str) or not key.isdigit():
            raise CertificateError(f"invalid node key {key!r}")
        q = int(key)
        if str(q) != key:
            raise CertificateError(f"node key {key!r} is not canonical")
        if q > limit:
            raise CertificateError(f"node {q} exceeds generator limit")
        if not isinstance(raw_node, dict):
            raise CertificateError(f"node {q} must be an object")
        outcome = raw_node.get("outcome")
        if outcome not in {"WIN", "LOSS"}:
            raise CertificateError(f"node {q} has invalid outcome")
        rank = _integer(raw_node.get("rank"), f"node {q} rank", minimum=1)
        raw_children = raw_node.get("proof_children")
        if not isinstance(raw_children, list):
            raise CertificateError(f"node {q} proof_children must be a list")
        children = tuple(
            _integer(child, f"node {q} child") for child in raw_children
        )
        nodes[q] = outcome, rank, children

    if root not in nodes:
        raise CertificateError("root node is absent")
    if nodes[root][0] != root_outcome:
        raise CertificateError("root_outcome does not match root node")

    for q, (outcome, rank, children) in nodes.items():
        if q == 0:
            if outcome != "LOSS" or children:
                raise CertificateError("terminal node 0 must be LOSS with no children")
            continue

        actual = moves(q)
        if outcome == "WIN":
            if len(children) != 1 or children[0] not in actual:
                raise CertificateError(
                    f"WIN node {q} must name one actual LOSS child"
                )
            required_outcome = "LOSS"
        else:
            if Counter(children) != Counter(actual):
                raise CertificateError(
                    f"LOSS node {q} must name both actual children"
                )
            required_outcome = "WIN"

        for child in children:
            if child not in nodes:
                raise CertificateError(f"node {q} references absent child {child}")
            child_outcome, child_rank, _ = nodes[child]
            if child_outcome != required_outcome:
                raise CertificateError(
                    f"node {q} requires child {child} to be {required_outcome}"
                )
            if child_rank >= rank:
                raise CertificateError(
                    f"rank does not decrease on edge {q} -> {child}"
                )

    reachable: set[int] = set()
    stack = [root]
    while stack:
        q = stack.pop()
        if q in reachable:
            continue
        reachable.add(q)
        stack.extend(nodes[q][2])
    extras = set(nodes) - reachable
    if extras:
        raise CertificateError(f"unreachable nodes present: {sorted(extras)}")

    return {
        "root": root,
        "outcome": root_outcome,
        "nodes": len(nodes),
        "max_rank": max(rank for _, rank, _ in nodes.values()),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "certificate",
        help="JSON certificate path, or - to read the certificate from stdin",
    )
    args = parser.parse_args()
    try:
        if args.certificate == "-":
            source = sys.stdin.read()
        else:
            source = Path(args.certificate).read_text(encoding="utf-8")
        payload = json.loads(source)
        summary = verify_certificate(payload)
    except (OSError, json.JSONDecodeError, CertificateError) as exc:
        raise SystemExit(f"INVALID: {exc}") from exc
    print(
        "VALID finite outcome certificate: "
        f"q={summary['root']} is {summary['outcome']}; "
        f"{summary['nodes']} nodes; max rank {summary['max_rank']}"
    )


if __name__ == "__main__":
    main()
