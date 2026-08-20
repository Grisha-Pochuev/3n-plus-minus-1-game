#!/usr/bin/env python3
"""Independent finite-certificate checker for the 3n±1 game.

This checks concrete WIN/LOSS proof trees and finite coinductive DRAW traps.
It deliberately does NOT treat bounded search as a universal proof.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Dict, Mapping, MutableSet, Sequence, Tuple


def odd_part(x: int) -> int:
    if x <= 0:
        raise ValueError("odd_part expects a positive integer")
    while x % 2 == 0:
        x //= 2
    return x


def children(n: int) -> Tuple[int, int]:
    if n <= 1 or n % 2 == 0:
        raise ValueError("a nonterminal position must be an odd integer > 1")
    return odd_part(3 * n - 1), odd_part(3 * n + 1)


def short_long(n: int) -> Tuple[int, int]:
    a, b = children(n)
    short, long = (a, b) if a < n else (b, a)
    if not (short < n < long):
        raise AssertionError(f"short/long invariant failed at n={n}: {a}, {b}")
    return short, long


class CertificateError(ValueError):
    pass


def _as_int(value: Any, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise CertificateError(f"{field} must be an integer")
    return value


def verify_finite_certificate(cert: Mapping[str, Any], active: MutableSet[int] | None = None) -> str:
    """Return 'W' or 'L' after recursively checking a finite proof tree."""
    if active is None:
        active = set()
    if not isinstance(cert, Mapping):
        raise CertificateError("certificate node must be an object")
    identity = id(cert)
    if identity in active:
        raise CertificateError("finite certificate contains an object cycle")
    active.add(identity)
    try:
        kind = cert.get("kind")
        n = _as_int(cert.get("n"), "n")
        if n <= 0 or n % 2 == 0:
            raise CertificateError(f"n must be a positive odd integer, got {n}")

        if kind == "L":
            if n == 1:
                allowed = {"kind", "n"}
                extra = set(cert) - allowed
                if extra:
                    raise CertificateError(f"terminal LOSS has unexpected fields: {sorted(extra)}")
                return "L"
            expected = set(children(n))
            raw_children = cert.get("children")
            if not isinstance(raw_children, Sequence) or isinstance(raw_children, (str, bytes)):
                raise CertificateError("nonterminal LOSS requires a two-element children list")
            if len(raw_children) != 2:
                raise CertificateError("nonterminal LOSS must certify exactly both legal children")
            seen = set()
            for child_cert in raw_children:
                if not isinstance(child_cert, Mapping):
                    raise CertificateError("child certificate must be an object")
                child_n = _as_int(child_cert.get("n"), "child.n")
                seen.add(child_n)
                if verify_finite_certificate(child_cert, active) != "W":
                    raise CertificateError(f"LOSS({n}) requires WIN certificates for both children")
            if seen != expected:
                raise CertificateError(
                    f"LOSS({n}) children mismatch: expected {sorted(expected)}, got {sorted(seen)}"
                )
            return "L"

        if kind == "W":
            if n == 1:
                raise CertificateError("terminal position 1 cannot have a WIN certificate")
            child_cert = cert.get("child")
            if not isinstance(child_cert, Mapping):
                raise CertificateError("WIN requires one child certificate")
            child_n = _as_int(child_cert.get("n"), "child.n")
            if child_n not in set(children(n)):
                raise CertificateError(f"{child_n} is not a legal child of {n}")
            if verify_finite_certificate(child_cert, active) != "L":
                raise CertificateError(f"WIN({n}) requires a LOSS child")
            return "W"

        raise CertificateError(f"unknown certificate kind {kind!r}")
    finally:
        active.remove(identity)


def verify_draw_trap(data: Mapping[str, Any]) -> None:
    """Verify a finite coinductive DRAW trap.

    Format:
      {
        "draw_nodes": [5, 7, ...],
        "exit_win_certificates": {"13": {...}, ...}
      }

    For every draw node, at least one legal child must remain in the trap.
    Every legal child outside the trap must have a valid WIN certificate.
    Therefore no trap node has a LOSS exit, and play can stay in the trap forever.
    """
    raw_nodes = data.get("draw_nodes")
    if not isinstance(raw_nodes, Sequence) or isinstance(raw_nodes, (str, bytes)):
        raise CertificateError("draw_nodes must be a nonempty list")
    nodes = {_as_int(x, "draw_node") for x in raw_nodes}
    if not nodes:
        raise CertificateError("draw trap is empty")
    for n in nodes:
        if n <= 1 or n % 2 == 0:
            raise CertificateError(f"invalid draw node {n}")

    raw_exits = data.get("exit_win_certificates", {})
    if not isinstance(raw_exits, Mapping):
        raise CertificateError("exit_win_certificates must be an object")

    checked_exits: Dict[int, str] = {}
    for key, cert in raw_exits.items():
        try:
            n = int(key)
        except (TypeError, ValueError) as exc:
            raise CertificateError(f"invalid exit key {key!r}") from exc
        if not isinstance(cert, Mapping) or cert.get("n") != n:
            raise CertificateError(f"exit certificate key/node mismatch at {key!r}")
        outcome = verify_finite_certificate(cert)
        if outcome != "W":
            raise CertificateError(f"exit {n} must be certified WIN, got {outcome}")
        checked_exits[n] = outcome

    required_exits = set()
    for n in nodes:
        succ = set(children(n))
        if not (succ & nodes):
            raise CertificateError(f"draw node {n} has no successor inside the trap")
        required_exits.update(succ - nodes)
    missing = required_exits - set(checked_exits)
    if missing:
        raise CertificateError(f"missing WIN certificates for exits: {sorted(missing)}")
    unused = set(checked_exits) - required_exits
    if unused:
        raise CertificateError(f"unused exit certificates: {sorted(unused)}")


def verify_arithmetic_identity(n: int) -> None:
    if n <= 1 or n % 2 == 0:
        raise ValueError("n must be odd and > 1")
    epsilon = 1 if n % 4 == 1 else -1
    raw_short = 3 * n + epsilon
    v = 0
    t = raw_short
    while t % 2 == 0:
        t //= 2
        v += 1
    b = t
    p = (3 * n - epsilon) // 2
    if v < 2 or b != short_long(n)[0] or p != short_long(n)[1]:
        raise AssertionError("short/long decomposition failed")
    if p != (2 ** (v - 1)) * b - epsilon:
        raise AssertionError("sibling identity failed")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("file", nargs="?", type=Path, help="JSON finite certificate or draw trap")
    parser.add_argument("--draw-trap", action="store_true", help="interpret JSON as a draw trap")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        # LOSS(1), WIN(5) via 1, and the arithmetic identities on a deterministic range.
        loss1 = {"kind": "L", "n": 1}
        win5 = {"kind": "W", "n": 5, "child": loss1}
        assert verify_finite_certificate(loss1) == "L"
        assert verify_finite_certificate(win5) == "W"
        for n in range(3, 10001, 2):
            verify_arithmetic_identity(n)
        # The cycle 5<->7 must be rejected as a DRAW trap because 5 has LOSS exit 1.
        bad_trap = {
            "draw_nodes": [5, 7],
            "exit_win_certificates": {
                "11": {"kind": "W", "n": 11, "child": {"kind": "L", "n": 1}}
            },
        }
        try:
            verify_draw_trap(bad_trap)
        except CertificateError:
            pass
        else:
            raise AssertionError("invalid 5<->7 draw trap was accepted")
        print("self-test: OK")
        return 0

    if args.file is None:
        parser.error("provide a JSON file or --self-test")
    data = json.loads(args.file.read_text(encoding="utf-8"))
    if args.draw_trap:
        verify_draw_trap(data)
        print("valid finite coinductive DRAW trap")
    else:
        result = verify_finite_certificate(data)
        print(f"valid finite {result} certificate for n={data['n']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
