#!/usr/bin/env python3
"""Verify the symbolic global-routing assembly certificate.

The checker is intentionally independent of the exploratory game library.  It
checks the finite proof assembly: source integrity, total guard partitions,
one rule per declared case, lexicographic size change, and acyclicity of the
remaining equal-rank control graph.

It does *not* prove that the declared macro rules refine every legal game
continuation.  That refinement is the explicitly listed human trust boundary
of the certificate and of certificates/global-routing-certificate.md.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SUPPORTED_ORDERS = {"nat", "finite-multiset-extension(nat)"}
EFFECTS = {"preserve", "decrease", "reset"}
REQUIRED_MACHINE_CHECKS = {
    "source-integrity",
    "declared-guard-coverage",
    "one-rule-per-case",
    "lexicographic-size-change",
    "equal-rank-control-acyclicity",
    "proof-section-presence",
}
REQUIRED_TRUSTED_OBLIGATIONS = {
    "local-arithmetic-and-coordinate-identities",
    "declared-guards-refine-all-game-cases",
    "outcome-compatible-draw-continuation",
    "finite-macrostep-productivity",
}


class CertificateError(ValueError):
    """Raised when the certificate fails a checker obligation."""


def fail(message: str) -> None:
    raise CertificateError(message)


def require_dict(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{where} must be an object")
    return value


def require_list(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        fail(f"{where} must be an array")
    return value


def require_string(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{where} must be a nonempty string")
    return value


def unique_strings(values: Any, where: str) -> list[str]:
    result = [require_string(value, f"{where}[]") for value in require_list(values, where)]
    if len(result) != len(set(result)):
        fail(f"{where} contains duplicates")
    return result


def exact_keys(record: dict[str, Any], expected: set[str], where: str) -> None:
    missing = expected - record.keys()
    extra = record.keys() - expected
    if missing or extra:
        details = []
        if missing:
            details.append("missing " + ", ".join(sorted(missing)))
        if extra:
            details.append("unexpected " + ", ".join(sorted(extra)))
        fail(f"{where}: " + "; ".join(details))


def expand_section_ranges(specs: Any) -> set[int]:
    result: set[int] = set()
    for index, raw in enumerate(require_list(specs, "proof_section_ranges")):
        text = require_string(raw, f"proof_section_ranges[{index}]")
        match = re.fullmatch(r"([1-9][0-9]*)(?:-([1-9][0-9]*))?", text)
        if match is None:
            fail(f"invalid section range: {text!r}")
        start = int(match.group(1))
        stop = int(match.group(2) or start)
        if stop < start:
            fail(f"descending section range: {text!r}")
        result.update(range(start, stop + 1))
    return result


def canonical_text(path: Path) -> str:
    """Return platform-independent UTF-8 text with LF line endings."""
    return path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")


def canonical_sha256(path: Path) -> str:
    return hashlib.sha256(canonical_text(path).encode("utf-8")).hexdigest()


def verify_source(payload: dict[str, Any]) -> tuple[Path, set[int]]:
    source = require_dict(payload.get("proof_source"), "proof_source")
    exact_keys(source, {"path", "sha256", "proof_section_ranges"}, "proof_source")
    relative = require_string(source["path"], "proof_source.path")
    path = (ROOT / relative).resolve()
    try:
        path.relative_to(ROOT)
    except ValueError:
        fail("proof source must stay inside the repository")
    if not path.is_file():
        fail(f"proof source does not exist: {relative}")
    digest = canonical_sha256(path)
    expected_digest = require_string(source["sha256"], "proof_source.sha256").lower()
    if not re.fullmatch(r"[0-9a-f]{64}", expected_digest):
        fail("proof_source.sha256 must contain 64 hexadecimal digits")
    if digest != expected_digest:
        fail(
            f"proof source hash mismatch: expected {expected_digest}, got {digest}; "
            "review the mathematical change before updating the certificate"
        )

    headings = {
        int(match.group(1))
        for match in re.finditer(r"^## ([1-9][0-9]*)\.", canonical_text(path), re.M)
    }
    required = expand_section_ranges(source["proof_section_ranges"])
    missing = sorted(required - headings)
    if missing:
        fail("proof source is missing required sections: " + ", ".join(map(str, missing)))
    return path, required


def verify_rank_components(payload: dict[str, Any]) -> list[str]:
    components = require_list(payload.get("rank_components"), "rank_components")
    if not components:
        fail("rank_components must not be empty")
    ids: list[str] = []
    for index, raw in enumerate(components):
        item = require_dict(raw, f"rank_components[{index}]")
        exact_keys(item, {"id", "order", "meaning"}, f"rank_components[{index}]")
        component_id = require_string(item["id"], f"rank_components[{index}].id")
        order = require_string(item["order"], f"rank_components[{index}].order")
        require_string(item["meaning"], f"rank_components[{index}].meaning")
        if order not in SUPPORTED_ORDERS:
            fail(f"unsupported well-founded order {order!r}")
        ids.append(component_id)
    if len(ids) != len(set(ids)):
        fail("rank component identifiers must be unique")
    return ids


def verify_partition(partition_id: str, raw: Any) -> list[str]:
    item = require_dict(raw, f"guard_partitions.{partition_id}")
    kind = require_string(item.get("kind"), f"guard_partitions.{partition_id}.kind")
    if kind == "enum":
        exact_keys(item, {"kind", "meaning", "cases"}, f"guard_partitions.{partition_id}")
        require_string(item["meaning"], f"guard_partitions.{partition_id}.meaning")
        cases = unique_strings(item["cases"], f"guard_partitions.{partition_id}.cases")
        if not cases:
            fail(f"enum partition {partition_id!r} has no cases")
        return cases

    if kind != "integer_intervals":
        fail(f"unknown partition kind {kind!r} in {partition_id!r}")
    exact_keys(
        item,
        {"kind", "meaning", "domain_min", "domain_max", "cases"},
        f"guard_partitions.{partition_id}",
    )
    require_string(item["meaning"], f"guard_partitions.{partition_id}.meaning")
    domain_min = item["domain_min"]
    domain_max = item["domain_max"]
    if not isinstance(domain_min, int) or isinstance(domain_min, bool):
        fail(f"{partition_id}.domain_min must be an integer")
    if domain_max is not None and (not isinstance(domain_max, int) or isinstance(domain_max, bool)):
        fail(f"{partition_id}.domain_max must be an integer or null")
    if domain_max is not None and domain_max < domain_min:
        fail(f"{partition_id} has an empty integer domain")

    cases_raw = require_list(item["cases"], f"guard_partitions.{partition_id}.cases")
    if not cases_raw:
        fail(f"interval partition {partition_id!r} has no cases")
    next_min = domain_min
    case_ids: list[str] = []
    for index, raw_case in enumerate(cases_raw):
        case = require_dict(raw_case, f"{partition_id}.cases[{index}]")
        exact_keys(case, {"id", "min", "max"}, f"{partition_id}.cases[{index}]")
        case_id = require_string(case["id"], f"{partition_id}.cases[{index}].id")
        lower, upper = case["min"], case["max"]
        if not isinstance(lower, int) or isinstance(lower, bool):
            fail(f"{partition_id}.{case_id}.min must be an integer")
        if upper is not None and (not isinstance(upper, int) or isinstance(upper, bool)):
            fail(f"{partition_id}.{case_id}.max must be an integer or null")
        if lower != next_min:
            fail(
                f"{partition_id} is not a disjoint cover: expected next interval "
                f"to start at {next_min}, got {lower}"
            )
        if upper is not None and upper < lower:
            fail(f"{partition_id}.{case_id} is an empty interval")
        if upper is None:
            if index != len(cases_raw) - 1 or domain_max is not None:
                fail(f"unbounded interval in {partition_id} must be the final case of an unbounded domain")
        else:
            next_min = upper + 1
        case_ids.append(case_id)

    if len(case_ids) != len(set(case_ids)):
        fail(f"partition {partition_id!r} contains duplicate case identifiers")
    final_upper = cases_raw[-1]["max"]
    if domain_max is None:
        if final_upper is not None:
            fail(f"partition {partition_id!r} does not cover its unbounded tail")
    elif final_upper != domain_max:
        fail(f"partition {partition_id!r} ends at {final_upper}, expected {domain_max}")
    return case_ids


def find_cycle(nodes: set[str], edges: dict[str, list[str]]) -> list[str] | None:
    color = {node: 0 for node in nodes}
    stack: list[str] = []
    positions: dict[str, int] = {}

    def visit(node: str) -> list[str] | None:
        color[node] = 1
        positions[node] = len(stack)
        stack.append(node)
        for target in edges.get(node, []):
            if color[target] == 0:
                cycle = visit(target)
                if cycle is not None:
                    return cycle
            elif color[target] == 1:
                return stack[positions[target] :] + [target]
        stack.pop()
        positions.pop(node)
        color[node] = 2
        return None

    for node in sorted(nodes):
        if color[node] == 0:
            cycle = visit(node)
            if cycle is not None:
                return cycle
    return None


def verify_certificate(payload: dict[str, Any]) -> dict[str, Any]:
    exact_keys(
        payload,
        {
            "schema_version",
            "certificate_kind",
            "status",
            "game",
            "global_claim",
            "claim_scope",
            "proof_source",
            "machine_checked_obligations",
            "trusted_obligations",
            "rank_components",
            "guard_partitions",
            "control_states",
            "transitions",
        },
        "certificate",
    )
    if payload["schema_version"] != 1:
        fail("unsupported schema_version (expected 1)")
    if payload["certificate_kind"] != "global-routing-assembly-certificate":
        fail("unexpected certificate_kind")
    if payload["status"] != "CONDITIONAL_MACHINE_CHECK":
        fail("status must be CONDITIONAL_MACHINE_CHECK")
    if payload["game"] != "conjugated-3n-plus-minus-1":
        fail("unexpected game identifier")
    require_string(payload["global_claim"], "global_claim")
    require_string(payload["claim_scope"], "claim_scope")

    proof_path, required_sections = verify_source(payload)
    rank_ids = verify_rank_components(payload)

    machine_checks = set(unique_strings(payload["machine_checked_obligations"], "machine_checked_obligations"))
    if machine_checks != REQUIRED_MACHINE_CHECKS:
        fail(
            "machine_checked_obligations must be exactly: "
            + ", ".join(sorted(REQUIRED_MACHINE_CHECKS))
        )

    trusted_raw = require_list(payload["trusted_obligations"], "trusted_obligations")
    trusted_ids: set[str] = set()
    for index, raw in enumerate(trusted_raw):
        item = require_dict(raw, f"trusted_obligations[{index}]")
        exact_keys(item, {"id", "status", "proof_sections", "description"}, f"trusted_obligations[{index}]")
        obligation_id = require_string(item["id"], f"trusted_obligations[{index}].id")
        if item["status"] != "HUMAN_PROOF":
            fail(f"trusted obligation {obligation_id!r} must have status HUMAN_PROOF")
        refs = item["proof_sections"]
        if not isinstance(refs, list) or not refs or any(not isinstance(value, int) for value in refs):
            fail(f"trusted obligation {obligation_id!r} needs integer proof_sections")
        if not set(refs) <= required_sections:
            fail(f"trusted obligation {obligation_id!r} references a section outside proof_source ranges")
        require_string(item["description"], f"trusted_obligations[{index}].description")
        trusted_ids.add(obligation_id)
    if trusted_ids != REQUIRED_TRUSTED_OBLIGATIONS:
        fail(
            "trusted_obligations must be exactly: "
            + ", ".join(sorted(REQUIRED_TRUSTED_OBLIGATIONS))
        )

    partitions_raw = require_dict(payload["guard_partitions"], "guard_partitions")
    if not partitions_raw:
        fail("guard_partitions must not be empty")
    partition_cases = {
        partition_id: verify_partition(partition_id, raw)
        for partition_id, raw in partitions_raw.items()
    }

    states_raw = require_list(payload["control_states"], "control_states")
    state_partitions: dict[str, str] = {}
    for index, raw in enumerate(states_raw):
        state = require_dict(raw, f"control_states[{index}]")
        exact_keys(state, {"id", "guard_partition", "meaning"}, f"control_states[{index}]")
        state_id = require_string(state["id"], f"control_states[{index}].id")
        partition_id = require_string(state["guard_partition"], f"control_states[{index}].guard_partition")
        require_string(state["meaning"], f"control_states[{index}].meaning")
        if partition_id not in partition_cases:
            fail(f"state {state_id!r} uses unknown guard partition {partition_id!r}")
        if state_id in state_partitions:
            fail(f"duplicate control state {state_id!r}")
        state_partitions[state_id] = partition_id
    if not state_partitions:
        fail("control_states must not be empty")

    transitions_raw = require_list(payload["transitions"], "transitions")
    transition_ids: set[str] = set()
    covered: dict[str, set[str]] = defaultdict(set)
    equal_edges: dict[str, list[str]] = defaultdict(list)
    strict_count = 0
    equal_count = 0
    referenced_sections: set[int] = set()
    for index, raw in enumerate(transitions_raw):
        rule = require_dict(raw, f"transitions[{index}]")
        exact_keys(
            rule,
            {"id", "from", "guard_case", "to", "rank_effect", "proof_sections", "meaning"},
            f"transitions[{index}]",
        )
        rule_id = require_string(rule["id"], f"transitions[{index}].id")
        source = require_string(rule["from"], f"transitions[{index}].from")
        target = require_string(rule["to"], f"transitions[{index}].to")
        guard_case = require_string(rule["guard_case"], f"transitions[{index}].guard_case")
        require_string(rule["meaning"], f"transitions[{index}].meaning")
        if rule_id in transition_ids:
            fail(f"duplicate transition identifier {rule_id!r}")
        transition_ids.add(rule_id)
        if source not in state_partitions or target not in state_partitions:
            fail(f"transition {rule_id!r} references an unknown control state")
        allowed_cases = partition_cases[state_partitions[source]]
        if guard_case not in allowed_cases:
            fail(f"transition {rule_id!r} uses unknown case {guard_case!r} for state {source!r}")
        if guard_case in covered[source]:
            fail(f"state {source!r} has more than one rule for case {guard_case!r}")
        covered[source].add(guard_case)

        refs = rule["proof_sections"]
        if not isinstance(refs, list) or not refs or any(not isinstance(value, int) for value in refs):
            fail(f"transition {rule_id!r} needs nonempty integer proof_sections")
        if not set(refs) <= required_sections:
            fail(f"transition {rule_id!r} references a section outside proof_source ranges")
        referenced_sections.update(refs)

        effects = require_list(rule["rank_effect"], f"transition {rule_id!r}.rank_effect")
        if len(effects) != len(rank_ids):
            fail(
                f"transition {rule_id!r} has {len(effects)} effects for "
                f"{len(rank_ids)} rank components"
            )
        if any(effect not in EFFECTS for effect in effects):
            fail(f"transition {rule_id!r} has an unknown rank effect")
        first_change = next((position for position, effect in enumerate(effects) if effect != "preserve"), None)
        if first_change is None:
            equal_count += 1
            equal_edges[source].append(target)
        else:
            if effects[first_change] != "decrease":
                fail(
                    f"transition {rule_id!r} resets {rank_ids[first_change]!r} "
                    "before any earlier strict decrease"
                )
            strict_count += 1

    for state, partition_id in state_partitions.items():
        expected = set(partition_cases[partition_id])
        actual = covered[state]
        if actual != expected:
            missing = sorted(expected - actual)
            extra = sorted(actual - expected)
            fail(f"state {state!r} guard coverage mismatch; missing={missing}, extra={extra}")

    cycle = find_cycle(set(state_partitions), equal_edges)
    if cycle is not None:
        fail("equal-rank control cycle: " + " -> ".join(cycle))

    decisive_sections = {129, 132, 136, 137, 138}
    if not decisive_sections <= referenced_sections:
        fail(
            "transition inventory does not reference all decisive assembly sections: "
            + ", ".join(map(str, sorted(decisive_sections - referenced_sections)))
        )

    return {
        "status": payload["status"],
        "proof_source": str(proof_path.relative_to(ROOT)),
        "proof_source_sha256": canonical_sha256(proof_path),
        "rank_components": len(rank_ids),
        "guard_partitions": len(partition_cases),
        "control_states": len(state_partitions),
        "transitions": len(transitions_raw),
        "strict_transitions": strict_count,
        "equal_rank_transitions": equal_count,
        "trusted_obligations": len(trusted_ids),
    }


def load_payload(path: str) -> dict[str, Any]:
    try:
        if path == "-":
            value = json.load(sys.stdin)
        else:
            value = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read certificate: {exc}")
    return require_dict(value, "certificate")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Verify the symbolic global-routing proof assembly."
    )
    parser.add_argument(
        "certificate",
        nargs="?",
        default="certificates/global-routing.json",
        help="certificate path, or - for stdin",
    )
    args = parser.parse_args()
    try:
        summary = verify_certificate(load_payload(args.certificate))
    except CertificateError as exc:
        print(f"GLOBAL CERTIFICATE REJECTED: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc

    print("GLOBAL ROUTING ASSEMBLY CERTIFICATE ACCEPTED")
    print(f"status: {summary['status']}")
    print(
        "scope: machine-checked assembly conditional on the four declared "
        "human proof obligations"
    )
    print(
        f"inventory: {summary['control_states']} states, "
        f"{summary['transitions']} transitions, "
        f"{summary['guard_partitions']} total guard partitions"
    )
    print(
        f"rank check: {summary['strict_transitions']} strict transitions; "
        f"{summary['equal_rank_transitions']} equal-rank transitions form a DAG"
    )
    print(
        f"proof source: {summary['proof_source']} "
        f"sha256={summary['proof_source_sha256']}"
    )
    print(
        f"NOT kernel-checked here: {summary['trusted_obligations']} local "
        "refinement/outcome obligations; see certificates/global-routing-certificate.md"
    )


if __name__ == "__main__":
    main()
