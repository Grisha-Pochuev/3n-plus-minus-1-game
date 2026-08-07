#!/usr/bin/env python3
"""One-command local audit for an independent reader.

This command checks repository integrity requirements, runs the complete unit
suite, verifies exact arithmetic over a stated finite range, generates one
finite outcome proof DAG, and validates it with the independent checker.

It does not claim to machine-check the global no-DRAW proof; that proof still
requires the human audit described in AUDIT.md.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parent
REQUIRED_FILES = (
    "AUDIT.md",
    "START_HERE.md",
    "certificates/README.md",
    "docs/problem.md",
    "docs/normal-form.md",
    "docs/global-proof.md",
    "docs/proof-map.md",
    "docs/proof-ledger.md",
    "docs/verified-results.md",
    "docs/pitfalls.md",
    "scripts/verify_claims.py",
    "scripts/extract_proof.py",
    "scripts/verify_outcome_certificate.py",
    "scripts/README.md",
    "formal/COVERAGE.md",
    "paper/README.md",
)


def run_stage(label: str, command: list[str]) -> float:
    print(f"\n=== {label} ===", flush=True)
    print("$ " + " ".join(command), flush=True)
    started = time.monotonic()
    completed = subprocess.run(command, cwd=ROOT, check=False)
    elapsed = time.monotonic() - started
    if completed.returncode != 0:
        raise SystemExit(
            f"\nAUDIT FAILED in {label!r} "
            f"(exit code {completed.returncode})"
        )
    print(f"--- passed in {elapsed:.2f}s", flush=True)
    return elapsed


def capture_stage(label: str, command: list[str]) -> tuple[str, float]:
    """Run a generator and return its stdout without creating a shared file."""
    print(f"\n=== {label} ===", flush=True)
    print("$ " + " ".join(command), flush=True)
    started = time.monotonic()
    completed = subprocess.run(
        command, cwd=ROOT, check=False, text=True, capture_output=True
    )
    elapsed = time.monotonic() - started
    if completed.returncode != 0:
        if completed.stdout:
            print(completed.stdout, end="")
        if completed.stderr:
            print(completed.stderr, end="", file=sys.stderr)
        raise SystemExit(
            f"\nAUDIT FAILED in {label!r} "
            f"(exit code {completed.returncode})"
        )
    print(f"--- passed in {elapsed:.2f}s", flush=True)
    return completed.stdout, elapsed


def verify_from_stdin(label: str, command: list[str], certificate: str) -> float:
    print(f"\n=== {label} ===", flush=True)
    print("$ " + " ".join(command) + " < generated-certificate.json", flush=True)
    started = time.monotonic()
    completed = subprocess.run(
        command, cwd=ROOT, check=False, text=True, input=certificate
    )
    elapsed = time.monotonic() - started
    if completed.returncode != 0:
        raise SystemExit(
            f"\nAUDIT FAILED in {label!r} "
            f"(exit code {completed.returncode})"
        )
    print(f"--- passed in {elapsed:.2f}s", flush=True)
    return elapsed


def check_layout() -> None:
    missing = [path for path in REQUIRED_FILES if not (ROOT / path).is_file()]
    if missing:
        raise SystemExit("AUDIT FAILED: missing required files: " + ", ".join(missing))
    print("required proof, audit, code, and coverage files are present")


def documentation_files() -> list[Path]:
    files = list(ROOT.glob("*.md"))
    for dirname in (
        "certificates",
        "docs",
        "formal",
        "paper",
        "scripts",
        "src",
        "tests",
    ):
        files.extend((ROOT / dirname).glob("*.md"))
    return sorted(set(files))


def check_documentation_links() -> None:
    pattern = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
    broken: list[str] = []
    checked = 0
    for document in documentation_files():
        lines = document.read_text(encoding="utf-8").splitlines()
        for raw_target in (
            target for line in lines for target in pattern.findall(line)
        ):
            target = raw_target.strip()
            if target.startswith("<") and target.endswith(">"):
                target = target[1:-1]
            if (
                not target
                or target.startswith("#")
                or "://" in target
                or target.startswith("mailto:")
            ):
                continue
            target = unquote(target.split("#", 1)[0])
            resolved = (document.parent / target).resolve()
            checked += 1
            if not resolved.exists():
                broken.append(f"{document.relative_to(ROOT)} -> {raw_target}")
    if broken:
        raise SystemExit("AUDIT FAILED: broken local links:\n" + "\n".join(broken))
    print(f"checked {checked} local Markdown links")


def check_lean_placeholders() -> None:
    forbidden = re.compile(r"\b(?:axiom|admit|sorry)\b")
    failures: list[str] = []
    lean_sources = list((ROOT / "formal").glob("*.lean"))
    lean_sources.extend((ROOT / "formal" / "ThreeNPlusMinusOne").rglob("*.lean"))
    for source in lean_sources:
        for line_number, line in enumerate(
            source.read_text(encoding="utf-8").splitlines(), start=1
        ):
            if forbidden.search(line):
                failures.append(
                    f"{source.relative_to(ROOT)}:{line_number}: {line.strip()}"
                )
    if failures:
        raise SystemExit(
            "AUDIT FAILED: forbidden Lean placeholders:\n" + "\n".join(failures)
        )
    print("Lean sources contain no axiom/admit/sorry placeholders")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run the reproducible local audit; see AUDIT.md for scope."
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=100_000,
        help="finite arithmetic verification limit (default: 100000)",
    )
    parser.add_argument(
        "--certificate-root",
        type=int,
        default=100,
        help="conjugated position for the sample proof certificate",
    )
    parser.add_argument(
        "--certificate-limit",
        type=int,
        default=200_000,
        help="safe retrograde cutoff used only to generate the sample certificate",
    )
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("--limit must be positive")
    if not 0 <= args.certificate_root <= args.certificate_limit:
        parser.error("certificate root must lie in 0..certificate-limit")

    print("Optimal 3n±1 game — reproducible local audit")
    print(f"Python: {sys.version.split()[0]}")
    print(f"Repository: {ROOT}")
    print(
        "Scope: regression tests + finite identities + one finite proof DAG.\n"
        "The global theorem remains a human proof; follow AUDIT.md to review it."
    )

    total_started = time.monotonic()
    print("\n=== repository layout ===")
    check_layout()
    check_documentation_links()
    check_lean_placeholders()

    run_stage(
        "unit and regression tests",
        [sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"],
    )
    run_stage(
        "finite arithmetic identities",
        [
            sys.executable,
            "scripts/verify_claims.py",
            "--limit",
            str(args.limit),
        ],
    )
    run_stage(
        "committed certificate example",
        [
            sys.executable,
            "scripts/verify_outcome_certificate.py",
            "certificates/examples/q10.json",
        ],
    )

    certificate, _ = capture_stage(
        "finite certificate generation",
        [
            sys.executable,
            "scripts/extract_proof.py",
            str(args.certificate_root),
            "--limit",
            str(args.certificate_limit),
        ],
    )
    parsed_certificate = json.loads(certificate)
    print(f"generated nodes: {parsed_certificate['node_count']}")
    digest = hashlib.sha256(certificate.encode("utf-8")).hexdigest()
    print(f"certificate SHA-256: {digest}")
    verify_from_stdin(
        "independent certificate verification",
        [sys.executable, "scripts/verify_outcome_certificate.py", "-"],
        certificate,
    )

    elapsed = time.monotonic() - total_started
    print("\n=== AUDIT PASSED ===")
    print(f"All machine-checkable local stages passed in {elapsed:.2f}s.")
    print("Next: perform the human proof audit in AUDIT.md Sections 4–5.")


if __name__ == "__main__":
    main()
