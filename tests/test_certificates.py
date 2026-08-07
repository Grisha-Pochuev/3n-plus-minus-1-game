from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "verify_outcome_certificate.py"
SPEC = importlib.util.spec_from_file_location("certificate_checker", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


def valid_certificate() -> dict[str, object]:
    # q=1 has children A(1)=2 and B(1)=0; the LOSS child 0 proves q=1 WIN.
    return {
        "schema_version": 1,
        "certificate_kind": "finite-outcome-proof-dag",
        "game": "conjugated-3n-plus-minus-1",
        "claim_scope": "one finite WIN/LOSS proof; not the global theorem",
        "limit": 10,
        "root": 1,
        "root_outcome": "WIN",
        "node_count": 2,
        "nodes": {
            "0": {"outcome": "LOSS", "rank": 1, "proof_children": []},
            "1": {"outcome": "WIN", "rank": 2, "proof_children": [0]},
        },
    }


class OutcomeCertificateTests(unittest.TestCase):
    def test_accepts_valid_certificate(self) -> None:
        summary = CHECKER.verify_certificate(valid_certificate())
        self.assertEqual(summary["outcome"], "WIN")

    def test_rejects_nonmove_edge(self) -> None:
        payload = valid_certificate()
        payload["nodes"]["1"]["proof_children"] = [3]  # type: ignore[index]
        with self.assertRaises(CHECKER.CertificateError):
            CHECKER.verify_certificate(payload)

    def test_rejects_non_decreasing_rank(self) -> None:
        payload = valid_certificate()
        payload["nodes"]["0"]["rank"] = 2  # type: ignore[index]
        with self.assertRaises(CHECKER.CertificateError):
            CHECKER.verify_certificate(payload)

    def test_rejects_unreachable_padding(self) -> None:
        payload = valid_certificate()
        payload["nodes"]["2"] = {  # type: ignore[index]
            "outcome": "WIN",
            "rank": 2,
            "proof_children": [0],
        }
        payload["node_count"] = 3
        with self.assertRaises(CHECKER.CertificateError):
            CHECKER.verify_certificate(payload)


if __name__ == "__main__":
    unittest.main()
