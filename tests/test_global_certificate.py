from __future__ import annotations

import copy
import importlib.util
import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "verify_global_certificate.py"
CERTIFICATE = ROOT / "certificates" / "global-routing.json"
SPEC = importlib.util.spec_from_file_location("global_certificate_checker", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


def valid_certificate() -> dict[str, object]:
    return json.loads(CERTIFICATE.read_text(encoding="utf-8"))


class GlobalCertificateTests(unittest.TestCase):
    def test_accepts_committed_inventory(self) -> None:
        summary = CHECKER.verify_certificate(valid_certificate())
        self.assertEqual(summary["status"], "CONDITIONAL_MACHINE_CHECK")
        self.assertEqual(summary["transitions"], 46)

    def test_rejects_missing_declared_case(self) -> None:
        payload = valid_certificate()
        payload["transitions"] = payload["transitions"][:-1]  # type: ignore[index]
        with self.assertRaises(CHECKER.CertificateError):
            CHECKER.verify_certificate(payload)

    def test_rejects_reset_before_strict_decrease(self) -> None:
        payload = valid_certificate()
        transition = copy.deepcopy(payload["transitions"][0])  # type: ignore[index]
        transition["rank_effect"] = ["reset", "preserve", "preserve", "preserve"]
        payload["transitions"][0] = transition  # type: ignore[index]
        with self.assertRaises(CHECKER.CertificateError):
            CHECKER.verify_certificate(payload)

    def test_rejects_equal_rank_cycle(self) -> None:
        payload = valid_certificate()
        transition = copy.deepcopy(payload["transitions"][0])  # type: ignore[index]
        transition["rank_effect"] = ["preserve"] * 4
        payload["transitions"][0] = transition  # type: ignore[index]
        with self.assertRaises(CHECKER.CertificateError):
            CHECKER.verify_certificate(payload)

    def test_rejects_overlapping_integer_partition(self) -> None:
        payload = valid_certificate()
        partition = payload["guard_partitions"]["b_valuation"]  # type: ignore[index]
        partition["cases"][0]["max"] = 3
        with self.assertRaises(CHECKER.CertificateError):
            CHECKER.verify_certificate(payload)

    def test_rejects_proof_source_hash_mismatch(self) -> None:
        payload = valid_certificate()
        payload["proof_source"]["sha256"] = "0" * 64  # type: ignore[index]
        with self.assertRaises(CHECKER.CertificateError):
            CHECKER.verify_certificate(payload)


if __name__ == "__main__":
    unittest.main()
