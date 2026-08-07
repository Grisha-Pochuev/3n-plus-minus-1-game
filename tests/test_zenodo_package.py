from __future__ import annotations

import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EMAIL = "n_854@mail.ru"
REPOSITORY = "https://github.com/Grisha-Pochuev/3n-plus-minus-1-game"
PROBLEM_PAGE = "https://althofer.de/collatz-prizes.html"


class ZenodoPackageTests(unittest.TestCase):
    def test_zenodo_metadata_contains_required_identity_and_links(self) -> None:
        metadata = json.loads((ROOT / ".zenodo.json").read_text(encoding="utf-8"))
        encoded = json.dumps(metadata, ensure_ascii=False)
        for required in ("Pochuev, Grisha", REPOSITORY, PROBLEM_PAGE):
            self.assertIn(required, encoded)

    def test_deposit_metadata_exposes_scope_and_correspondence(self) -> None:
        metadata = json.loads(
            (ROOT / "zenodo" / "deposit-metadata.json").read_text(encoding="utf-8")
        )
        encoded = json.dumps(metadata, ensure_ascii=False)
        for required in (EMAIL, REPOSITORY, "CONDITIONAL_MACHINE_CHECK"):
            self.assertIn(required, encoded)

    def test_article_source_contains_publication_links(self) -> None:
        source = (ROOT / "paper" / "main.tex").read_text(encoding="utf-8")
        self.assertIn(EMAIL, source)
        self.assertIn("github.com/Grisha-Pochuev/3n-plus-minus-1-game", source)
        self.assertIn("AlthoferProblemPage", source)

    def test_compiled_article_is_present(self) -> None:
        pdf = ROOT / "paper" / "main.pdf"
        self.assertTrue(pdf.is_file())
        self.assertTrue(pdf.read_bytes().startswith(b"%PDF-"))


if __name__ == "__main__":
    unittest.main()
