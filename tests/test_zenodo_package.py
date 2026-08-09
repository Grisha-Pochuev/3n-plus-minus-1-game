from __future__ import annotations

import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EMAIL = "n_854@mail.ru"
REPOSITORY = "https://github.com/Grisha-Pochuev/3n-plus-minus-1-game"
PROBLEM_PAGE = "https://althofer.de/collatz-prizes.html"
DOI = "10.5281/zenodo.21844684"


class ZenodoPackageTests(unittest.TestCase):
    def test_zenodo_metadata_contains_required_identity_and_links(self) -> None:
        metadata = json.loads((ROOT / ".zenodo.json").read_text(encoding="utf-8"))
        encoded = json.dumps(metadata, ensure_ascii=False)
        for required in ("Pochuev, Grisha", REPOSITORY, PROBLEM_PAGE, DOI):
            self.assertIn(required, encoded)

    def test_deposit_metadata_exposes_scope_and_correspondence(self) -> None:
        metadata = json.loads(
            (ROOT / "zenodo" / "deposit-metadata.json").read_text(encoding="utf-8")
        )
        encoded = json.dumps(metadata, ensure_ascii=False)
        for required in (EMAIL, REPOSITORY, DOI, "CONDITIONAL_MACHINE_CHECK"):
            self.assertIn(required, encoded)

    def test_article_source_contains_publication_links_and_open_status(self) -> None:
        source = (ROOT / "paper" / "main.tex").read_text(encoding="utf-8")
        self.assertIn(EMAIL, source)
        self.assertIn("github.com/Grisha-Pochuev/3n-plus-minus-1-game", source)
        self.assertIn("AlthoferProblemPage", source)
        self.assertIn(DOI, source)
        self.assertIn("Target theorem (open)", source)
        self.assertIn("Remaining attachment lemma", source)
        self.assertIn("not claimed as proved", source)

    def test_compiled_article_is_valid_if_present(self) -> None:
        # The audited repair deliberately removes the pre-audit PDF because it
        # states the old, invalid global conclusion.  A PDF becomes mandatory
        # only for a release bundle rebuilt from the current source.  If a
        # developer has built one locally, still reject a non-PDF placeholder.
        pdf = ROOT / "paper" / "main.pdf"
        if pdf.exists():
            self.assertTrue(pdf.is_file())
            self.assertTrue(pdf.read_bytes().startswith(b"%PDF-"))


if __name__ == "__main__":
    unittest.main()
