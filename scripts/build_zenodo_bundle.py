#!/usr/bin/env python3
"""Build the immutable files intended for a manual Zenodo deposit.

Run this only from a clean committed checkout after paper/main.pdf has been
compiled and visually inspected. The script does not contact Zenodo.
"""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import zipfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "dist" / "zenodo"
PDF_SOURCE = ROOT / "paper" / "main.pdf"
PDF_NAME = "termination-optimal-3n-plus-minus-1.pdf"
SOURCE_NAME = "termination-optimal-3n-plus-minus-1-source.zip"
SNAPSHOT_NAME = "verification-repository-snapshot.zip"
METADATA_NAME = "deposit-metadata.json"
RELEASE_NAME = "RELEASE.txt"
MANIFEST_NAME = "SHA256SUMS.txt"
SOURCE_FILES = (
    "paper/main.tex",
    "paper/references.bib",
    "paper/README.md",
    "paper/LICENSE.md",
    "zenodo/deposit-metadata.json",
    "zenodo/UPLOAD_CHECKLIST.md",
)


def run_git(*args: str, capture: bool = False) -> str:
    completed = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        check=False,
        text=True,
        capture_output=capture,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() if capture else ""
        raise SystemExit(f"git {' '.join(args)} failed: {detail}")
    return completed.stdout.strip() if capture else ""


def require_clean_tracked_checkout() -> str:
    if subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=ROOT).returncode:
        raise SystemExit("tracked working-tree changes exist; commit them before packaging")
    if subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=ROOT).returncode:
        raise SystemExit("staged changes exist; commit them before packaging")
    return run_git("rev-parse", "HEAD", capture=True)


def validate_inputs() -> None:
    if not PDF_SOURCE.is_file() or not PDF_SOURCE.read_bytes().startswith(b"%PDF-"):
        raise SystemExit("paper/main.pdf is missing or is not a PDF; compile and inspect it first")
    missing = [name for name in SOURCE_FILES if not (ROOT / name).is_file()]
    if missing:
        raise SystemExit("missing source files: " + ", ".join(missing))
    metadata = json.loads((ROOT / "zenodo" / "deposit-metadata.json").read_text(encoding="utf-8"))
    encoded = json.dumps(metadata, ensure_ascii=False)
    for required in (
        "Pochuev, Grisha",
        "n_854@mail.ru",
        "https://github.com/Grisha-Pochuev/3n-plus-minus-1-game",
        "10.5281/zenodo.21844684",
        "CONDITIONAL_MACHINE_CHECK",
    ):
        if required not in encoded:
            raise SystemExit(f"deposit metadata is missing required value: {required}")


def write_source_archive(path: Path) -> None:
    with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for relative in SOURCE_FILES:
            data = (ROOT / relative).read_bytes()
            info = zipfile.ZipInfo(f"article-source/{relative}", date_time=(1980, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> None:
    revision = require_clean_tracked_checkout()
    validate_inputs()
    OUTPUT.mkdir(parents=True, exist_ok=True)

    outputs = [
        OUTPUT / PDF_NAME,
        OUTPUT / SOURCE_NAME,
        OUTPUT / SNAPSHOT_NAME,
        OUTPUT / METADATA_NAME,
        OUTPUT / RELEASE_NAME,
        OUTPUT / MANIFEST_NAME,
    ]
    for path in outputs:
        if path.exists():
            path.unlink()

    shutil.copyfile(PDF_SOURCE, OUTPUT / PDF_NAME)
    shutil.copyfile(ROOT / "zenodo" / "deposit-metadata.json", OUTPUT / METADATA_NAME)
    write_source_archive(OUTPUT / SOURCE_NAME)
    run_git("archive", "--format=zip", f"--output={OUTPUT / SNAPSHOT_NAME}", "HEAD")

    (OUTPUT / RELEASE_NAME).write_text(
        "Termination under Optimal Play in the Two-Player 3n+/-1 Game\n"
        f"Git revision: {revision}\n"
        "Repository: https://github.com/Grisha-Pochuev/3n-plus-minus-1-game\n"
        "Published DOI: https://doi.org/10.5281/zenodo.21844684\n"
        "Correspondence: n_854@mail.ru\n"
        "Certificate scope: CONDITIONAL_MACHINE_CHECK; see certificates/global-routing-certificate.md\n",
        encoding="utf-8",
        newline="\n",
    )

    manifest_targets = [path for path in outputs if path.name != MANIFEST_NAME]
    manifest = "".join(f"{sha256(path)}  {path.name}\n" for path in manifest_targets)
    (OUTPUT / MANIFEST_NAME).write_text(manifest, encoding="ascii", newline="\n")

    print(f"Zenodo bundle created for revision {revision}")
    for path in outputs:
        print(f"{path.relative_to(ROOT)} ({path.stat().st_size} bytes)")
    print("No network request was made. Follow zenodo/UPLOAD_CHECKLIST.md.")


if __name__ == "__main__":
    main()
