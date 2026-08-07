# Zenodo publication package

This directory contains the metadata and human checklist for depositing the
article as a Zenodo **Publication / Preprint**.

- `deposit-metadata.json` is a copyable metadata record for the web form or
  legacy deposit API.
- `UPLOAD_CHECKLIST.md` gives the exact Russian-language upload procedure.
- `../.zenodo.json` provides GitHub/Zenodo release metadata.
- `../scripts/build_zenodo_bundle.py` creates the preservation files under
  `dist/zenodo/` from a clean committed checkout.

The intended deposit contains the compiled article PDF, a small LaTeX source
archive, a full Git repository snapshot, and a SHA-256 manifest. The article
record uses CC BY 4.0; the verification software in the repository snapshot
uses the root MIT license.

Do not publish automatically. Preview the draft, verify the files and
metadata, and let the author press Zenodo's final `Publish` button.
