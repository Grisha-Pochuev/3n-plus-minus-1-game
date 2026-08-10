# Zenodo publication package

Published historical record: <https://doi.org/10.5281/zenodo.21844684>.

**Do not publish a new proof version from this repair branch.**  The published
record predates the external Althöfer audit.  Corrected Sections 136--138 now
withdraw the invalid old entry argument, prove the missing two-level
arithmetic normalization, and isolate an arbitrary exponent-one
provenance/rank attachment lemma that is still open.

The files in this directory are therefore retained for provenance and for a
future corrected release only after that lemma has been proved and the whole
assembly has been independently re-audited.

- `deposit-metadata.json` records the audited repair status.
- `UPLOAD_CHECKLIST.md` is historical/future release guidance, not an
  instruction to publish the current branch.
- `../.zenodo.json` records the same open-proof status.
- `../scripts/build_zenodo_bundle.py` should be used only after a future
  completed proof has been re-reviewed.

The stale pre-audit `paper/main.pdf` is deliberately absent from this branch.
The authoritative article source is `paper/main.tex`, whose title, abstract,
and theorem-status section now state that the global theorem is open.
