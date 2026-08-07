.PHONY: audit test verify retrograde suffixes proof certificate global-certificate zenodo lean

audit:
	python audit.py

test:
	python -m unittest discover -s tests -v

verify:
	python scripts/verify_claims.py --limit 1000000

retrograde:
	python scripts/retrograde_prefix.py --limit 1000000

suffixes:
	python scripts/analyze_suffixes.py --limit 1000000 --suffix-bits 12

proof:
	python scripts/extract_proof.py 1 --limit 100000

certificate:
	python scripts/extract_proof.py 100 --limit 200000 --output results/proof-100.json
	python scripts/verify_outcome_certificate.py results/proof-100.json

global-certificate:
	python scripts/verify_global_certificate.py

zenodo:
	python scripts/build_zenodo_bundle.py

lean:
	cd formal && lake build
