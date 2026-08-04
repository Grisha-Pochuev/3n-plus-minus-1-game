.PHONY: test verify retrograde suffixes

test:
	python -m unittest discover -s tests -v

verify:
	python scripts/verify_claims.py --limit 1000000

retrograde:
	python scripts/retrograde_prefix.py --limit 1000000

suffixes:
	python scripts/analyze_suffixes.py --limit 1000000 --suffix-bits 12
