# Manuscript evolution archive

This directory preserves the development history of the manuscript for the two-player `3n ± 1` game.

The versions are arranged chronologically:

```text
v1
└── v2
    └── v3.0
        └── v4.0
            └── v5.0
                └── v6.3
                    └── v7.0
```

Each version directory is a snapshot of the article and, where available, the verification scripts, audit notes, routing certificates, checksums, and other supporting files that accompanied that stage of the proof.

These files are kept for provenance and comparison. They are **historical snapshots, not independent claims that every intermediate version is correct**. Some versions were superseded specifically because later audits found gaps or required repairs.

The current working manuscript remains `paper/main.tex` / `paper/main.pdf`. New publication-ready versions should be developed there; this archive should only grow by adding a new version directory, without rewriting earlier snapshots.

## Preserved versions

- `v1/` — first preserved article snapshot.
- `v2/` — second article snapshot. A second pair of source files present in the project sources was byte-for-byte identical to this version and is therefore not duplicated here.
- `v3.0/` — article plus first preserved standalone verification script.
- `v4.0/` — expanded article package with verification, routing certificate, self-audit, and checksums.
- `v5.0/` — audit-hardened package with explicit open proof obligations and repair report.
- `v6.3/` — larger audit-hardened manuscript with structural verification and audit report.
- `v7.0/` — latest preserved historical package from the project sources, including article, LaTeX source, verification output, PDF preflight/inspection notes, and audit report.

The archive is intentionally append-only in spirit: future `v8`, `v9`, and later snapshots should be added as new sibling directories so that the full proof-development lineage remains visible.
