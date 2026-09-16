# Singleton Three-Rainbow Domination of Cylindrical Graphs

Paper and machine-checkable proofs of the exact singleton three-rainbow
domination number of `P_m □ C_n`, for every `m,n ≥ 3`.

- **Read the paper:** [PDF](paper/main.pdf) · [LaTeX source](paper/main.tex)
- **Reproduce:** [verification guide](docs/REPRODUCIBILITY.md)
- **AI assistance:** [disclosure](docs/AI_ASSISTANCE.md)

The singleton condition allows at most one color per vertex. This is distinct
from ordinary rainbow domination, which permits sets of colors at a vertex.
The paper cites the relevant prior results and identifies its improvement
relative to Žerovnik (2026). Formal verification establishes the stated
theorems, not publication priority or peer-review status.

## Results

All circumferences below satisfy `n ≥ 3`.

| Width | Exact value |
|---|---|
| Odd `m ≥ 5` | `ceil(m*n/2)` |
| Even `m ≥ 6` | `m*n/2 + (n mod 2)` |
| `m = 3` | `ceil(3*n/2)`, plus 1 exactly when `n mod 12` is 2 or 10 |
| `m = 4`, odd `n` | `2*n + 1` |
| `m = 4`, even `n` | `2*n`, except 9 at `n = 4` and 18 at `n = 8` |

## Verify from a fresh checkout

Install **Lean 4.33.0** (with bundled Std) and **Python 3.10+**. No mathlib,
SciPy, or additional Python packages are required. From this directory:

```text
python scripts/check_lean.py --lean /absolute/path/to/lean
python scripts/check_paper_blocks.py
python scripts/check_width3_counts.py
```

With the correct Lean on PATH, omit `--lean`. On Windows the executable
normally ends in `lean.exe`. Quote paths containing spaces.
The full proof rebuild can take around 15 minutes; width four dominates
the runtime. For slower machines add `--timeout 3600`.

The scripts write only to ignored `build/` paths. `reports/` contains frozen
release evidence; compare the fresh source hashes to those records.
The proof audit permits only `propext`, `Classical.choice`, and `Quot.sound`.

## Repository layout

```text
S3RD/lean/     19 Lean modules; original module names preserved
scripts/      proof checks, source integrity check, and paper build
paper/        English paper, bibliography, finite certificate appendix
reports/      recorded verification results for the released sources
docs/         reproduction guide and AI assistance disclosure
lean-toolchain  pinned Lean version
CITATION.cff   citation metadata
```

The research history, search experiments, local caches, and old manuscripts
are not needed to reproduce this release and are not distributed here.

## Check source integrity

```text
python scripts/check_integrity.py
```

This checks the distributed file hashes and matches all 19 Lean sources to
`reports/lean_report.json`. It requires no archives or build outputs.
A matching hash identifies the recorded sources; run Lean to verify the proofs.

## Build the paper

With a TeX installation providing PDFLaTeX, BibTeX, and latexmk:

```text
python scripts/build_paper.py
```

The rebuilt PDF and bibliography are written to `build/paper/`. The distributed
paper files remain unchanged. The included PDF can be read without installing TeX.

## Status and reuse

This repository is a preprint and proof artifact, not a record of journal
acceptance. No arXiv identifier or DOI is assigned here.
The author has not selected a separate reuse license for the repository;
no open-source license is implied by public availability. 
