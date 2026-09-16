# Reproduction and proof boundaries

## Requirements

- Lean 4.33.0, with its standard library; the root `lean-toolchain` pins it.
- Python 3.10 or later, standard library only.
- A TeX installation with latexmk, PDFLaTeX and BibTeX only if rebuilding
  the paper. Reading the PDF and checking Lean do not need TeX.

No network access is needed for verification once these tools are installed.
Python is not trusted as a theorem prover: finite data and the infinite
parameter arguments are checked inside Lean.

## Commands

From the repository root, or the `anc/` directory of the arXiv source:

```text
python scripts/check_lean.py --lean /absolute/path/to/lean
python scripts/check_paper_blocks.py
python scripts/check_width3_counts.py
```

The first command recompiles all 19 modules, in dependency order, using a
local `LEAN_PATH`. It creates `build/S3RD/lean/*.olean` and
`build/reports/lean_report.json`. It checks the compiler version, rejects
admitted proofs, and audits the printed axioms. A successful run ends with
`PASS Audit` and report status `PASS`. The width-four search is a kernel
computation and can take several minutes. Each module defaults to a
1200-second timeout; use `--timeout 3600` if necessary.

The other commands check explicit finite blocks and the width-three count
for circumferences 3 through 36. They write reports under `build/reports/`.
These are supplemental finite checks, not proofs of all parameter values.

## Main theorem entry points

| Source | Statement or role |
|---|---|
| `S3RD/lean/Audit.lean` | `all_widths_ge_five_graph_optimal`: all widths at least five |
| `S3RD/lean/Audit.lean` | `all_odd_graph_optimal`: odd widths including width three |
| `S3RD/lean/Audit.lean` | `width4_odd_graph_optimal`, `even_even_graph_optimal_large`: remaining width-four families |
| `S3RD/lean/WidthFour.lean` | `width4_four_optimal`, `width4_eight_optimal`: short width-four exceptions |
| `S3RD/lean/Semantics.lean` | Finite vertices, cylinder adjacency and equivalence of validity predicates |
| `S3RD/lean/WidthThreeCount.lean` | Periodic equality cases and labeled counts |

The standard axioms reported are `propext`, `Classical.choice`, and
`Quot.sound`. There are no admitted goals, custom mathematical axioms,
or `native_decide` proofs. The statements include existence of an admissible
coloring and optimality against every admissible coloring.

## Frozen reports and integrity

`reports/lean_report.json` records a successful verification of the exact
released source bytes. `python scripts/check_integrity.py` compares these
hashes and the files listed in `MANIFEST.json`. No ZIP files are required. It does not
rerun Lean and does not replace a fresh proof rebuild.

Build output is deliberately kept outside the frozen `reports/` directory.
The frozen reports describe the distributed version. Fresh verification writes
separate reports so the original evidence remains available for comparison.

## Rebuilding the manuscript

```text
python scripts/build_paper.py
```

The paper build writes a new PDF and bibliography to `build/paper/`, preserving
the distributed files. The supplied
`.bbl` records the resolved bibliography. `paper/repository.tex` is a small
LaTeX input for the optional repository link.

Git newline conversion is disabled by `.gitattributes` so that checkouts retain
the exact bytes identified by the verification hashes.
