# Stafford's identity over simple Noetherian rings: paper and Lean proof

A reader's guide to the paper "Stafford's identity over simple Noetherian
rings with infinite centre" and its Lean 4 formalization, for referees who know
ring theory but not Lean. It is generated from the paper
[itpplasma/generalized-stafford-paper](https://github.com/itpplasma/generalized-stafford-paper)
at commit 148631ad09edd9bcad8df3b6eaee6f7e60fc56ce, its statement map, and the
formal proof
[itpplasma/generalized-stafford-formal](https://github.com/itpplasma/generalized-stafford-formal)
at commit e63321970bcb7cf360a378bf48368f23d9bc1e6a, with
[AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis) at
22b3946c0cfc13960cd238319acea76ae0d5f168.

- [index.html](index.html), first screen: the main results as stated in the
  paper, the proof structure, and one line per lemma with its Lean declaration.
  Below it, and collapsed: the known results the paper cites (statement,
  reference with item and page, Lean declaration, which results use them), the
  paper and Lean side by side for every numbered environment and every mapped
  proof step, the dependency graph of the printed proofs, and the references.
- [paper/main.pdf](paper/main.pdf): the paper, built from the pinned commit.
- [lean-dag.html](lean-dag.html): the Lean dependency graph, contracted to the
  declarations of the statement map and expandable to every project declaration.
- [verification/index.html](verification/index.html): pins, the challenge
  checksum, and the verifier commands and results recorded by the formal
  repository.

Statements, numbers, titles and references are rendered from the paper's LaTeX
source (pandoc and KaTeX); nothing about the paper is kept by hand except the
location of the mapped proof steps (`data/steps.json`) and the printed pages of
cited items (`data/citations.json`). Every Lean identifier links to its
declaration with an offline hover preview. Project and AlgebraicAnalysis
sources are bundled under `sources/`; Mathlib and Lean core names link to their
pinned GitHub sources.

## Reading offline

Download or clone the repository and open `index.html` in a browser. The pages
load nothing from the network; only links to Mathlib and Lean core sources
need internet access.

## Regenerating

`site.json` holds the pins of the paper, the formal proof and the library, and
the inputs of the Lean graph; `data/overview.json` the groups of the overview
graph, as paper labels.

```sh
python3 scripts/rebuild.py                    # render from the recorded data
python3 scripts/rebuild.py --paper PATH       # rebuild the paper from a clone
python3 scripts/rebuild.py --formal PATH      # re-extract from a built checkout
node scripts/check-site.mjs . OUTPUT_DIR      # browser checks and screenshots
```

Rendering needs Python 3 with PyYAML and Graphviz. `--paper` needs latexmk,
pandoc, Node.js and KaTeX 0.16.22 (`npm install katex@0.16.22` under
`$SUPPLEMENTARY_CACHE/node`, or set `SUPPLEMENTARY_KATEX`); it fails when the
statement map and the paper disagree on labels, citations or proof steps.
`--formal` needs a checkout whose Lean files, lakefile, manifest and toolchain
equal the pinned commit, built with `lake build`, and elan on `PATH`. Lean's
own reference data and environment supply every link and graph edge. Scratch
files go to `$SUPPLEMENTARY_CACHE` (default
`/mnt/storage/cache/generalized-stafford-supplementary`). The browser check
needs Node.js and Chrome or Chromium (`CHROMIUM_PATH`).

Licences and attribution: [NOTICE](NOTICE).
