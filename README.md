# Theorem A in Lean: supplementary material

A reader's guide to the Lean 4 formalization of Theorem A (affine generation
over simple Noetherian rings with infinite centre), its corollaries and its
applications, for referees who know ring theory but not Lean. The pages are
generated from the formal repository
[itpplasma/generalized-stafford-formal](https://github.com/itpplasma/generalized-stafford-formal)
at commit 17f84e3bc693b309f40dc5c75a901ec891214bf0, with
[AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis) at
22b3946c0cfc13960cd238319acea76ae0d5f168.

- [index.html](index.html): the main statements, the proof structure and one
  line per main lemma with its Lean declaration, and, set apart, the cited
  literature results that the Lean proof formalizes. Rows expand to the full
  statement, the proof outline and the Lean text. The comparison with the
  paper's printed proofs is a placeholder until the paper draft exists.
- [lean-dag.html](lean-dag.html): the Lean dependency graph, contracted to the
  key declarations and expandable to every project declaration.
- [verification/index.html](verification/index.html): pins, the challenge
  checksum, and the verifier commands and results recorded by the formal
  repository.

Every Lean identifier links to its declaration. Project and AlgebraicAnalysis
sources are bundled under `sources/`; Mathlib and Lean core names link to
their pinned GitHub sources. Hovering or focusing a link shows the
declaration's statement.

## Reading offline

Download or clone the repository and open `index.html` in a browser. The pages
load nothing from the network; only links to Mathlib and Lean core sources
need internet access.

## Regenerating

`site.json` holds the pins, the Lean modules to import and the library inputs
of the graph; `data/overview.json` holds the statements, the main lemmas and
their Lean names, with the paper's labels; `data/citations.json` holds the
literature results the paper cites and the Lean declarations that formalize
them, keyed by citation (which results use them is computed from Lean). With Python 3 and Graphviz:

```sh
python3 scripts/rebuild.py                    # render from the recorded data
python3 scripts/rebuild.py --formal PATH      # re-extract from a built checkout
python3 scripts/rebuild.py --statement-map ../generalized-stafford-paper/statement-map.yaml
node scripts/check-site.mjs . OUTPUT_DIR      # browser checks and screenshots
```

`--formal` needs a checkout whose Lean files, lakefile, manifest and toolchain
equal the pinned commit, built with `lake build`, and elan on `PATH`; the
scripts refuse any other state. Lean's own reference data (`.ilean` files)
and environment supply every link and graph edge; no name is matched
textually. `--statement-map` checks the Lean names against the paper's
statement map (PyYAML). Scratch files go to
`$SUPPLEMENTARY_CACHE` (default `/mnt/storage/cache/generalized-stafford-supplementary`).
The browser check needs Node.js and Chrome or Chromium (`CHROMIUM_PATH`).

Licences and attribution: [NOTICE](NOTICE).
