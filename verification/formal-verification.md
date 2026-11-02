# Verification

This file records how the formalization is checked and what each check
establishes. [PLAN.md](../PLAN.md) holds the current gate states.

## Gates

| Gate | Command or record | What it establishes |
| --- | --- | --- |
| Pins | `scripts/check-pins.py` (run by `scripts/verify.sh`) | `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` match `dependency-pins.json`; one shared Mathlib package. |
| Build | `lake build` | The library and the solution compile at the pins. |
| Axiom audit | `scripts/verify.sh` | Every name in [endpoints.txt](endpoints.txt) exists and depends only on `propext`, `Classical.choice` and `Quot.sound`, checked with `--trust=0`. |
| Palomar check (local replay) | `scripts/verify-palomar.sh` | The challenge and solution copies are byte-identical, the challenge has exactly 41 `sorry` holes; the solution proves each theorem of `comparator.json` with the challenge's exact name and type; the challenge imports only Mathlib; the solution does not import the challenge; NanoDa and the Lean kernel accept the solution. |
| Statement faithfulness | statement-faithfulness audit | PASS: independent statement-faithfulness audits of 2 November 2026 of the 40-theorem challenge (sha256 `07efe11f…`, all statements unchanged from the audited 46-theorem challenge except the new `corollaryC2_omega`; repair applied: `knownDimension_hAll_of_omega` added) and of that addition (sha256 `778588a0…`); the final change is docstring-only (precise McConnell--Robson locators 6.2.3 and 6.3.9), sha256 `272c7eb9454d5ef02e6d5bb5ea41e0cbc3d112be9d2a5e931a29b7226dfd413f`. |
| Human review | none yet | Required before any claim of human verification. |

Machine checks establish that the Lean proofs are correct for the Lean
statements. Whether those statements match the intended mathematics is the separate
statement-faithfulness question. Neither check is human review, and none of
them is publication.

## Verification record: module-system port

Status: commit `dd9447b` on branch `module-port`, 2 November 2026, same pins and Palomar tool revisions as the records below. Every tracked Lean file now begins with `module`, imports with `public import` and opens `@[expose] public section`, as the Palomar registry requires. In the challenge (both copies) this changes only the header, the import keywords and the section visibility, except for one further change: the proofs of the six non-compared closure lemmas of `diffOps` (`endCommutator_add`, `endCommutator_mul`, `isOrderLE_zero`, `isOrderLE_add`, `isOrderLE_succ`, `isOrderLE_mul`) were rewritten, statements unchanged, so that they create no auxiliary declarations. In a module such declarations get private names containing the module name, and Comparator, which compares the proof terms that `diffOps` uses, rejected the solution copy in `GeneralizedStafford/Challenge/DiffOpTransport.lean` until both sides were rewritten identically. This proof-text change was approved. The challenge was then shortened to 924 lines for Palomar's 1,000-line limit by rewrapping and condensing comments and docstrings and removing blank lines, with declarations unchanged. Commands, each under a 16 GiB memory cap:

```sh
PYTHON=python3 scripts/verify.sh
scripts/verify-palomar.sh
```

Both exited 0, with the same outcomes as the record below: 81 endpoint axiom reports with axioms exactly `propext`, `Classical.choice`, `Quot.sound`; duplicate files byte-identical, exactly 41 `sorry` holes, both import-closure checks passed, and all 41 compared theorems accepted (`nanoda kernel accepts the solution`, `Lean default kernel accepts the solution`, `Your solution is okay!`). The challenge sha256 is `b8404b6adc97f3433dc7a76f06e41135bd6457f4cb56aa2b7e5dcbbbc9ef669e`; it has 924 lines and 51,793 bytes, within Palomar's limits for a challenge (1,000 lines, 100 KiB).

Statement preservation. Against the challenge at `50c0138` (sha256 `272c7eb9…`): `#check @T` with `pp.all`, `pp.proofs` and `pp.universes` printed identical output for all 41 compared theorems `T`; and a dump of every constant of the module `GeneralizedStaffordChallenge` (kind, universe parameters, type, and the value of each definition, each with its structural `Expr.hash`) is identical for all 182 constants present on both sides. The 15 constants present only at `50c0138` are the auxiliary declarations of the six rewritten proofs (matchers, structural-recursion functionals, `abel` and `omega` lemmas); none is used by a compared statement.

## Verification record: challenge restricted to the paper

Status: commit `e63321970bcb7cf360a378bf48368f23d9bc1e6a` on branch `paper-scope`, 2 November 2026, with the pins of the record below (AlgebraicAnalysis `22b3946c0cfc13960cd238319acea76ae0d5f168`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`). The challenge was reduced to the numbered results of the paper: `corollaryB_dimension`, `corollaryC3_lower`, `corollaryC3_upper`, `filteredCorollaryB`, `filteredGeneratorBounds`, `envelopingCorollaryB` and `envelopingGeneratorBounds` were removed, with the challenge definitions only they used and the library module `GeneralizedStafford/GeneratorBounds.lean`, and `corollaryC2_omega` (the omega case of C.2, which Corollary C states) and `knownDimension_hAll_of_omega` (McConnell-Robson 6.3.9, the cited input of Corollary B) were added. The 39 other statements are unchanged. Commands, as below, each under a 16 GiB memory cap:

```sh
PYTHON=python3 scripts/verify.sh
scripts/verify-palomar.sh
```

Both exited 0. `verify.sh`: pins, full build of `GeneralizedStafford` and `GeneralizedStaffordSolution`, 81 endpoint axiom reports with `--trust=0`, axioms exactly `propext`, `Classical.choice`, `Quot.sound`. `verify-palomar.sh`: duplicate files byte-identical, exactly 41 `sorry` holes, both import-closure checks passed, and in the local replay of the Palomar check (same tool revisions as below; Landrun in best-effort mode) all 41 compared theorems were accepted (`nanoda kernel accepts the solution`, `Lean default kernel accepts the solution`, `Your solution is okay!`). `tests/SolutionOracle.lean` reports the three standard axioms for each of the 41 theorems. The challenge sha256 is `272c7eb9454d5ef02e6d5bb5ea41e0cbc3d112be9d2a5e931a29b7226dfd413f`. No statement-faithfulness audit has been run on this file yet.

## Release verification record of the 46-theorem challenge

This record and the statement audits it lists apply to the earlier challenge, superseded by the record above.

Status: commit `17f84e3bc693b309f40dc5c75a901ec891214bf0`, 2 November 2026, with AlgebraicAnalysis pinned at `22b3946c0cfc13960cd238319acea76ae0d5f168` and Mathlib at `c55e6e786f49471c72fbddbec5415808896aec1e`. Its parent commits move the application-independent Goldie splitting lemmas of `GeneratorBounds.lean` to AlgebraicAnalysis (`AlgebraicAnalysis.RingTheory.Goldie.Splitting`) and re-pins it; the challenge, solution and `comparator.json` bytes are those of `4eca6de8e3ce`. Commands, from the repository root with `~/.elan/bin` on `PATH`:

```sh
PYTHON=python3 scripts/verify.sh
scripts/bootstrap-palomar-tools.sh   # CARGO_BUILD_JOBS=2; same tool revisions as below
scripts/verify-palomar.sh
```

All exited 0. `verify.sh`: pins (exact Lean, AlgebraicAnalysis, one shared Mathlib and 8 transitive dependencies); full build of `GeneralizedStafford` and `GeneralizedStaffordSolution`; 94 endpoint axiom reports with `--trust=0`, axioms exactly `propext`, `Classical.choice`, `Quot.sound`. `verify-palomar.sh`: duplicate files byte-identical, exactly 46 `sorry` holes, both import-closure checks passed, and in this local replay of the Palomar check (Comparator with NanoDa and the Lean kernel; Landrun in best-effort mode) all 46 compared theorems were accepted (`nanoda kernel accepts the solution`, `Lean default kernel accepts the solution`, `Your solution is okay!`). The sandbox was not re-probed in this run. The challenge sha256 is `2546aae28ceca93fa72326d09bf415fd15a40add94967f8148ab0492c6ef06a5`.

Statement audits (2 November 2026), unchanged by this run: 14 abstract (audited `4cb2cd5e...9e95`, later name/docstring changes only), 11 Weyl-algebra (`1158aeb9...8fd8c7`), 8 filtered-ring (`cf905b9a...a0ba`), 7 enveloping-algebra (`bf6a8b90...22697`) and 6 differential-operator statements (`2546aae2...ef06a5`, no repair; definitions verbatim from the registered Global Stafford challenge), with docstring-only repairs where requested.

The previous record, at commit `4eca6de8e3ce8e4d7561cf3d012e9dcf86ceef1d` with AlgebraicAnalysis at `71af6ecc07335b67cad93451f33e26b0412dda6a`, passed the same checks with the same challenge sha256.

## Palomar comparator run, 2 November 2026

This run covered the 12 compared theorems solved at that time (C.3 was not
yet in `comparator.json`). It establishes the tool set and the sandbox facts
below; the release record above supersedes its theorem list.

Tool revisions (`scripts/bootstrap-palomar-tools.sh`, checked by
`scripts/verify-palomar.sh`), all for Lean `leanprover/lean4:v4.35.0-rc3`:

| Tool | Exact revision |
| --- | --- |
| Comparator | `fd5d5bcf14177b187f66d4502071268d877887c3` (tag `v4.35.0-rc3`; its `lean-toolchain` is v4.35.0-rc3) |
| lean4export | `66f1fb4bc256072069767fce52d39480e4524869` (tag `v4.35.0-rc3`; the revision Comparator's manifest pins) |
| NanoDa | `8de7e0c4ed3052745a7f8725164efd9e76d84c56` (head of the default branch on 2026-11-02; no toolchain pin upstream) |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (on `main`; no Lean dependency) |

Commands, from the repository root with `~/.elan/bin` on `PATH`:

```sh
scripts/bootstrap-palomar-tools.sh   # CARGO_BUILD_JOBS=2
scripts/verify-palomar.sh
```

Outcome: both commands exited 0. `verify-palomar.sh` built
`GeneralizedStaffordChallenge` and `GeneralizedStaffordSolution`, passed both
import-closure checks, and printed `nanoda kernel accepts the solution`,
`Lean default kernel accepts the solution` and `Your solution is okay!`. The
log is `.lake/verification/comparator.log` (untracked).

Sandbox. Landrun ran with `--best-effort`, which Comparator always passes. The
kernel offered Landlock ABI v7, below the v9 that Landrun requests, so Landrun
enforced filesystem restrictions only: a probe showed unlisted paths
unreadable and unwritable, while the network and scope rules of the V9
profile were not applied. A strict run without `--best-effort` fails at
sandbox setup. A second run through a logging shim confirmed that the
sandboxed steps (lake builds and `lean4export`) went through
`scripts/landrun-wrapper.sh`. No unsandboxed diagnostic run was needed.

Tool path. Palomar's About page says that records verified with a Lean
toolchain's own `lake comparator` cite the toolchain commit and bundled-tool
digests, and that only earlier records cite standalone Comparator,
lean4export and Landrun revisions. This run used the standalone tools. The
toolchain's `lake comparator` was tried once and stopped because `bwrap` is
not installed; it was not installed. The Palomar pages state no required tool
version. The registry entry pages are rendered by JavaScript, so no
registered entry was inspected.

## Earlier records

Verification records of the pre-Palomar development (87 and 170 endpoint
audits, the statement-map checker, the projective-width extension) apply to
the tree on branch `archive/pre-palomar-2026-11-02` only.
