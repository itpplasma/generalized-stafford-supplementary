# Verification

This file records how the formalization is checked and what each check
establishes. [PLAN.md](../PLAN.md) holds the current gate states.

## Gates

| Gate | Command or record | What it establishes |
| --- | --- | --- |
| Pins | `scripts/check-pins.py` (run by `scripts/verify.sh`) | `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` match `dependency-pins.json`; one shared Mathlib package. |
| Build | `lake build` | The library and the solution compile at the pins. |
| Axiom audit | `scripts/verify.sh` | Every name in [endpoints.txt](endpoints.txt) exists and depends only on `propext`, `Classical.choice` and `Quot.sound`, checked with `--trust=0`. |
| Palomar check (local replay) | `scripts/verify-palomar.sh` | The challenge and solution copies are byte-identical, the challenge has exactly 46 `sorry` holes; the solution proves each theorem of `comparator.json` with the challenge's exact name and type; the challenge imports only Mathlib; the solution does not import the challenge; NanoDa and the Lean kernel accept the solution. |
| Statement faithfulness | independent statement-faithfulness audit (2 November 2026) passed; audited challenge sha256 `4cb2cd5e7a6043f4c38fecddb78850d6f8012048c91a7de7e188d18598dc9e95`; later changes name/docstring-only, confirmed by the final review | The challenge statements say what the written theorems say. |
| Human review | none yet | Required before any claim of human verification. |

Machine checks establish that the Lean proofs are correct for the Lean
statements. Whether those statements match the intended mathematics is the separate
statement-faithfulness question. Neither check is human review, and none of
them is publication.

## Release verification record

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
