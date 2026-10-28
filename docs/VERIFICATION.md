# Verification

The library proves Theorem A, Corollary B, Corollary 5.6 and every numbered
result of the October 18, 2026 manuscript with mathematical content; the
[correspondence](PAPER-CORRESPONDENCE.md) lists the declarations. Records are
in [`verification/`](../verification/).

## Independent statement

`BrickAccessibility/Statement.lean` states the three principal results with
Mathlib alone: finite quivers and their path algebras presented by vertex
idempotents and arrows, admissible bound quiver presentations
`π : kQ → Λ` with `R^m ⊆ ker π ⊆ R²`, the special biserial conditions on such a
presentation, biserial algebras through the radicals of indecomposable
projective modules on both sides, basic algebras, bricks, brick-finiteness,
representation-finiteness, brick accessibility and the set of brick
dimensions. Modules are finite-dimensional right modules, that is, modules over
`Λᵐᵒᵖ`.

`BrickAccessibility.theoremA`, `corollaryB` and `corollaryBiserial` prove these
statements. The library works with path data on `Λᵐᵒᵖ`; the bridges are
`AdmissiblePresentation.toPathData` (presentation to path data) and
`PathData.isSpecialBiserial_of_pathData` (path data with vertices and arrows
independent modulo paths of length two to an admissible special biserial
presentation, used for Corollary 5.6).

`Challenge.lean` is generated from `Statement.lean` with three deliberate
`sorry` placeholders, for Theorem A, Corollary B and Corollary 5.6.
`Solution.lean` proves them and does not import the Challenge.

## Results of October 29, 2026

| Check | Result |
| --- | --- |
| Lean source check (`scripts/check-lean-sources.py`) | every file uses the module system and has at most 10,000 lines |
| Fresh build (no project artifacts, Mathlib prebuilt at the pinned commit) | 2347 jobs including Challenge and Solution, 3 min 30 s, largest process 1.7 GB |
| Axiom audit, `scripts/AxiomAudit.lean` | 19 declarations, including the three Challenge theorems proved in Solution; only `propext`, `Classical.choice`, `Quot.sound`; a scan of all 2921 declarations (`scripts/ScanAxioms.lean`) finds no other axiom |
| API generation (doc-gen4) and website check | 120 modules, 4 min 33 s; 133 pages, all local targets present, displayed Challenge matches |
| `lake comparator` on Challenge and Solution | not yet run: `bwrap` (bubblewrap) is not installed on the build machine |

The [record](../verification/2026-10-29/README.md) gives the hashes. These are
local runs, not a hosted Palomar preflight or registry acceptance.

## Reproduce the checks

```sh
python3 scripts/check-lean-sources.py
lake exe cache get
lake build
python3 scripts/audit_axioms.py
python3 scripts/generate_challenge.py --check
lake build Challenge Solution
./scripts/verify-comparator.sh
```

`verify-comparator.sh` follows the Palomar template: it runs the
`lake comparator` bundled with the toolchain, with the Lean kernel and the
bundled NanoDa and con-ron checkers, inside a `bwrap` (bubblewrap) sandbox, so
`bwrap` must be on the path. The workflow
[Palomar preflight](../.github/workflows/palomar-preflight.yml) runs Palomar's
complete mechanical verification on GitHub for a chosen commit.
