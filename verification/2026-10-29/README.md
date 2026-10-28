# Verification record, October 29, 2026

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`, Lean
module system. Source: research repository commit
`e743cf372b65dcb078567c29a84b3e86b8252986`, ported as recorded in
[`source-sync.json`](source-sync.json): every file is converted to the module
system, and two files have port edits (a Mathlib rename and a direct import).

| Check | Result |
| --- | --- |
| Lean source check | all 124 Lean files (120 library files, Challenge, Solution and two scripts) use the module system; none exceeds 10,000 lines |
| Fresh build | no project artifacts, Mathlib prebuilt at the pinned commit: 2347 jobs including Challenge and Solution, 3 min 30 s, largest process 1.7 GB, no `sorry` outside the three Challenge placeholders |
| Axiom audit | [`axioms.log`](axioms.log), [`axioms.json`](axioms.json): 19 queried declarations with only `propext`, `Classical.choice`, `Quot.sound`; `scripts/ScanAxioms.lean` scans all 2921 declarations of the library and Solution and finds no other axiom |
| API generation (doc-gen4) and website check | 120 modules, 4 min 33 s; 133 pages, all local targets present, displayed Challenge matches |
| `lake comparator` | not run: `bwrap` (bubblewrap) is not installed on the build machine |

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `32ad3faa2f6ab8745d7b6303fa6016b9855d2b76c8c54dc68422505456945fac` |
| `Solution.lean` | `5cf949579eb4165f047f0c452b068b01cf49cdbe8ab8bd8d3d6fb1e57545d9b9` |
| `comparator.json` | `3b69dbd5935296d376aae87b63aaf0dd16bed411ede3de8419188ced46d6bf42` |
| `docs/manuscript/main.tex` | `36defd3e07e4f4628ada451d39788f6ae9c6d5b2a3a320819cfca5a00506be5a` |
| `docs/manuscript/main.pdf` | `cfc7e7324c94ac801671471f5d8e87f8bd044f4696fd6285369f2efcd852f7ef` |

These are local runs, not a hosted Palomar preflight or registry acceptance.
