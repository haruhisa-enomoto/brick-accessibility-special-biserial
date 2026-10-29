# Brick accessibility for brick-finite special biserial algebras

[Manuscript](docs/MANUSCRIPT.md) ·
[Main theorems in Lean](BrickAccessibility/MainTheorems.lean) ·
[Independent statement](BrickAccessibility/Statement.lean) ·
[Paper correspondence](docs/PAPER-CORRESPONDENCE.md)

This repository contains a complete Lean 4 formalization of the manuscript
*Brick accessibility for brick-finite special biserial algebras* (revision of
October 18, 2026). A *brick* is a nonzero module whose endomorphism ring is a
division ring. Mousavand asked whether the dimensions of bricks over a
representation-finite algebra have no gaps. The paper answers this for
biserial algebras.

**Theorem A.** Let `k` be an algebraically closed field and `Λ` a basic
finite-dimensional brick-finite special biserial `k`-algebra. Every nonsimple
brick `M` has a brick submodule or a brick quotient of dimension `dim M - 1`.

**Corollary B.** Every brick over such an algebra is *brick accessible*: it can
be reduced to a simple module by passing successively to a brick submodule or
quotient of dimension one less. If `Λ` is nonzero, its brick dimensions form an
interval `{1, 2, …, N}`.

**Corollary 5.6.** Both conclusions hold for basic representation-finite
biserial algebras, which are special biserial by a theorem of Skowroński and
Waschbüsch.

Special biserial is essential: brick accessibility fails in general. The
Kronecker algebra has no brick of dimension 4, and the paper gives a
brick-finite algebra with the same gap.

## Start reading

- [Main theorems](BrickAccessibility/MainTheorems.lean): `theoremA`,
  `corollaryB` and `corollaryBiserial`, with `isSpecialBiserial_of_biserial`
  (Skowroński–Waschbüsch).
- [Independent statement](BrickAccessibility/Statement.lean): the three results
  stated with Mathlib alone. The [Challenge](Challenge.lean) is generated from
  it, and [Solution](Solution.lean) proves it.
- [Paper correspondence](docs/PAPER-CORRESPONDENCE.md): every numbered
  statement of the manuscript with its Lean declarations.

All definitions and proofs are complete. The main statements depend only on
the axioms `propext`, `Classical.choice` and `Quot.sound`. The inputs the paper
cites are proved in the library: the string and band classification of
Butler–Ringel (Theorem 4.5, for bands of every rank), the string quotient of
Wald–Waschbüsch (Lemma 5.3), and the Skowroński–Waschbüsch theorem that
representation-finite biserial algebras are special biserial.

## Coverage

Theorem A, Corollary B, Corollary 5.6 and every numbered proposition, lemma,
theorem, corollary and remark of the manuscript are proved, and its numbered
definitions and constructions are formalized. Not formalized: the genericity
sentences of Remark 2.2, the four numbered examples and the two questions.
Remark 5.7 cites the closure of special biserial algebras under quotients; this
is proved in the path-data form that the argument uses. Some statements are
proved in an equivalent or more general form, and some proofs take a different
route; the [correspondence](docs/PAPER-CORRESPONDENCE.md) records these.

Conventions: modules are right modules, formalized as modules over the opposite
algebra. Paths are multiplied in traversal order, as in the paper. The field
`k`, the algebra `Λ` and the modules live in one universe. `Ext¹` is modelled
by derivations modulo inner derivations.

## Build and verify

Lean is pinned to `v4.35.0-rc3` and Mathlib to its `v4.35.0-rc3` tag, commit
`c55e6e786f49471c72fbddbec5415808896aec1e`, the only external dependency.
Every Lean file uses the Lean module system.

```sh
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
```

or, with memory and timing records for each step,

```sh
python3 scripts/build_lean_serial.py --package . --output .build-audit/full \
  --max-rss-kib 12582912 BrickAccessibility
python3 scripts/audit_axioms.py
```

The statement check uses the `lake comparator` shipped with the toolchain,
with the Lean kernel and the bundled NanoDa and con-ron checkers. It needs
`bwrap` (bubblewrap) on the path:

```sh
python3 scripts/check-lean-sources.py
./scripts/verify-comparator.sh
```

[docs/VERIFICATION.md](docs/VERIFICATION.md) describes the checks, and the
records are in [verification](verification/).

## Palomar

The repository follows the layout of the
[Palomar registry](https://palomar-registry.org): the statement of record is
[Challenge.lean](Challenge.lean), proved in [Solution.lean](Solution.lean),
with [comparator.json](comparator.json) and the metadata in
[formalization.yaml](formalization.yaml). The workflow
[Palomar preflight](.github/workflows/palomar-preflight.yml) runs Palomar's
mechanical verification for a chosen commit.

## Website

The [website sources](website/README.md) present the theorems, the independent
statement, a proof guide and the searchable Lean API.

## Provenance

See [PROVENANCE.md](PROVENANCE.md) for the source of the Lean files, the
formalized manuscript and contributions. No source is vendored from other
projects ([VENDORED.md](VENDORED.md)). Licensed under the
[Apache License 2.0](LICENSE).
