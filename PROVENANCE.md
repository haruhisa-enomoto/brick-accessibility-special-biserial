# Provenance

The Lean development is maintained by Haruhisa Enomoto. It formalizes the
unpublished manuscript *Brick accessibility for brick-finite special biserial
algebras*, revision of October 18, 2026, as frozen at commit
`62a219c8e4fdba2484fe6c84c52e06e814f100fa` of the private research repository
`homological-conjectures` (the TeX source last changed at `3fdea5c50`). The
manuscript is not distributed here; [docs/MANUSCRIPT.md](docs/MANUSCRIPT.md)
identifies the revision by hash. The
[correspondence](docs/PAPER-CORRESPONDENCE.md) describes formal coverage.

The Lean sources originate in `formalization/brick_accessibility` of the same
research repository, at commit `e743cf372b65dcb078567c29a84b3e86b8252986`. The
[source manifest](verification/2026-10-29/source-sync.json) records the hash of
every file before and after the port described below.

## Contributions

The manuscript names OpenAI Codex (GPT-6) as its author. It was written under
Haruhisa Enomoto's direction. The formalization was developed with AI coding
agents under Haruhisa Enomoto's direction, mainly with Claude Opus 5.5 and
GPT-6. A complete model-by-model history of the development has not been
reconstructed.

## Dependencies and licences

The proof package pins Lean 4.35.0-rc3 and Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`). Mathlib is the
only external Lake dependency. The research package pinned Lean 4.33.1 and
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; the move to the newer
toolchain and to the Lean module system changed proofs only, not statements.
No source is vendored ([VENDORED.md](VENDORED.md)). This repository is released
under the [Apache License 2.0](LICENSE).
