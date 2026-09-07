# Sources, attribution and license scope

## Apache-2.0 for certificate code

This project's contributions to the Lean certificate source files under
`proofs/` are licensed under the Apache License, Version 2.0
(`Apache-2.0`). The complete license text is in [LICENSE](LICENSE).

This grant covers rights held by the project contributors or that they are
authorized to license. Third-party portions retain their existing licenses,
copyright and attribution notices; this declaration does not relicense material
for which the project lacks permission. Retain applicable upstream notices when
redistributing the certificates and identify modifications as required by the
license.

This license selection is specific to certificate code. It does not grant a
license for the datasets, documentation or other files in this repository;
their licensing scope remains to be determined.

## Sources and attribution

The challenge collections and proof evidence were assembled during YanbiaoLab's
equational-reasoning solver research. Historical records credit Jiaming,
solver work identified as ZplusM, and other team and upstream contributors.
These are source-record attributions, not a finalized author list or an assertion
of priority. Final names, ordering and preferred credits remain to be confirmed.

The historical research used these upstream projects:

- [Equational Theories Project](https://github.com/teorth/equational_theories)
- [SAIR Stage 2 Lean environment](https://github.com/SAIRcompetition/equational-theories-lean-stage2)

Both upstream projects publish Apache-2.0 license notices:

- Equational Theories Project: Copyright 2025 Contributors of the Equational
  Theories Project. See its [license](https://github.com/teorth/equational_theories/blob/main/LICENSE).
- SAIR Stage 2: Copyright 2026 SAIR Foundation. See its
  [license](https://github.com/SAIRcompetition/equational-theories-lean-stage2/blob/main/LICENSE).

The pinned Mathlib dependency is also distributed under
[Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/LICENSE).
These upstream notices identify their respective material and do not imply
endorsement of this project.

Upstream material is not claimed as original work of this repository. Public
certificate headers identify the directed problem, recorded verdict and source
submission hash; embedded helper sections identify their original modules.
Detailed import and validation records are retained by the maintainers locally
and are not part of the public package. Source hashes are identifiers, not a
replacement for attribution or permission.

## Wrong Book 3500 addition (2026-09-07)

The 563 additional directed-pair solutions were selected from the
`wrongbook3500_hits_20260816` export supplied by Jiaming. Its historical runs
identify v48, d17_fixed, cyclic_skew_search and presburger_affine_search among
the solvers producing these additions. Original submissions and historical
Judge metadata are retained locally. Twenty-two submissions received
compatibility repairs and fresh Judge acceptance. Public files embed project
helpers and use narrowed imports where independently validated by Lean.
The license and attribution scope above continues to apply.
