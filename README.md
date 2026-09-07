# Equational Challenges

[English](README.md) · [Simplified Chinese](README.zh-CN.md)

A collection of difficult equational reasoning problems and their Lean proofs,
built during solver development. Failed attempts exposed gaps in proof search,
countermodel construction and proof generation, driving successive solver
iterations. Solutions found offline are collected in [`proofs/`](proofs/);
solved problems remain in the collection as regression tests.

Each problem asks whether one identity implies another in every **magma**
(a set with a binary operation). `true` requires an implication proof;
`false` requires a countermodel. The implication direction matters.

## Current results

<!-- results:start -->
Offline solutions archived as of **2026-09-07**:

| Collection | Problems | true | false | Solved / with proof | Remaining |
| --- | ---: | ---: | ---: | ---: | ---: |
| [Wrong Book 3000](datasets/wrong-book-3000/README.md) | 2,983 | 1,484 | 1,290 | **2,774** | 209 |
| [Wrong Book 3500](datasets/wrong-book-3500/README.md) | 3,500 | 1,674 | 1,303 | **2,977** | 523 |
<!-- results:end -->

The collections share an identical 2,500-row prefix. Their extensions are
disjoint: **3,983 unique directed problems**, with **3,337 distinct solutions**.
Do not add the two solved counts. The 1,000-problem 3500 extension now has 563 solutions and 437 remaining; “remaining” does not claim mathematical open status.

Every solved problem has one public Lean file. All 3,337 selected submission
sources have recorded Judge-v3-repl acceptance. The 563 new solutions from
`wrongbook3500_hits_20260816` include 22 compatibility repairs accepted after
reverification; their final standalone files were also compiled individually
with Lean 4.33.1 and checked for allowed axiom dependencies. The existing 2,774
files were preserved; this update does not claim a fresh compilation of all of
them. Detailed source, compiler and Judge records remain local. See the
[Lean verification instructions](docs/verification.md).

## How Wrong Book 3000 and 3500 were built

Both collections extend **Wrong Book 2500** independently. “3000” is a historical
name: the frozen collection actually contains 2,983 problems.

1. **Baseline → Candidate 2000.** From a catalogue of 62,576 equations, structural
   clusters guided sampling after simple proof and small-countermodel filters.
   A 10,120-problem baseline contained 10,000 residual and 120 calibration cases.
   Candidate 2000 retained 1,880 residual cases (including 120 difficult-case
   places) plus all 120 calibration cases.
2. **Candidate 2118 → Wrong Book 2500.** Add 118 capability probes, then 382
   representative failures of a fixed `v97` solver. The added members were
   repaired and frozen after retesting. The inherited prefix includes many
   already solved problems, preserving coverage of existing capabilities.
3. **Wrong Book 3000 = 2,500 + 194 + 289 = 2,983.** Two earlier candidate batches
   were filtered through successive proof-search and false-solver runs, retaining
   194 and 289 cases. Nine retained cases had resource-limit outcomes.
4. **Wrong Book 3500 = 2,500 + 621 + 379 = 3,500.** Retain 621 of 642 historical
   candidates after screening. Of 5,120 new candidates evaluated, proof search
   removed 4,427 and the false solver removed 297; remove 15 overlapping
   clusters, then select 379 of the remaining 381 for structural diversity.

“Wrong book” describes failures under particular solver versions and budgets,
including documented execution/resource exceptions. It is not a truth label or
an unbiased difficulty ranking. Membership and order stay frozen when later
solver iterations solve a problem. The [curation record](docs/curation.md)
preserves screening details, seeds and solver fingerprints.

## Quick start

The problem files are plain JSONL. Each proof is named by its directed pair:

```text
datasets/wrong-book-3000/wrong-book-3000.jsonl
proofs/34_to_50568.lean
```

Read a proof directly, or compile it from this repository after installing the
pinned Lean toolchain:

```sh
lean -j 1 -M 512 proofs/34_to_50568.lean
```

The repository includes its own Lean/Lake configuration: **Lean 4.33.1**, with
[Mathlib pinned to `0df444a360ea`](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474).
Proofs needing Mathlib require the [one-time setup](docs/verification.md#lean-environment).
No separate research checkout, solver, private path or remote Judge is needed.
Toolchain and library installation initially requires network access; subsequent
compilation can run offline. Individual proofs can require more memory than the
small example; see the verification instructions for resource limits.

## Repository contents

| Path | Contents |
| --- | --- |
| [`datasets/`](datasets/) | Two frozen five-field JSONL problem sets and manifests |
| [`proofs/`](proofs/) | One final Lean certificate per solved directed problem |
| [`docs/`](docs/) | Curation, data format and verification details |

See [data format](docs/data-format.md) for field definitions and joins.

## Attribution, license and contributions

This project's contributions to the Lean certificate code in `proofs/` are
licensed under [Apache-2.0](LICENSE). Third-party portions retain their applicable
licenses and notices. See [NOTICE](NOTICE.md) for the license scope and attribution.
The datasets and documentation are not covered by this certificate-code license;
their licensing remains to be determined.

To contribute a proof, countermodel or correction, include the directed problem
ID, Lean source, toolchain versions and validation result. Preserve frozen
membership and include source attribution for any contributed material.
If these public problems or proofs informed solver development or training,
disclose that use when reporting evaluation results.
