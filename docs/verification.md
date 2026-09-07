# Checking the published proofs

[English overview](../README.md) · [Chinese overview](../README.zh-CN.md)

## Published scope

The public repository contains the frozen problem sets, one standalone Lean
certificate per solved directed problem, construction notes and a pinned Lean
environment. Each certificate embeds its magma definitions, premise, conclusion,
goal and required project helpers. Reading a proof needs no other project.

As of 2026-09-07, the maintainers report 2,774 selected submission sources
accepted by Judge-v3-repl: 1,484 true and 1,290 false. Of these, 2,414 also belong
to Wrong Book 3500. Detailed requests, responses, original submissions and
maintenance tools remain local and are not included in the public repository.

The expanded public files have different hashes from their submission sources.
The historical acceptance count therefore describes the selected sources in the
Judge's problem context; it is not a report of fresh compilation of all expanded
files. Readers can independently compile the public files using the steps below.

## Lean environment

The repository's `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` pin
Lean 4.33.1, Mathlib and its transitive dependencies. The Mathlib commit's
[own toolchain file](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/lean-toolchain)
confirms the Lean version. No project-specific Lean modules remain as imports in
the final certificates; their required definitions are embedded.

With [elan](https://github.com/leanprover/elan) installed, install the compiler:

```sh
elan toolchain install leanprover/lean4:v4.33.1
```

From this repository's root, compile a small certificate without Mathlib:

```sh
lean -j 1 -M 512 proofs/34_to_50568.lean
```

A maintainer's earlier check of this example succeeded with this memory budget
and about 400 MiB peak child RSS. The budget is not a guarantee of total process
memory, and larger proofs may need more. A later 128 MiB attempt hit the memory
limit; a memory failure does not refute the mathematical statement.

For proofs importing Mathlib, perform this one-time setup in this repository:

```sh
lake exe cache get
```

Lake obtains libraries at the revisions in the lockfile. Installation can use
several GB of disk and significant memory. Once installation has completed,
compile a proof using that environment:

```sh
lake env lean -j 1 -M 512 proofs/10205_to_10541.lean
```

The `-j 1` option limits compiler workers and `-M 512` sets Lean's memory budget
in MiB. Compile one proof at a time and monitor resource use. These direct
commands do not impose a wall-clock timeout. Initial toolchain/library downloads
need network access; compilation can run offline once dependencies are installed.

## Interpreting a check

The file ends with an explicit theorem named `certificate_<eq1_id>_to_<eq2_id>`
and a `#print axioms` command. Check that:

- the premise and conclusion agree with the published directed problem;
- Lean exits successfully and the theorem states the required implication or
  existential countermodel;
- the printed axiom dependencies are appropriate, without `sorryAx` or an
  unproved assumption of the target statement.

An exit code alone is not a substitute for checking the theorem and its axioms.
A timeout or resource failure gives no mathematical verdict. Local compilation
and historical Judge acceptance have distinct scopes.
