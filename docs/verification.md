# Checking the published proofs

[English overview](../README.md) · [Chinese overview](../README.zh-CN.md)

## Published scope

The public repository contains the frozen problem sets, one standalone Lean
certificate per solved directed problem, construction notes and a pinned Lean
environment. Each certificate embeds its magma definitions, premise, conclusion,
goal and required project helpers. Reading a proof needs no other project.

As of 2026-09-08, all **3,412 selected submission sources** have recorded
Judge-v3-repl acceptance: **1,754 true and 1,658 false**. Of these, 3,051 belong
to Wrong Book 3500. Detailed validation records remain local.

The latest update adds 75 certificates from `solo_v9.py`: 2 implication proofs
and 73 countermodels. Their original requests, accepted responses, control job
IDs and source hashes were archived during the completed cloud run. Each
request is bound to the frozen directed problem, its explicit proof policy and
the exact submitted source. Acceptance of that source is distinct from
compilation of the expanded standalone file.

On 2026-09-08, all 75 passed a fresh Aurora Judge-v3-repl replay with
caching disabled, a 1,800-second verification timeout and up to 35 concurrent
jobs. The adapter checked each current public file hash and proof-body
boundary, then submitted its exact original source with the frozen directed
problem. Every new job ID, request, result, adapter binding and previous
acceptance record is retained locally. Judge supplies the trusted problem
and helper modules, so this was an adapted-source replay rather than a
verbatim submission of the expanded standalone file. The separate local
Lean checks cover those exact standalone bytes; all 75 hashes stayed unchanged.

All 75 new standalone files were compiled individually with Lean 4.33.1 and
the pinned Mathlib revision, in an isolated directory without Judge modules in
`LEAN_PATH`. Each check verified the exact final file hash, the explicit
`certificate_<id>` theorem and its allowed axiom dependencies. Imports were
narrowed where needed while preserving accepted proof bodies. Compilation was
serial, with explicit Lean memory and process-RSS limits and system-pressure
monitoring. Of these 75 files, 74 passed with Lean budgets at or below 2 GiB;
`2531_to_1313` required a 4 GiB budget and passed below its 4 GiB process-RSS
stop threshold (observed peak: 4,017.06 MiB). Exact per-file limits and compiler
logs are retained locally.

The previous 563 additions from `wrongbook3500_hits_20260816` also retain their
successful standalone compilation records, including 22 compatibility repairs
with fresh Judge acceptance. Together with the previously compiled example,
**639 current standalone files** have exact-file compilation records.
The existing 3,337 public files were unchanged in this update and were not all
freshly compiled.

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
