# Dataset construction

This document describes the historical selection process behind the published
challenge sets. Counts, screening outcomes, seeds and solver fingerprints below
are transcribed from the maintainers' research records. The complete candidate
pools, original selection records, execution logs and solver implementations are
not distributed here; this narrative does not provide a replay of discovery.

The [English overview](../README.md#how-wrong-book-3000-and-3500-were-built) and
[Chinese overview](../README.zh-CN.md) summarize the construction.
Published rows contain the directed-pair ID, both equation IDs and both formulas.
Their membership and order are frozen. Public dataset manifests record the
published file hashes; later solutions do not change which problems are included.

## Shared prefix and historical terminology

The initial catalogue had 62,576 equations. Source/target groups based on
expression shape and syntax formed directed-pair clusters. After excluding
four families covered by simple proofs or small countermodels, a stratified
sample of 10,000 residual pairs plus 120 calibration problems formed the
10,120-problem baseline. "Residual" describes those filters, not a claim that
the mathematics was unsolved.

Candidate 2000 was a smaller evaluation proxy for the 10,120-problem baseline.
It selected 1,880 residual problems: 120 difficult-case places and 1,760 ordinary
distribution places. Both the overall residual quota and the difficult-case
quota were apportioned by the baseline's sample counts in six rank bands using
the largest-remainder method. The final residual band counts were
940 / 226 / 226 / 254 / 131 / 103.

Difficult cases were selected first within each band, aiming for half earlier
non-passes and half accepted cases requiring at least 20 Judge calls or
300 seconds. A shortage in either group was filled from the same band's
remaining difficult candidates. Priority was descending
`judge_calls + elapsed_seconds / 60`, then ascending `sample_index`.
The remaining places were filled without replacement using seed `20260703`:
a SHA-256 of seed, band-specific sampling role and problem ID determined `u`,
and rows were ranked by ascending `-log(u) / evaluation_weight`, with
`sample_index` breaking ties. The fixed inputs and seed made this deterministic.

All 120 calibration problems were retained in addition to the 1,880 residual
problems. Their four families each contained 30 cases, for 90 historically
labeled true and 30 false. Each family also contained internal easy/medium/hard
subgroups; "easy calibration" identifies the family set, not a claim that every
row has the lowest difficulty tag. Calibration results should be separated
from weighted residual acceptance. These composition counts, roles and the seed
come from the original selection metadata retained by the maintainers.

Candidate 2118 added 70
`seedbank_v27` and 48 `specialization_v6` capability probes. The probes selected
one source from each family/shape/syntax/variable-count group and a target by
fixed hash, excluding self-pairs and duplicate Candidate 2000 pairs. These
historical family names identify coverage experiments, not required libraries.

## Wrong Book 2500

The 2,118 inherited rows and the `v97` solver were held fixed while 382
representative failures were collected and repaired. The solver SHA-256 was
`b48147f11410346dd64d8da97f49016db1ae6711f953e4b3b67cca09fa450e97`.
Here A means a Judge-accepted proof or countermodel; R means that the solver
executed, called the Judge and completed clean search exhaustion without an
accepted result. E covers execution/validation failures and incomplete runs.
These are run classifications; R does not mean the implication is false.

The new candidate pool was derived from 618,523 frozen example occurrences in
213,759 historical unresolved clusters, representing 129,475,508 directed pairs.
Each cluster had at most three example pairs. After excluding covered sources,
targets, pairs and exact clusters, then deduplicating within the pool, 3,599
candidates remained. Sources and targets were each unique within that pool.

The pre-screening priority was
`(0.5 + 0.5 H) * (0.50 C + 0.30 V1 + 0.20 V2)`, using empirical midrank
percentiles of historical unresolved frequency (`H`), residual cluster size
(`C`), and remaining structural coverage under FV1 and FV2 (`V1`, `V2`). FV1
uses shape and syntax; FV2 adds finer tree structure. Historical frequency was
only a ranking prior. The residual cluster weight came from the residual ledger,
not from the historical unresolved count. Ties used descending residual cluster
size, FV1 remaining weight, FV2 remaining weight and historical count, followed
by ascending stable candidate ID.

Full solver evaluation was attempted for 1,327 distinct problems, including
earlier exploratory results and runs ending in E. Static-only inspection and
infrastructure retries were not additional full solver attempts:

| Stage | Sent to full solver | A | R | E | Initially selected R |
| --- | ---: | ---: | ---: | ---: | ---: |
| Earlier exploration | 33 | 0 | 33 | 0 | 26 |
| Static pre-screening (976 inspected) | 121 | 10 | 110 | 1 | 110 |
| Direct full evaluation | 1,173 | 911 | 258 | 4 | 246 |
| Total | 1,327 | 921 | 401 | 5 | 382 |

The initial 382 R accumulated across 23 immutable batches; 7 low-frequency R
were kept separately and 12 surplus R exceeded the remaining capacity.
IDs, directed pairs and normalized formulas were deduplicated across evaluated
and pending records.

The first full evaluation, after infrastructure retries, classified the added
382 rows as 4 A / 374 R / 4 E. The 4 accepted cases and 4 cases with
non-retryable execution errors were removed. The first 8 of the final batch's
12 surplus R, in frozen order,
replaced them: 374 + 8 = 382, with 4 surplus cases unused. The 2,118-row prefix
remained unchanged, and the repaired 2,500 IDs, pairs and normalized inputs
were globally unique.

The repaired collection's full run used the same `v97`, 64 workers and a
900-second solver timeout. The inherited prefix gave 2,019 A / 99 R / 0 E;
the extension gave 5 A / 376 R / 1 E, totaling 2,024 A / 475 R / 1 E.
The 5 accepted extension cases were 4 true and 1 false, despite unchanged input
bytes and solver hash; the audit did not establish the cause of this change.
The remaining E timed out without completing clean search exhaustion. Its
initial runner classification as R was corrected, and the error was explicitly
retained when the repaired membership was frozen. These outcomes do not update
the published solution counts by themselves.

The resulting 2,500 rows form the identical prefix of both published collections.
The historical selection categories are described above; the public problem
rows contain only the five mathematical problem fields.

## Wrong Book 3000

The frozen construction is 2,500 + 194 + 289 = 2,983 problems. The extension
selection involved earlier search/false-solver runs followed by `v31-cpu` and
`d8` checks. First, `v30` and `d2` left 261 candidates; a single-core `v31`
run removed one accepted true result. The 260 retained candidates were rechecked:
10 true results and 56 false results were removed, leaving 194. For the second,
548 earlier residual candidates were reduced by 40 false results, then 191 true
results, then 28 further true results, leaving 289.

The final 289 included 9 cases described as `resource_limit_unresolved`, not
logical negative results. Later evidence updates do not change frozen membership.
Historical records describe 300-second search budgets in relevant screening
stages; configurations and concurrency differed across stages. Do not treat that
as one uniform benchmark run across all 2,983 problems.

## Wrong Book 3500

The shared 2,500 prefix is extended with 621 historical and 379 new candidates.
For the historical 642, the screening records report `v31-cpu` accepted 21 true results and
`d8` found no additional accepted result, leaving 621.

For the new cluster-proxy pool, 8,192 candidates were prepared and the first 5,120
screened. Search accepted 4,427 true results, leaving 693; the false solver
accepted 297, leaving 396. Removing 15 cluster overlaps left 381; deterministic
diversity selection retained 379. The remaining 3,072 reserve candidates were
not screened. These are source-reported screening counts, not runs performed here.

The "129M" pool used frozen example pairs from an older cluster ledger covering
129,475,508 directed pairs. It was a structural coverage proxy; it did not sample
uniformly over every pair and did not establish exact membership in a separate,
unavailable 115,557,502-row residual CSV. Existing challenge pairs and earlier
expansion pools were excluded before screening.

The final 379 were selected across four roles, redistributing unavailable quota:

| Sampling role | Requested | Eligible | Selected |
| --- | ---: | ---: | ---: |
| Coverage weighted by square root of cluster size (`coverage_sqrt_mass`) | 189 | 180 | 180 |
| Uniform cluster coverage (`cluster_uniform`) | 95 | 61 | 61 |
| Less-represented structures (`novel_long_tail`) | 57 | 87 | 86 |
| Historical pair-count control (`legacy_pairmass_control`) | 38 | 53 | 52 |
| Total | 379 | 381 | 379 |

Selection favored fewer repeated source/target equations, then stable SHA-256
tie-breaking. The 1,000-row extension contains 1,000 distinct clusters; a source
equation occurs at most 14 times and a target at most 4 times.
For the new pool, `v31-cpu` used a 300-second internal budget, 330-second outer
timeout and up to 150 concurrent tasks; `d8` used a 360-second outer timeout and
up to 100 concurrent tasks. One historical candidate was retained after the
cloud connection ended following 300.601 seconds, with no Judge request sent;
its original protocol-error record was preserved.

Source solver identities:

| Solver | SHA-256 |
| --- | --- |
| `v31-cpu` | `557ba17d2141c81b41e5ce06180f95c8bfa8c38dbbbe7b967f5ac7485683b9ae` |
| `d8` | `fd9c906ffa7be6f840af90556cacf66f3f670582d6e76fb80af833c51b7873ab` |

The selection seed is `wrongbook3500-new379-diversified-v1`; that is a historical
experiment identifier, not a release version of this repository.
The complete discovery pools, solver implementations and run environments are
not distributed, so a full replay of discovery is outside this data package.
The public package contains the frozen problems and final standalone proof files.
See [verification](verification.md) for checking an individual proof and
[NOTICE](../NOTICE.md) for source attribution.
