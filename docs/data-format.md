# Published data format

Problem files are UTF-8 JSONL, one JSON object per line. Each row has exactly
five fields:

| Field | Meaning |
| --- | --- |
| `id` | Directed pair `<eq1_id>_to_<eq2_id>` |
| `eq1_id`, `eq2_id` | Ordered premise and conclusion equation IDs |
| `equation1`, `equation2` | Formulas, including significant parentheses |

Each equation is a universally quantified magma identity. The binary operation
is written `*` in the data and usually `◇` in Lean. Reversing a pair changes the
problem. Parentheses must be preserved.

The two collections have frozen membership and row order. They share an
identical 2,500-row prefix; their extensions are disjoint. Join by directed `id`
and count shared problems only once: there are 3,983 unique problems in total.

## Proofs and verdicts

A solved problem has one file at `proofs/<id>.lean`. For example,
[`34_to_50568.lean`](../proofs/34_to_50568.lean) is the certificate for
Equation34 → Equation50568.

The certificate header records:

- the directed equation IDs and both formulas;
- `Recorded verdict: true` for an implication proof, or `false` for a countermodel;
- the source submission hash and, where applicable, the correction hash.

The public file contains its own problem definitions and the explicit final
`certificate_<id>` theorem. A source hash in its header identifies the input
submission; it is not the hash of the expanded public file. See
[verification](verification.md) for compiling and interpreting a certificate.

A missing proof means no solution is included in this package for that problem.
It does not assert that the problem is mathematically open. Problem rows contain
no verdict labels; readers can associate the published proofs using their IDs.

## Dataset manifests

Each dataset's `manifest.json` contains:

| Field | Meaning |
| --- | --- |
| `name`, `file`, `rows` | Dataset identity, JSONL filename and row count |
| `sha256`, `size_bytes` | Hash and size of the published JSONL bytes |
| `frozen_membership` | Whether membership/order are frozen |
| `as_of` | Date of the reported solution snapshot |
| `recorded_verdict_counts` | Published true/false solution counts and unknown count |
| `accepted_submission_sources` | Maintainer-reported historical Judge acceptances for selected sources |
| `proof_path_template` | Relative path pattern for a problem's final certificate |
| `verification_scope` | Scope of the historical acceptance statement |

Detailed construction and validation records are maintained locally; the public
package does not include the maintenance ledgers or require them to read the
problems and compile the certificates. See [curation](curation.md) for the
historical selection narrative and [NOTICE](../NOTICE.md) for attribution.
