# Wrong Book 3000

An open challenge and regression dataset with **2,983 frozen problems**. The
historical name is retained; the file does not contain exactly 3,000 rows.

- [`wrong-book-3000.jsonl`](wrong-book-3000.jsonl): five-field publication data.
- [`manifest.json`](manifest.json): size, SHA-256, and reconciled recorded counts.
- [`../../results/verdicts.jsonl`](../../results/verdicts.jsonl): separate current ledger.
- [`../../provenance/raw/wrong-book-3000.jsonl`](../../provenance/raw/wrong-book-3000.jsonl):
  the original byte-preserved data, including historical labels and metadata.
- [`../../provenance/problem-ids.jsonl`](../../provenance/problem-ids.jsonl): original
  IDs mapped to public directed-pair IDs.

Each publication row contains only `id`, `eq1_id`, `eq2_id`, `equation1`, and
`equation2`. Public IDs use `<eq1_id>_to_<eq2_id>`; membership and order are frozen.

Available proofs use one [`../../proofs/`](../../proofs/) file per problem,
`<eq1_id>_to_<eq2_id>.lean`, with problem definitions and project helpers embedded.
[`../../evidence/certificates.jsonl`](../../evidence/certificates.jsonl) records
source selection, hashes and remaining standard library imports. Original Lean
sources and alternative proofs are retained in the provenance archive.

The first 2,500 rows come from Wrong Book 2500. The extensions contain 194 and 289
problems, respectively. After membership was frozen, subsequent solutions were
recorded without deleting problems or changing their original labels.

Recorded counts: **1,484 true, 1,290 false, 209 unknown**. “Unknown” means no verdict
in the imported evidence. These are source-record counts, not a new proof audit.

All **2,774** problems with a recorded verdict now have a public certificate and
submission source. The 159-source augmentation consists of 147 certificates
recovered from two archived d12 final-result ledgers, five source-05 certificates,
and seven certificates from the fixed upstream commit recorded in provenance.
The recovery manifests under [`../../provenance/recoveries/`](../../provenance/recoveries/)
bind every row to its source and Lean SHA-256. Package reconstruction and integrity
checks have passed. The current Aurora Cloud Judge-v3-repl audit binds each
published certificate to an exact accepted submission and reports **2,774/2,774
accepted** (1,484 true and 1,290 false); see
[`../../results/judge-v3-aurora-wrong-book-3000-final-accepted-20260907/audit.json`](../../results/judge-v3-aurora-wrong-book-3000-final-accepted-20260907/audit.json).

The original README's later total and the original manifest's earlier total
refer to different stages. This repository reconciles the per-problem evidence
and provides a separate ledger. Historical labels are retained in the raw archive,
not copied into the publication rows.

The archived original file SHA-256 is:

```text
28ea0fa0d283f1d116522d722cd0dbb1c7035cfad81ebc5581342fab311ab570
```

The publication file's SHA-256 is recorded in [`manifest.json`](manifest.json).

See [curation](../../docs/curation.md), [format](../../docs/data-format.md), and
[verification](../../docs/verification.md) for details and limitations.
