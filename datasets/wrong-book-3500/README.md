# Wrong Book 3500

An open challenge and regression dataset with **3,500 frozen problems**.

- [`wrong-book-3500.jsonl`](wrong-book-3500.jsonl): five-field publication data.
- [`manifest.json`](manifest.json): size, SHA-256, and reconciled recorded counts.
- [`../../results/verdicts.jsonl`](../../results/verdicts.jsonl): separate current ledger.
- [`../../provenance/raw/wrong-book-3500.jsonl`](../../provenance/raw/wrong-book-3500.jsonl):
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

Composition: the byte-identical Wrong Book 2500 prefix (2,500), 621 retained
historical candidates, and 379 newly selected candidates. The 1,000 additional
problems do not occur in Wrong Book 3000 by directed equation pair.

Recorded counts after applying evidence for shared problems: **1,406 true,
1,008 false, 1,086 unknown**. Of the unknowns, 86 are in the shared prefix and
1,000 are in the extension. This import includes no later verdict evidence for
the extension; it does not assert that all 1,000 remain mathematically open.

The latest [Aurora Cloud Judge-v3-repl acceptance audit](../../results/judge-v3-aurora-wrong-book-3000-final-accepted-20260907/README.md)
reconciles 2,774 accepted certificates for Wrong Book 3000, including all
**2,414 source-backed certificates** shared with this collection. It matches the
current certificate and submitted-source hashes to saved cloud acceptances;
the final reconciliation itself did not submit new cloud jobs. All recorded
verdicts in this collection now have certificate source. The remaining 1,086
problems have no imported verdict, so this does not claim that all 3,500 problem
rows have certificates or were verified.

The earlier [2,412-certificate audit](../../results/judge-v3-aurora/README.md)
is retained as historical evidence and does not describe current coverage.

Selection-stage failure means that the fixed `v31-cpu` and `d8` configurations did
not produce an accepted submission under their screening budgets. It is not a
truth label. See [curation notes](../../docs/curation.md) for the screening funnel.

The archived original file SHA-256 is:

```text
25fe4492091c6f76de1a46a1ce7a32e2f931ffe3fdbecc6af2adcb3127e0c468
```

The publication file's SHA-256 is recorded in [`manifest.json`](manifest.json).
