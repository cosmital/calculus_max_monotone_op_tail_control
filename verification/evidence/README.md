# Verification receipts

The current package status is in `../../docs/CODEX_PROGRESS.md`.

- `release-2026-11-09.json` and the corresponding output files record the current six-command build/audit/reader gate, source hashes, and author-approved coverage. All commands and the release gate exited 0.
- `tooling-tests-2026-11-09-output.txt` records 33 successful tooling tests. The additional source-collection regression receipt checks that generated exports are excluded while legitimate nested project sources remain guarded.
- `package-checks-2026-11-09.json` records final metadata and correspondence checks. `pdf-reconciliation-2026-11-09.json` records the PDF/source reconciliation and all 62 numbered headings.
- `fresh-2026-11-08-*` are historical receipts for the complete fresh mathematical rebuild. All six Lean commands passed then; release exit 2 recorded the author review that was still ungranted on that date. Old console wording in those unmodified logs is historical, not a current missing-proof status.

Compiler receipts are preserved without rewriting their output. Author correspondence acceptance is recorded separately in `../../docs/AUTHOR_REVIEW.json`.
