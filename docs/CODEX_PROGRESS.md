# Final manuscript synchronization — 12 November 2026

The final submission PDF replaces the earlier snapshot. All 62 numbered statements and 56 supplemental excerpts were compared with the accepted version; mathematical claims and exact Lean sources are unchanged. The dictionary, equation references, all PDF page links, source inventory, PDF hash, and author-review location bindings are synchronized. See [MANUSCRIPT_SYNC.json](MANUSCRIPT_SYNC.json) for the audit and [MANUSCRIPT_VERSION.json](MANUSCRIPT_VERSION.json) for hashes. Historical evidence below remains dated and does not certify a new compiler run.

Current standalone checks: metadata and recorded correspondence passed; all 33 Python tests completed successfully (32 passed, one Windows-specific test skipped on Linux). All 118 PDF links and 2,382 Lean declaration links were checked. Dated output is preserved under `verification/evidence/`. The exact Lean sources match the accepted source hashes. This PDF synchronization does not itself assert a new compiler success.

# Current verification and submission package — 9 November 2026

The final article PDF and PDF-numbered reader dictionary are ready in this package. All 62 numbered and 56 supplemental claims have complete proof mappings and author-directed correspondence acceptance. The record of that instruction is `AUTHOR_REVIEW.json`.

- 335 mathematical modules; 2480 indexed public declarations.
- The author's current manuscript revisions are retained. The only additional article edit is n ≥ 1 in Example 2.5, visible on PDF page 25.
- All 62 numbered headings were checked against the rebuilt 45-page PDF. Equation locations use the new AUX labels; unnumbered locations use SyncTeX.
- Final PDF SHA-256: `84c1f27956d69c9ae457d4c5a98a40514f9af8fd1fb635c1bda7f96d4eafeb51`.
- Current metadata and author-approved coverage checks: PASS, exit 0.
- `python tools/verify.py --release`: PASS, exit 0; all six Lean build/audit/reader commands exited 0.
- `python -m unittest discover -s tests -v`: 33 tests passed, exit 0 (286.993 s).
- The final source-collection regression also passed after excluding generated `dist/` exports from the own-source guard; legitimate nested project sources remain included.

Actual receipts are in [verification/evidence](../verification/evidence): `release-2026-11-09.json`, `release-2026-11-09-output.txt`, `tooling-tests-2026-11-09-output.txt`, and `package-checks-2026-11-09.json`.

The six Lean commands are:

```text
lake env lean --version
lake build MonotoneOperators EndOfPaper Paper
lake env lean EndSmokeTests.lean
lake env lean AxiomAudit.lean
lake env lean AxiomAuditEnd.lean
lake env lean PaperChecks.lean
```

Both audits retain only `propext`, `Classical.choice`, and `Quot.sound`. No mathematical Lean proof was added or changed in this preparation. Obsolete development-status comments in the Lean readers and one audit console message were corrected; audit logic and expected types are unchanged. The comment in `ChainMetricAlgebra.lean` was rebuilt with its dependents. Routine supporting proofs remain outside the main reader table.

The complete fresh own-module rebuild from 8 November is preserved as historical compiler evidence. It passed all six Lean commands and returned release exit 2 because author acceptance had not yet been recorded. The 9 November incremental release gate above records the subsequent accepted state; no new full fresh rebuild is claimed.

The public manuscript is [the PDF](../manuscript/monotone_calculus.pdf). [RESULT_DICTIONARY.md](RESULT_DICTIONARY.md) uses printed PDF numbering and short descriptions; [PROOF_DETAILS.md](PROOF_DETAILS.md) keeps the full Lean mappings. Private TeX, bibliography files and development archives stay local and are excluded from Git and `tools/export_release.py`. The public metadata and coverage gates work without TeX.

The pinned environment remains Lean 4.19.0, Lake 5.0.0-6caaee8, Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, Python 3.13.17 locally (3.11+ supported). Commands run from the project directory with the native Windows toolchain.

No mathematical proof or author-review flag remains outstanding in the current inventory. GitHub upload, remote CI, repository URL, publication license, and public release tagging remain author publication actions. Earlier incomplete reports and the Downloads progress copy are superseded; local historical archives are preserved.
