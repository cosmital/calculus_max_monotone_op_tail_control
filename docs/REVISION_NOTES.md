# Final submission synchronization — 12 November 2026

The bundled manuscript is now the 66-page final submission PDF. Its current hash is recorded in [MANUSCRIPT_VERSION.json](MANUSCRIPT_VERSION.json), and all 118 indexed PDF locations are reconciled in [MANUSCRIPT_SYNC.json](MANUSCRIPT_SYNC.json). The result numbering and Lean declarations are unchanged. The two equations in the relocated median proof are now (A.1) and (A.2); their dictionary entries and the proof-location link point into Appendix A.5. The earlier author acceptance is preserved for the unchanged mathematical claims and exact Lean sources, with the PDF bindings migrated transparently.

The obsolete archived-version footnote was removed from the manuscript, and PDF title metadata now matches the final article title. Prior artifacts are preserved locally and excluded from the public package.

The following notes describe the earlier preparation.

# Final manuscript and package reconciliation — 9 November 2026

The submitted PDF was rebuilt from the author's current `../monotone_calculus.tex`. All author revisions present in that source are retained, including the revised abstract, keywords, MSC classification, Aumann integration, article organization, and removal of the final Declarations section.

The only additional article edit in this preparation is the explicitly authorized n ≥ 1 assumption in Example 2.5. Exact comparison with the previous frozen source confirms that no other article text changed. All 62 numbered headings were checked against the rebuilt PDF. Equation pages come from the new AUX labels; unnumbered locations are reconciled with SyncTeX.

The author instructed that paper-to-Lean correspondence review be treated as complete. `AUTHOR_REVIEW.json` records that instruction, the PDF hash, all 118 claim fingerprints, and the exact Lean sources. This is an author-directed acceptance record; it does not assert an independent external review.

The public manuscript is now the PDF. TeX and bibliography files, including historical copies, are excluded from Git and the release export. The verification tools validate the frozen PDF and statement inventory without requiring private TeX. If a private source snapshot is available locally, they additionally check its hash and numbering.

`RESULT_DICTIONARY.md` now gives the PDF's result numbers, pages, and short descriptions. The full declaration mappings are in `PROOF_DETAILS.md`; equations and unnumbered claims are in `LABEL_INDEX.md`. Routine helpers are kept out of the main dictionary. Existing mathematical proofs and coverage requirements are preserved.

Stale incomplete-status descriptions were replaced in current reader documents and citation metadata. One obsolete comment in `EndOfPaper/ChainMetricAlgebra.lean` was updated; its mathematical tokens are unchanged. Earlier reports and private manuscripts are preserved locally under `historical/`, which is excluded from the public export. They describe earlier states and are not the current release status.

Obsolete development-status comments in `Paper.lean` and `PaperChecks.lean`, and the audit console’s “missing results” message, were also corrected. Mathematical proofs, expected types, and audit logic are unchanged.
