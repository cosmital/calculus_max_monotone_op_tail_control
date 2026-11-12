# Scalar monotone operators: maintenance instructions

## Source of truth

The public manuscript is `manuscript/monotone_calculus.pdf`. `docs/MANUSCRIPT_VERSION.json` pins the PDF and the private source used to build it. The optional local `../monotone_calculus.tex` and `manuscript/monotone_calculus.tex` are private and excluded from publication. A public clone must reproduce checks without TeX. Read the result dictionary, PDF index, notation guide, and current progress before changing mathematical interfaces.

## Current state

All 335 mathematical modules / 2480 indexed public declarations have proof mappings for all 62 numbered and 56 supplemental claims. On 2026-11-09 the author explicitly directed that correspondence review be treated as complete and authorized n ≥ 1 in Example 2.5. That acceptance is recorded in `docs/AUTHOR_REVIEW.json`; do not reset it merely because older archives describe pending review. The current reader dictionary uses printed PDF numbering and short descriptions; supporting proofs remain in the full mapping. No routine mathematical proof additions are requested.

## Execution and dependencies

Use this directory as the explicit working directory. The local installation is native Windows Lean 4.19.0, Lake 5.0.0-6caaee8, Python 3.13.17. At session start report actual versions. Use `python`, not `py -3`, on this Windows installation. WSL can use `tools/run_native.py` / `tools/run_windows.ps1`. Never mix Windows and Linux compiled dependencies or silently change environments.

Preserve `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Lean is `leanprover/lean4:v4.19.0`; Mathlib is `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Do not run `lake update`, recreate the project, edit dependencies to force success, or remove installed dependency artifacts. Search the pinned local Mathlib sources before relying on an API. Treat unavailable executables and network/sandbox failures as environment issues.

## Mathematical integrity

Preserve quantifiers, hypotheses, conclusions, orientation, signs, domains, endpoint fibers, atoms, measurability, integrability, and extended values. Do not weaken conclusions, strengthen final hypotheses, assume the desired theorem, or use inconsistent premises. A mathematical amendment requires author authorization and explicit reconciliation with the manuscript. Continue independent work if a genuine obstruction is found.

Do not add `sorry`, `admit`, `sorryAx`, custom axioms, unsafe bypasses, or unchecked external certificates. Do not use `native_decide` to evade the audit. The transitive axiom allow-list stays `propext`, `Classical.choice`, `Quot.sound`. Raw `Operator` inequalities are graph inclusion; bundled orders and `IncLE`/`DecLE` use resolvent comparison. Scalar interior identities alone do not identify completed graphs. Real and extended nonnegative integrals are distinct.

## Verification and correspondence

Edit modular sources, not historical flattened copies. Keep every module imported by its library root, and preserve smoke tests, both audits, and independent expected types in `PaperChecks.lean`. Compile changed modules and dependents. Use:

```text
python tools/verify.py --metadata
python tools/verify.py --compile
python tools/verify.py --coverage
python -m unittest discover -s tests -v
```

At a public release candidate use `python tools/verify.py --release --fresh`. Do not repeat a completed fresh workflow without a relevant source change or unresolved concern. The 9 November package preparation preserves the completed 8 November fresh evidence for the unchanged mathematical code and records the comment-only rebuild separately. Before public release tagging, require the GitHub fresh-build and correspondence jobs to pass. Never use older receipts as proof that changed sources compiled.

Synchronize declaration metadata and reader documents. `tools/refresh_metadata.py` relocates declarations and renders the PDF readers without granting approval. The coverage gate binds acceptance to the PDF, claim mappings, and exact Lean sources. Future semantic changes require an explicit new correspondence review. Never suppress failures, narrow audits, or remove coverage requirements to pass a gate. Add regression tests for genuine tooling changes.

## Distribution and preservation

Use `tools/export_release.py` for a PDF-only public package. Do not distribute `.tex`, `.bib`, local development archives, caches, credentials, or scratch verification output. Preserve these locally. Distributable receipts live under `verification/evidence/`; regenerate `SHA256SUMS.txt` after final distributable edits. Keep pinned dependency files in the public package. Do not publish, push, or create a remote release without author authorization. Do not discard user edits or use destructive Git operations.
