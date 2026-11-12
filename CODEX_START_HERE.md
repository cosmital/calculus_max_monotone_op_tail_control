# Package maintenance

Start with `README.md`, `docs/CODEX_PROGRESS.md`, and `AGENTS.md`. The public manuscript is `manuscript/monotone_calculus.pdf`; the reader dictionary refers to printed PDF result numbers and pages.

All 62 numbered and 56 supplemental claims have proof mappings. The author directed that correspondence review be recorded on 2026-11-09. Example 2.5 now explicitly assumes n ≥ 1. No mathematical proof development is outstanding in the current inventory.

Preserve the pinned Lean/Mathlib versions and all completed proofs. The private parent manuscript and local TeX snapshot are excluded from distribution. Reconcile any future manuscript edit against the PDF index and actual claims before updating review records. Metadata generation never grants approval.

Run all commands from this directory. Use `python tools/verify.py --metadata`, `--compile`, and `--coverage`; `--release` combines the build and correspondence checks. Use `--fresh` only for a required fresh rebuild; it preserves dependency artifacts. The installed Windows environment is documented in `docs/LOCAL_RUN.md`.

The public package can be reproduced without TeX. `python tools/export_release.py dist/scalar_monotone_verification --zip` creates an upload directory and ZIP without private sources, caches, scratch output, or development archives. Publishing is a separate author action.
