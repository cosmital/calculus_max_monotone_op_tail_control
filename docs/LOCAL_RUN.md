# Reproducing the Lean verification

Run commands from the repository root containing `lakefile.toml` and `lean-toolchain`. Python 3.11+ is required. The local tested Windows installation reports Lean 4.19.0, Lake 5.0.0-6caaee8, and Python 3.13.17. On this installation use `python`, not `py -3`.

The bundled PDF is the final submission manuscript synchronized on 12 November 2026. Its result numbers, equation references, and PDF page links are recorded in [MANUSCRIPT_VERSION.json](MANUSCRIPT_VERSION.json) and [PDF_INDEX.json](PDF_INDEX.json). The presentation migration is documented in [MANUSCRIPT_SYNC.json](MANUSCRIPT_SYNC.json); the 62 numbered results, 56 supplemental claims, declaration mappings, and Lean sources retain their accepted mathematical content.

```text
lake env lean --version
lake --version
python --version
python tools/verify.py --metadata
python tools/verify.py --compile
python tools/verify.py --coverage
python -m unittest discover -s tests -v
```

Use `python3` on Linux if appropriate. Keep the Lean version in `lean-toolchain`, Mathlib revision in `lakefile.toml`, and resolved dependencies in `lake-manifest.json`. Obtain dependencies for the same operating system as Lean. Do not mix Windows and Linux `.olean` artifacts. A new installation may use `lake exe cache get`; preserve an already working dependency cache.

The article PDF is sufficient for the public package. Metadata validation checks its exact hash, the PDF-numbered claim inventory, declaration locations, complete module imports, source restrictions, and dependency pins. Local private TeX is checked additionally when present. Author correspondence acceptance is bound to the PDF, mappings, and Lean files in `AUTHOR_REVIEW.json`.

The compiler gate runs:

```text
lake env lean --version
lake build MonotoneOperators EndOfPaper Paper
lake env lean EndSmokeTests.lean
lake env lean AxiomAudit.lean
lake env lean AxiomAuditEnd.lean
lake env lean PaperChecks.lean
```

All six must succeed. The axiom allow-list is `propext`, `Classical.choice`, `Quot.sound`. The source guard rejects Lean files changed during a check. `python tools/verify.py --release` combines compilation and author-approved coverage. Add `--fresh` for a full own-module rebuild; installed dependency artifacts are preserved.

For an individual result:

```text
python tools/lookup.py 2.5
python tools/lookup.py 3.6 --check
python tools/refresh_metadata.py
```

Lookup uses printed PDF numbers, descriptions, or Lean declaration names. `--check` builds the corresponding modules and displays types and axiom dependencies. The metadata refresher preserves approval records and rejects a changed PDF; it never grants author approval.

From WSL, invoke the existing Windows runner from this directory:

```text
/mnt/c/Users/cosme/AppData/Local/Programs/Python/Python313/python.exe tools/run_native.py environment
/mnt/c/Users/cosme/AppData/Local/Programs/Python/Python313/python.exe tools/run_native.py compile
```

The runner uses the native Windows installation and isolated receipts under `verification/current/`. `docs/CODEX_PROGRESS.md` and `verification/evidence/` identify actual completed checks. Exit 0 means the requested checks passed; exit 2 means metadata or correspondence failed; exit 127 means the compiler was unavailable.
