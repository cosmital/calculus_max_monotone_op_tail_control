# GitHub package and manuscript updates

The public repository is [cosmital/calculus_max_monotone_op_tail_control](https://github.com/cosmital/calculus_max_monotone_op_tail_control). Its root contains the Lean project, proof sources, reader documentation, and [final submission PDF](../manuscript/monotone_calculus.pdf). Follow [LOCAL_RUN.md](LOCAL_RUN.md) to reproduce the checks.

The PDF was synchronized with the final submission on 12 November 2026. [MANUSCRIPT_VERSION.json](MANUSCRIPT_VERSION.json) records its exact hash and page count. [MANUSCRIPT_SYNC.json](MANUSCRIPT_SYNC.json) records the comparison with the previously accepted manuscript and the updated locations of all 118 indexed claims. The 62 numbered results and their Lean declarations are unchanged. The odd-median proof is now in Appendix A.5; its equations are (A.1) and (A.2). The author acceptance of the unchanged mathematical correspondence is preserved and its PDF bindings are updated transparently.

## Prepare an update

Run from the project root. Reconcile any changed manuscript against the accepted claims before updating hashes or page links. A change to mathematical content requires a new correspondence review. The normal metadata refresher preserves acceptance and rejects a changed PDF.

```sh
python tools/verify.py --metadata
python tools/verify.py --coverage
python -m unittest discover -s tests -v
python tools/refresh_checksums.py
python tools/export_release.py dist/next-upload --zip
```

Use a fresh destination for each export. The exporter excludes private manuscript TeX, bibliography sources, development archives, caches, credentials, and temporary verification output. It preserves dependency pins and distributable receipts. Keep the old snapshots locally.

Copy the exported directory's contents, including hidden files, into a clean checkout of the repository, inspect the diff, commit, and push. Upload the expanded package; the ZIP is only a backup. Preserve remote edits and do not force-push.

## Check the uploaded commit

The [Actions page](https://github.com/cosmital/calculus_max_monotone_op_tail_control/actions) runs two independent checks:

- **Compile Lean proofs and audit axioms** performs a fresh build of the supplied libraries, both axiom audits, and reader checks.
- **Check author-reviewed manuscript correspondence** runs the Python tests and checks the PDF, claims, and exact Lean sources against the recorded acceptance.

Both jobs must succeed before creating a versioned release. Inspect the public PDF, dictionary page links, and source links. Record the exact commit when citing the package. No versioned release tag or DOI is created by an ordinary upload.

## Verification evidence

`verification/evidence/` preserves historical compiler receipts. The 8 November fresh run records six successful Lean commands and a correspondence failure before author acceptance. The 9 November receipts record the accepted state. The 12 November manuscript migration changes PDF locations and presentation metadata, with the Lean sources unchanged. Current metadata and coverage results do not claim a new compiler run; consult the dated receipts and GitHub job outcomes for actual compilation evidence.
