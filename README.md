# Scalar maximally monotone operators — Lean verification

> **Package upload pending.** This reader guide is published first. The PDF, proof sources, and linked documentation will become available when the prepared Lean package is uploaded.


Lean companion to Cosme Louart's *A calculus of scalar maximally monotone operators for aggregation and tail control*.

This package contains formal proofs for the scalar operator calculus, Hardy aggregation bounds, and concentration inequalities with random Lipschitz controls. It includes 335 mathematical modules and 2,480 indexed public declarations, with proof mappings for 62 numbered manuscript items and 56 supplemental claims.

## Read the proofs without installing Lean

1. Open the [bundled article PDF](manuscript/monotone_calculus.pdf).
2. Find the result in the [paper-to-Lean dictionary](docs/RESULT_DICTIONARY.md), using its printed number or short description.
3. Follow its **Proofs** link to the full declaration mapping, then follow a source link to the corresponding Lean file.

The [notation guide](docs/NOTATION.md) translates the paper's notation into Lean definitions. The [supplemental index](docs/LABEL_INDEX.md) covers equations and unnumbered claims. After cloning or downloading the repository, open `docs/index.html` in a web browser for a searchable dictionary; GitHub's file preview does not run its search interface.

## Install and build

You need Git, Python 3.11 or later, and Lean managed by Elan. Follow the [official Lean installation guide](https://lean-lang.org/install/); VS Code with the official Lean 4 extension provides an interactive proof viewer. Open a new terminal after installation so that `lake` is available.

Clone the repository and run the following commands from its root:

```sh
git clone https://github.com/cosmital/calculus_max_monotone_op_tail_control.git
cd calculus_max_monotone_op_tail_control
lake env lean --version
lake exe cache get
lake build MonotoneOperators EndOfPaper Paper
```

The project pins **Lean 4.19.0** in `lean-toolchain` and Mathlib commit **`c44e0c8ee63ca166450922a373c7409c5d26b00b`** in `lakefile.toml` and `lake-manifest.json`. Keep these files unchanged when reproducing the verification. `lake exe cache get` downloads the [official Mathlib cache](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency#getting-started); the following build compiles this package. An initial build needs network access to obtain the pinned toolchain and dependencies.

The Python tools use only the standard library. No LaTeX installation or manuscript source is needed. Commands below use `python`; use `python3` instead if that is your Python 3.11+ executable on Linux or macOS. Run all commands in the cloned repository directory.

## Check the package

```sh
python tools/verify.py --metadata
python tools/verify.py --compile
python tools/verify.py --coverage
python -m unittest discover -s tests -v
```

| Command | What it checks |
|---|---|
| `--metadata` | The bundled PDF hash, claim inventory, declaration locations, library imports, proof-source restrictions, and dependency pins. This command does not compile proofs. |
| `--compile` | Every supplied library, smoke tests, both transitive axiom audits, and the independently stated expected types in `PaperChecks.lean`. |
| `--coverage` | The recorded author review tying the manuscript claims to their Lean declarations and exact source files. |
| Python tests | The verification, export, lookup, and platform-runner utilities. |

Each command must exit with code 0. Reports and compiler output are written to `verification/current/`. Compilation checks Lean proofs; correspondence with the mathematical manuscript also depends on the explicit author review in [AUTHOR_REVIEW.json](docs/AUTHOR_REVIEW.json), recorded at the author's direction on 9 November 2026.

To combine compilation and recorded correspondence in one command, run:

```sh
python tools/verify.py --release
```

For a fresh rebuild of the package's own modules, use `python tools/verify.py --release --fresh`. This preserves installed dependency artifacts. Historical completed runs and their scope are documented in [CODEX_PROGRESS.md](docs/CODEX_PROGRESS.md) and [verification/evidence](verification/evidence/).

## Find and inspect one result

For example, locate the survival-comparison lemma or the main concentration theorem:

```sh
python tools/lookup.py 1.17
python tools/lookup.py 3.6
python tools/lookup.py "Hardy"
```

Lookup prints the PDF location and the names, files, and lines of the corresponding Lean declarations. To build the relevant modules and display their exact Lean types and axiom dependencies, use an exact result number:

```sh
python tools/lookup.py 1.17 --check
python tools/lookup.py 3.6 --check
```

In VS Code, open the repository folder and then the source file listed by lookup. The Lean Infoview shows the proof state at the cursor. Follow definitions and theorem names to inspect their hypotheses and dependencies.

## Use the library in Lean

`MonotoneOperators` contains the operator algebra, resolvents, and order structure. `EndOfPaper` contains the integration, aggregation, and concentration results. `Paper` imports both libraries. Most core declarations are in the `ScalarMonotone` namespace; the application declarations mainly use `ScalarMonotone.EndOfPaper`.

For a minimal example, create `Example.lean` in the repository root:

```lean
import MonotoneOperators.Basic

open ScalarMonotone

#check inverse_inverse
#print axioms inverse_inverse

example (f : Operator) : inverse (inverse f) = f :=
  inverse_inverse f
```

Check it with:

```sh
lake env lean Example.lean
```

For the whole library, use `import Paper`; for a particular result, the lookup tool identifies the more specific module to import. A raw `Operator` is a function `ℝ → Set ℝ`, so its built-in `≤` means graph inclusion. The paper's resolvent comparison uses `IncLE`/`DecLE`, or the orders on the bundled maximal graphs. See the [notation guide](docs/NOTATION.md) before translating an inequality.

Use a separate working clone for new Lean files: the reproducibility checks bind author acceptance to the exact distributed sources and will report additional or modified Lean files.

## Troubleshooting

- **`lake` is not found:** complete the Lean/Elan installation and reopen the terminal.
- **Unknown module or missing compiled dependency:** run `lake exe cache get`, then the library build, from the repository root.
- **Wrong Lean version:** run `lake env lean --version` inside the repository and check that it reports 4.19.0. Preserve the supplied dependency pins; do not run `lake update` for reproduction.
- **Windows versus WSL:** build and obtain dependencies in the same operating system. A fresh clone in each environment avoids mixing compiled artifacts.
- **Metadata or correspondence failure:** use an unchanged clone and read the reported mismatch. Replacing the PDF or Lean files requires explicit reconciliation with their recorded hashes.

The [detailed reproduction guide](docs/LOCAL_RUN.md) includes the individual compiler/audit commands and the existing native Windows runner.

## Repository contents

| Path | Purpose |
|---|---|
| `MonotoneOperators/` | Core scalar maximally monotone operator theory. |
| `EndOfPaper/` | Integration, Hardy transforms, aggregation, and tail bounds. |
| `Paper.lean`, `PaperChecks.lean` | Library entry point and independent statement checks. |
| `AxiomAudit.lean`, `AxiomAuditEnd.lean` | Transitive axiom audits; the allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. |
| `docs/` | PDF correspondence, declaration index, notation, and reproduction instructions. |
| `tools/`, `tests/` | Verification and distribution utilities and their tests. |
| `manuscript/` | The exact PDF used by the correspondence records. |
| `verification/evidence/` | Preserved verification receipts. |

The GitHub Actions workflow in [`.github/workflows/`](.github/workflows/) runs compilation/audits and correspondence checks on pushes and pull requests. Inspect the repository's [Actions page](https://github.com/cosmital/calculus_max_monotone_op_tail_control/actions) for the status of the commit you use.

## Citation and questions

Please cite the accompanying article and identify the exact commit or release of this package; [CITATION.cff](CITATION.cff) supplies the repository metadata. Report reproducibility problems through [GitHub issues](https://github.com/cosmital/calculus_max_monotone_op_tail_control/issues), including your operating system, Lean/Python versions, the command, and its error output.
