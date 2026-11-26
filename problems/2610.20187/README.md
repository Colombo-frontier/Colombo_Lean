# Dynamic regret in exp-concave online learning

**English** | [简体中文](README.zh-CN.md)

Independent Lean 4 package `2610.20187` in Colombo Lean. The formal definitions and theorem types in this directory determine the mathematical scope.

## Build configuration

| Setting | Value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.24.0` |
| Lake directory | `.` |
| Default targets | `Audit254`, `Paper254` |
| Libraries | `Audit254`, `Paper254` |
| Inventoried Lean files | 313 |
| Production source files | 312 |
| Audit/check entry files | 1 |

Pinned configuration: [`lean-toolchain`](lean-toolchain), [`lakefile.toml`](lakefile.toml), [`lake-manifest.json`](lake-manifest.json). The [project inventory](project.json) records the current source hashes, production sources and audit/check entry files.

## Code entry points

- [`formalization/MinimaxMain254.lean`](formalization/MinimaxMain254.lean)
- [`formalization/UpperMain254.lean`](formalization/UpperMain254.lean)
- [`formalization/LowerMain254.lean`](formalization/LowerMain254.lean)
- [`Audit254.lean`](Audit254.lean)

Audit254 is a collection of local audit lemmas. The Paper254 library has separate regret and computational interfaces; primitive/oracle and finite-precision hypotheses must be checked in the selected theorem.

The [code coverage guide](proof/COVERAGE.md) explains the build and audit boundaries. A theorem is available only with the hypotheses in its Lean type; this documentation does not claim correspondence with an external document.

## Reproduce

Install Lean through [elan](https://github.com/leanprover/elan) and Python 3.11 or later. From the repository root, run the source checks:

```sh
python scripts/verify.py --project 2610.20187 --static
```

To fetch the pinned Mathlib cache and build the package:

```sh
cd problems/2610.20187
lake exe cache get
lake build
```

For the build and configured Lean audits, run this command from the repository root:

```sh
python scripts/verify.py --project 2610.20187
```

On systems where Python is named `python3`, substitute it in these commands. A static check validates source files and configuration; it does not execute Lean. Build and audit outcomes must come from a run against the current code.

[Repository guide](../../README.md) · [Contribution guide](../../CONTRIBUTING.md)
