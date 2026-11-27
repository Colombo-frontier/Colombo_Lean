# Two-point stochastic convex optimization with heavy tails

**English** | [简体中文](README.zh-CN.md)

Independent Lean 4 package `hy4_kimi_003` in Colombo Lean. The formal definitions and theorem types in this directory determine the mathematical scope.

## Build configuration

| Setting | Value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.32.1` |
| Lake directory | `project` |
| Default targets | `Main` |
| Libraries | `Main` |
| Inventoried Lean files | 233 |
| Production source files | 231 |
| Audit/check entry files | 2 |

Pinned configuration: [`lean-toolchain`](project/lean-toolchain), [`lakefile.toml`](project/lakefile.toml), [`lake-manifest.json`](project/lake-manifest.json). The [project inventory](project.json) records the current source hashes, production sources and audit/check entry files.

## Code entry points

- [`project/FullMain.lean`](project/FullMain.lean)
- [`project/ModelFull.lean`](project/ModelFull.lean)
- [`project/Main.lean`](project/Main.lean)

The main theorem is parameterized by Regime and the encoded scalar hidden-handle oracle model. Inspect ModelFull for dimension, accuracy, per-handle reply and worst-path query-budget restrictions.

The [code coverage guide](proof/COVERAGE.md) explains the build and audit boundaries. A theorem is available only with the hypotheses in its Lean type; this documentation does not claim correspondence with an external document.

## Reproduce

Install Lean through [elan](https://github.com/leanprover/elan) and Python 3.11 or later. From the repository root, run the source checks:

```sh
python scripts/verify.py --project hy4_kimi_003 --static
```

To fetch the pinned Mathlib cache and build the package:

```sh
cd problems/hy4_kimi_003/project
lake exe cache get
lake build
```

For the build and configured Lean audits, run this command from the repository root:

```sh
python scripts/verify.py --project hy4_kimi_003
```

On systems where Python is named `python3`, substitute it in these commands. A static check validates source files and configuration; it does not execute Lean. Build and audit outcomes must come from a run against the current code.

[Repository guide](../../README.md) · [Contribution guide](../../CONTRIBUTING.md)
