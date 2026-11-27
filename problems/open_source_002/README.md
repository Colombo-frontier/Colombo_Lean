# Full-history acceleration using exact comparisons

**English** | [简体中文](README.zh-CN.md)

Independent Lean 4 package `open_source_002` in Colombo Lean. The formal definitions and theorem types in this directory determine the mathematical scope.

## Build configuration

| Setting | Value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.32.1` |
| Lake directory | `project` |
| Default targets | `Main` |
| Libraries | `Main` |
| Inventoried Lean files | 3 |
| Production source files | 1 |
| Audit/check entry files | 2 |

Pinned configuration: [`lean-toolchain`](project/lean-toolchain), [`lakefile.toml`](project/lakefile.toml), [`lake-manifest.json`](project/lake-manifest.json). The [project inventory](project.json) records the current source hashes, production sources and audit/check entry files.

## Code entry points

- [`project/Main.lean`](project/Main.lean)

Some lower-bound and joint-bracket results retain explicit Dorn input premises. Those hypotheses are not discharged merely because the Lean proof builds; upper-bound results have separate assumptions.

The [code coverage guide](proof/COVERAGE.md) explains the build and audit boundaries. A theorem is available only with the hypotheses in its Lean type; this documentation does not claim correspondence with an external document.

## Reproduce

Install Lean through [elan](https://github.com/leanprover/elan) and Python 3.11 or later. From the repository root, run the source checks:

```sh
python scripts/verify.py --project open_source_002 --static
```

To fetch the pinned Mathlib cache and build the package:

```sh
cd problems/open_source_002/project
lake exe cache get
lake build
```

For the build and configured Lean audits, run this command from the repository root:

```sh
python scripts/verify.py --project open_source_002
```

On systems where Python is named `python3`, substitute it in these commands. A static check validates source files and configuration; it does not execute Lean. Build and audit outcomes must come from a run against the current code.

[Repository guide](../../README.md) · [Contribution guide](../../CONTRIBUTING.md)
