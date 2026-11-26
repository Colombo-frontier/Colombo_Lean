# Higher-order convex-concave minimax optimization

**English** | [简体中文](README.zh-CN.md)

Independent Lean 4 package `2609.28246` in Colombo Lean. The formal definitions and theorem types in this directory determine the mathematical scope.

## Build configuration

| Setting | Value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.32.1` |
| Lake directory | `package/audit/lean_project` |
| Default targets | `LeanArticleAudit` |
| Libraries | `LeanArticleAudit`, `MinimaxAudit`, `VIReference` |
| Inventoried Lean files | 155 |
| Production source files | 152 |
| Audit/check entry files | 3 |

Pinned configuration: [`lean-toolchain`](package/audit/lean_project/lean-toolchain), [`lakefile.toml`](package/audit/lean_project/lakefile.toml), [`lake-manifest.json`](package/audit/lean_project/lake-manifest.json). The [project inventory](project.json) records the current source hashes, production sources and audit/check entry files.

## Code entry points

- [`package/audit/lean_project/MinimaxAudit/RevisedMain.lean`](package/audit/lean_project/MinimaxAudit/RevisedMain.lean)
- [`package/audit/lean_project/MinimaxAudit/MainLower.lean`](package/audit/lean_project/MinimaxAudit/MainLower.lean)

Use the theorem statements in MinimaxAudit/RevisedMain.lean and their positive-parameter and measurability hypotheses. Other preserved Lean directories are not automatically part of this Lake target.

The [code coverage guide](proof/COVERAGE.md) explains the build and audit boundaries. A theorem is available only with the hypotheses in its Lean type; this documentation does not claim correspondence with an external document.

## Reproduce

Install Lean through [elan](https://github.com/leanprover/elan) and Python 3.11 or later. From the repository root, run the source checks:

```sh
python scripts/verify.py --project 2609.28246 --static
```

To fetch the pinned Mathlib cache and build the package:

```sh
cd problems/2609.28246/package/audit/lean_project
lake exe cache get
lake build
```

For the build and configured Lean audits, run this command from the repository root:

```sh
python scripts/verify.py --project 2609.28246
```

On systems where Python is named `python3`, substitute it in these commands. A static check validates source files and configuration; it does not execute Lean. Build and audit outcomes must come from a run against the current code.

[Repository guide](../../README.md) · [Contribution guide](../../CONTRIBUTING.md)
