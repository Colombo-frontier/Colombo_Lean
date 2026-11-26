# Higher-order monotone variational inequalities

**English** | [简体中文](README.zh-CN.md)

Independent Lean 4 package `2609.13462` in Colombo Lean. The formal definitions and theorem types in this directory determine the mathematical scope.

## Build configuration

| Setting | Value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.32.1` |
| Lake directory | `example_audits/monotone_vi/lean_project` |
| Default targets | `LeanArticleAudit` |
| Libraries | `LeanArticleAudit` |
| Inventoried Lean files | 88 |
| Production source files | 85 |
| Audit/check entry files | 3 |

Pinned configuration: [`lean-toolchain`](example_audits/monotone_vi/lean_project/lean-toolchain), [`lakefile.toml`](example_audits/monotone_vi/lean_project/lakefile.toml), [`lake-manifest.json`](example_audits/monotone_vi/lean_project/lake-manifest.json). The [project inventory](project.json) records the current source hashes, production sources and audit/check entry files.

## Code entry points

- [`example_audits/monotone_vi/lean_project/LeanArticleAudit/Pilot/MainSourceContract.lean`](example_audits/monotone_vi/lean_project/LeanArticleAudit/Pilot/MainSourceContract.lean)
- [`example_audits/monotone_vi/lean_project/LeanArticleAudit/Pilot/MainAssembly.lean`](example_audits/monotone_vi/lean_project/LeanArticleAudit/Pilot/MainAssembly.lean)

The formal interfaces distinguish oracle, execution, upper-bound and lower-bound contracts. Read MainSourceContract and its hypotheses when using the assembled result.

The [code coverage guide](proof/COVERAGE.md) explains the build and audit boundaries. A theorem is available only with the hypotheses in its Lean type; this documentation does not claim correspondence with an external document.

## Reproduce

Install Lean through [elan](https://github.com/leanprover/elan) and Python 3.11 or later. From the repository root, run the source checks:

```sh
python scripts/verify.py --project 2609.13462 --static
```

To fetch the pinned Mathlib cache and build the package:

```sh
cd problems/2609.13462/example_audits/monotone_vi/lean_project
lake exe cache get
lake build
```

For the build and configured Lean audits, run this command from the repository root:

```sh
python scripts/verify.py --project 2609.13462
```

On systems where Python is named `python3`, substitute it in these commands. A static check validates source files and configuration; it does not execute Lean. Build and audit outcomes must come from a run against the current code.

[Repository guide](../../README.md) · [Contribution guide](../../CONTRIBUTING.md)
