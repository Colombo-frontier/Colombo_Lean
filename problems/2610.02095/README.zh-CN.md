# Randomized matvec lower bounds for matrix games

[English](README.md) | **简体中文**

这是 Colombo Lean 中独立的 Lean 4 package `2610.02095`。具体 mathematical scope 以本目录的 formal definitions 和 theorem types 为准。

## Build configuration

| 配置 | 内容 |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.19.0` |
| Lake directory | `.` |
| Default targets | `Matvec`, `LowRank` |
| Libraries | `Matvec`, `LowRank` |
| Inventoried Lean files | 211 |
| Production source files | 209 |
| Audit/check entry files | 2 |

固定配置见 [`lean-toolchain`](lean-toolchain), [`lakefile.toml`](lakefile.toml), [`lake-manifest.json`](lake-manifest.json)。[project inventory](project.json) 记录当前 source hashes、production sources 与 audit/check entry files。

## Code entry points

- [`Matvec/MainSequences.lean`](Matvec/MainSequences.lean)
- [`Matvec/AllDimensionSpectral.lean`](Matvec/AllDimensionSpectral.lean)

Matvec 与随附的 LowRank support library 是不同的 Lake targets；应分别检查各 result 的 policy、query budget 和 matrix dimension assumptions。

[Code coverage guide](proof/COVERAGE.md) 说明 build 与 audit 的边界。使用 theorem 时必须满足其 Lean type 中的 hypotheses；本说明不宣称与外部文档逐项对应。

## 运行方式

通过 [elan](https://github.com/leanprover/elan) 安装 Lean，并准备 Python 3.11 或更高版本。在 repository root 运行 source checks：

```sh
python scripts/verify.py --project 2610.02095 --static
```

下载固定的 Mathlib cache 并 build：

```sh
cd problems/2610.02095
lake exe cache get
lake build
```

在 repository root 运行 build 和配置的 Lean audits：

```sh
python scripts/verify.py --project 2610.02095
```

若系统中的 Python 命令为 `python3`，请相应替换。Static check 检查 source files 与 configuration，不执行 Lean；build 和 audit 的结果应以当前 code 的实际运行记录为准。

[Repository guide](../../README.zh-CN.md) · [Contribution guide](../../CONTRIBUTING.zh-CN.md)
