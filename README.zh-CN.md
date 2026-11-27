# Colombo Lean

[English](README.md) · [Contributing](CONTRIBUTING.zh-CN.md) · [Verification](docs/VERIFICATION.md)

本 repository 包含 25 个独立的 Lean 4 / Lake project，涉及 optimization、oracle complexity、probability 等。每个 project 分别固定 Lean toolchain 和 dependencies，并提供可执行的 proof audit。

使用范围以 Lean statement 及其显式 hypotheses 为准。目录 ID 用于组织 code，不代表某个 manuscript version 的对应关系，也不代表 full-paper coverage。各 project 的 README 提供 entry points 和 scope limitations。

## Project index

| Project | Topic | Lean |
|---|---|---|
| [2609.13462](problems/2609.13462/) | Higher-order monotone variational inequalities | `v4.32.1` |
| [2609.18230](problems/2609.18230/) | Smooth convex exact-value optimization | `v4.19.0` |
| [2609.18728](problems/2609.18728/) | Strongly convex exact-value optimization | `v4.19.0` |
| [2609.28202](problems/2609.28202/) | Higher-order nonconvex finite-sum optimization | `v4.19.0` |
| [2609.28238](problems/2609.28238/) | Common-loss second-order stationarity | `v4.19.0` |
| [2609.28246](problems/2609.28246/) | Higher-order convex-concave minimax optimization | `v4.32.1` |
| [2609.35840](problems/2609.35840/) | Low-rank approximation using matvec queries | `v4.19.0` |
| [2610.00229](problems/2610.00229/) | Fresh-gradient nonconvex-strongly-concave minimax optimization | `v4.19.0` |
| [2610.00245](problems/2610.00245/) | Randomized first-order optimization with Lipschitz Hessians | `v4.19.0` |
| [2610.00260](problems/2610.00260/) | Heavy-tailed nonsmooth convex optimization | `v4.19.0` |
| [2610.00275](problems/2610.00275/) | Goldstein stationarity on Euclidean balls | `v4.19.0` |
| [2610.00276](problems/2610.00276/) | Strongly convex noisy zeroth-order optimization | `v4.34.0` |
| [2610.02095](problems/2610.02095/) | Randomized matvec lower bounds for matrix games | `v4.19.0` |
| [2610.03633](problems/2610.03633/) | Joint oracle complexity of stochastic bilevel optimization | `v4.19.0` |
| [2610.03638](problems/2610.03638/) | Smoothness-dependent stochastic bilevel optimization | `v4.19.0` |
| [2610.12184](problems/2610.12184/) | Geodesically convex optimization in hyperbolic space | `v4.19.0` |
| [2610.16771](problems/2610.16771/) | Full-Hessian nonconvex-strongly-concave minimax optimization | `v4.32.1` |
| [2610.16832](problems/2610.16832/) | Second-order stationarity with sample reuse | `v4.19.0` |
| [2610.16991](problems/2610.16991/) | Finite-sum nonconvex-concave optimization | `v4.34.0` |
| [2610.17074](problems/2610.17074/) | Higher-order smooth nonconvex first-order optimization | `v4.19.0` |
| [2610.20187](problems/2610.20187/) | Dynamic regret in exp-concave online learning | `v4.24.0` |
| [2610.22208](problems/2610.22208/) | Gradient-Hessian query tradeoffs | `v4.19.0` |
| [open_source_001](problems/open_source_001/) | Exact-value convex optimization in matched l1 geometry | `v4.32.1` |
| [open_source_002](problems/open_source_002/) | Full-history acceleration using exact comparisons | `v4.32.1` |
| [open_source_003](problems/open_source_003/) | Two-point stochastic convex optimization with heavy tails | `v4.32.1` |

## Verification

安装 [elan](https://github.com/leanprover/elan) 和 Python 3.11 或以上版本。根目录不是 Lake project；Lake command 应在各 project 指定的 `lake_project` 目录执行。

```sh
git clone https://github.com/Colombo-frontier/Colombo_Lean.git
cd Colombo_Lean
python scripts/projects.py --json
python scripts/verify.py --static
cd problems/2609.18230
lake exe cache get
cd ../..
python scripts/verify.py --project 2609.18230
```

`--static` 检查 source inventory、hash、configuration 和 source policy。完整 verification 还会 build production modules，并执行 Lean audits 和 statement checks。Static check 通过不等于 Lean compilation 通过。

首次运行需要下载对应 toolchain 和 Mathlib。新生成的 verification report 位于各 project 的 `proof/verification.json`；GitHub Actions 的结果对应其运行的 commit。Code structure、使用限制和 verification 方法见各 project README 及 [Verification](docs/VERIFICATION.md)。

Vendored code 的 license 和 attribution 保留在对应目录，见 [third-party notices](docs/THIRD_PARTY.md)。本 repository 未对其余 code 统一授予 license。
