# Colombo Lean

[简体中文](README.zh-CN.md) · [Contributing](CONTRIBUTING.md) · [Verification](docs/VERIFICATION.md)

[![Lean verification](https://github.com/Colombo-frontier/Colombo_Lean/actions/workflows/lean.yml/badge.svg)](https://github.com/Colombo-frontier/Colombo_Lean/actions/workflows/lean.yml)

Lean 4 formalizations of optimization, oracle complexity, probability, and related mathematical results. The repository contains 25 independent Lake projects. Each project pins its own Lean toolchain and dependencies and provides executable proof audits.

The formal statements and their explicit hypotheses in the Lean files define the scope. Directory identifiers organize the code; they do not certify correspondence with a particular manuscript or complete coverage of a paper. Start with each project's README for entry points and limitations.

## Projects

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
| [kimi_001](problems/kimi_001/) | Exact-value convex optimization in matched l1 geometry | `v4.32.1` |
| [kimi_002](problems/kimi_002/) | Full-history acceleration using exact comparisons | `v4.32.1` |
| [kimi_003](problems/kimi_003/) | Two-point stochastic convex optimization with heavy tails | `v4.32.1` |

## Verify a project

Install [elan](https://github.com/leanprover/elan) and Python 3.11 or later. There is no root Lake project: run Lake inside the selected project's `lake_project` directory, listed in its README and `project.json`.

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

Use `python3` where appropriate. The first full verification needs network access and enough disk space for the pinned toolchain and Mathlib. Other projects may require different Lean versions.

Static checks validate the current source inventory, hashes, configuration, and source policy. Full verification additionally builds the production modules and executes the listed Lean audits and statement checks. A successful static check is not a proof compilation result. Fresh reports are generated in `problems/<id>/proof/verification.json`; GitHub Actions records results for its own commit.

## Layout

```text
problems/<id>/
  project.json          # current source inventory and verification inputs
  README.md             # code entry points and scope
  <lake_project>/       # Lean sources and pinned Lake configuration
  proof/                # executable audits and scope documentation
scripts/                # discovery and verification
tests/                  # verifier regression tests
.github/workflows/      # fresh verification in CI
```

Dependencies and vendored code retain their applicable license and attribution notices. See [third-party notices](docs/THIRD_PARTY.md). No blanket license is granted for the repository's other code.
