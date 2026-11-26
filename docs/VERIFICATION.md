# Verification

Each `project.json` describes the current package: `lake_project` locates its Lake directory, `source_files` records the retained Lean files and SHA-256 hashes, `production_files` selects modules to compile, `audit_files` selects executable audits and statement checks, and `config_files` pins the build configuration.

## Commands

```sh
python scripts/projects.py --json
python scripts/verify.py --static
python scripts/verify.py --project <id>
python scripts/verify.py
```

The last command verifies all projects and can require substantial time and disk space. Install elan so that each project's `lean-toolchain` selects the appropriate compiler. Run `lake exe cache get` inside the selected Lake directory before a first build to obtain compatible Mathlib artifacts.

## What the checks establish

Static verification checks source and configuration identity, inventory completeness, portable dependencies, and source policy. Full verification uses the pinned Lean version, compiles production modules, and runs every listed audit and statement check. Audit implementations define which declarations and transitive axioms they inspect; consult their Lean code for the precise scope. Expected foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Theorems can have explicit mathematical premises even when the axiom audit succeeds. In particular, `kimi_002` retains Dorn premises, conditional Bilevel results retain `PrefixBarrier`, and `2610.00276` exposes lower and upper components without an unconditional shared-model minimax endpoint. A successful build does not remove these hypotheses.

No check here certifies correspondence with an external manuscript. Statement-check filenames may retain names used by the Lean implementation; their current purpose is to check the expressions actually present in those files.

## Results

The verifier writes fresh logs and `proof/verification.json` for full runs, and `proof/static-verification.json` for static runs. Static-only success and full success are distinct. These generated files are ignored by Git. CI uploads the fresh results as artifacts and ties each run to a commit; the README badge shows workflow status rather than a perpetual correctness claim.

Dependency version pins are required build inputs. Do not replace them with newer versions solely to obtain a successful build: dependency changes require review and fresh verification.

## CI disk usage

CI frees unrelated preinstalled SDKs on its disposable runner before installing
Lean. GitHub caches contain only each project's `.lake/build`; dependency builds
come from Mathlib's public cache. This avoids keeping a separate multi-gigabyte
Mathlib checkout in every project cache. The largest source trees start first,
with at most eight project jobs running concurrently. Every project still runs
the full build and its configured audits.

When a project build cache is absent, CI can read a previously verified cache
with exactly matching project, toolchain, dependency lock, and Lake configuration
pins. Lake checks source freshness and the verifier reruns all audits. Successful
runs continue to save only `.lake/build` in the current cache format.
