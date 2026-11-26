# Code coverage: 2609.13462

This guide describes the current Lean package for **Higher-order monotone variational inequalities**. It is a map of code and verification entry points, not a claim that an external text has been formalized in full.

## Production scope

The Lake directory is `example_audits/monotone_vi/lean_project`. Its default targets are `LeanArticleAudit`; its declared libraries are `LeanArticleAudit`. [project.json](../project.json) lists **85 production source files**, **88 inventoried Lean files**, and **3 audit/check entry files**. Production and inventory counts describe files, not distinct mathematical results.

Start with:

- [`example_audits/monotone_vi/lean_project/LeanArticleAudit/Pilot/MainSourceContract.lean`](../example_audits/monotone_vi/lean_project/LeanArticleAudit/Pilot/MainSourceContract.lean)
- [`example_audits/monotone_vi/lean_project/LeanArticleAudit/Pilot/MainAssembly.lean`](../example_audits/monotone_vi/lean_project/LeanArticleAudit/Pilot/MainAssembly.lean)

The formal interfaces distinguish oracle, execution, upper-bound and lower-bound contracts. Read MainSourceContract and its hypotheses when using the assembled result.

## Audit entry points

- [`example_audits/monotone_vi/lean_project/Check.lean`](../example_audits/monotone_vi/lean_project/Check.lean)
- [`example_audits/monotone_vi/lean_project/RateForge/AxiomAudit.lean`](../example_audits/monotone_vi/lean_project/RateForge/AxiomAudit.lean)
- [`proof/Audit.lean`](../proof/Audit.lean)

The inventory distinguishes production sources from other retained Lean files. Files outside the configured production and audit lists are available for inspection but are not automatically covered by the standard verification command. A default `lake build` and an explicit Lean audit serve different purposes: the former compiles its import closure, while the latter runs the checks encoded in that audit file.

## Interpreting verification

- Source checks validate the files and pinned configuration recorded by the repository verifier.
- A successful build establishes that the selected Lean code elaborates with its dependencies.
- An axiom audit establishes only the dependency conditions implemented by that audit; inspect its source for the selected declarations and allowed axioms.
- A conditional theorem retains its premises after verification. Source hashes and file counts do not establish mathematical correspondence with an external document.

Run `python scripts/verify.py --project 2609.13462` from the repository root for current build and audit results. Add `--static` to run source checks without executing Lean. See the [package README](../README.md) for setup.
