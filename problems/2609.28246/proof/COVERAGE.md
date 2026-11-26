# Code coverage: 2609.28246

This guide describes the current Lean package for **Higher-order convex-concave minimax optimization**. It is a map of code and verification entry points, not a claim that an external text has been formalized in full.

## Production scope

The Lake directory is `package/audit/lean_project`. Its default targets are `LeanArticleAudit`; its declared libraries are `LeanArticleAudit`, `MinimaxAudit`, `VIReference`. [project.json](../project.json) lists **152 production source files**, **155 inventoried Lean files**, and **3 audit/check entry files**. Production and inventory counts describe files, not distinct mathematical results.

Start with:

- [`package/audit/lean_project/MinimaxAudit/RevisedMain.lean`](../package/audit/lean_project/MinimaxAudit/RevisedMain.lean)
- [`package/audit/lean_project/MinimaxAudit/MainLower.lean`](../package/audit/lean_project/MinimaxAudit/MainLower.lean)

Use the theorem statements in MinimaxAudit/RevisedMain.lean and their positive-parameter and measurability hypotheses. Other preserved Lean directories are not automatically part of this Lake target.

## Audit entry points

- [`package/audit/lean_project/RateForge/AxiomAudit.lean`](../package/audit/lean_project/RateForge/AxiomAudit.lean)
- [`proof/Audit.lean`](../proof/Audit.lean)
- [`proof/SourceAudit.lean`](../proof/SourceAudit.lean)

The inventory distinguishes production sources from other retained Lean files. Files outside the configured production and audit lists are available for inspection but are not automatically covered by the standard verification command. A default `lake build` and an explicit Lean audit serve different purposes: the former compiles its import closure, while the latter runs the checks encoded in that audit file.

## Interpreting verification

- Source checks validate the files and pinned configuration recorded by the repository verifier.
- A successful build establishes that the selected Lean code elaborates with its dependencies.
- An axiom audit establishes only the dependency conditions implemented by that audit; inspect its source for the selected declarations and allowed axioms.
- A conditional theorem retains its premises after verification. Source hashes and file counts do not establish mathematical correspondence with an external document.

Run `python scripts/verify.py --project 2609.28246` from the repository root for current build and audit results. Add `--static` to run source checks without executing Lean. See the [package README](../README.md) for setup.
