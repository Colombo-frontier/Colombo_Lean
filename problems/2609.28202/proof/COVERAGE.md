# Code coverage: 2609.28202

This guide describes the current Lean package for **Higher-order nonconvex finite-sum optimization**. It is a map of code and verification entry points, not a claim that an external text has been formalized in full.

## Production scope

The Lake directory is `.`. Its default targets are `FullJet`; its declared libraries are `FullJet`. [project.json](../project.json) lists **136 production source files**, **138 inventoried Lean files**, and **2 audit/check entry files**. Production and inventory counts describe files, not distinct mathematical results.

Start with:

- [`FullJet/MainComplexity.lean`](../FullJet/MainComplexity.lean)
- [`FullJet/MainExpectedComplexity.lean`](../FullJet/MainExpectedComplexity.lean)

The complexity statements use the encoded componentwise oracle model. Inspect the finite-sum size and parameter restrictions in the lower-bound and expected-complexity theorem types.

## Audit entry points

- [`proof/Audit.lean`](../proof/Audit.lean)
- [`proof/SourceAudit.lean`](../proof/SourceAudit.lean)

The inventory distinguishes production sources from other retained Lean files. Files outside the configured production and audit lists are available for inspection but are not automatically covered by the standard verification command. A default `lake build` and an explicit Lean audit serve different purposes: the former compiles its import closure, while the latter runs the checks encoded in that audit file.

## Interpreting verification

- Source checks validate the files and pinned configuration recorded by the repository verifier.
- A successful build establishes that the selected Lean code elaborates with its dependencies.
- An axiom audit establishes only the dependency conditions implemented by that audit; inspect its source for the selected declarations and allowed axioms.
- A conditional theorem retains its premises after verification. Source hashes and file counts do not establish mathematical correspondence with an external document.

Run `python scripts/verify.py --project 2609.28202` from the repository root for current build and audit results. Add `--static` to run source checks without executing Lean. See the [package README](../README.md) for setup.
