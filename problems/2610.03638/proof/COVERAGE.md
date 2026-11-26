# Code coverage: 2610.03638

This guide describes the current Lean package for **Smoothness-dependent stochastic bilevel optimization**. It is a map of code and verification entry points, not a claim that an external text has been formalized in full.

## Production scope

The Lake directory is `.`. Its default targets are `Smoothness2601`, `Bilevel`; its declared libraries are `Smoothness2601`, `Bilevel`. [project.json](../project.json) lists **247 production source files**, **249 inventoried Lean files**, and **2 audit/check entry files**. Production and inventory counts describe files, not distinct mathematical results.

Start with:

- [`Smoothness2601/MinimaxCorollaries.lean`](../Smoothness2601/MinimaxCorollaries.lean)
- [`Smoothness2601/ExactUpperCorollaries.lean`](../Smoothness2601/ExactUpperCorollaries.lean)
- [`Smoothness2601/BoundaryMinimax.lean`](../Smoothness2601/BoundaryMinimax.lean)

The code distinguishes finite smoothness lists, uniform-order bounds, stopping rules and boundary cases. Use the matching theorem and its model assumptions.

## Audit entry points

- [`proof/Audit.lean`](../proof/Audit.lean)
- [`proof/SourceAudit.lean`](../proof/SourceAudit.lean)

The inventory distinguishes production sources from other retained Lean files. Files outside the configured production and audit lists are available for inspection but are not automatically covered by the standard verification command. A default `lake build` and an explicit Lean audit serve different purposes: the former compiles its import closure, while the latter runs the checks encoded in that audit file.

## Interpreting verification

- Source checks validate the files and pinned configuration recorded by the repository verifier.
- A successful build establishes that the selected Lean code elaborates with its dependencies.
- An axiom audit establishes only the dependency conditions implemented by that audit; inspect its source for the selected declarations and allowed axioms.
- A conditional theorem retains its premises after verification. Source hashes and file counts do not establish mathematical correspondence with an external document.

Run `python scripts/verify.py --project 2610.03638` from the repository root for current build and audit results. Add `--static` to run source checks without executing Lean. See the [package README](../README.md) for setup.
