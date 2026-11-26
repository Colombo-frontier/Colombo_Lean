# Code coverage: 2610.20187

This guide describes the current Lean package for **Dynamic regret in exp-concave online learning**. It is a map of code and verification entry points, not a claim that an external text has been formalized in full.

## Production scope

The Lake directory is `.`. Its default targets are `Audit254`, `Paper254`; its declared libraries are `Audit254`, `Paper254`. [project.json](../project.json) lists **312 production source files**, **313 inventoried Lean files**, and **1 audit/check entry files**. Production and inventory counts describe files, not distinct mathematical results.

Start with:

- [`formalization/MinimaxMain254.lean`](../formalization/MinimaxMain254.lean)
- [`formalization/UpperMain254.lean`](../formalization/UpperMain254.lean)
- [`formalization/LowerMain254.lean`](../formalization/LowerMain254.lean)
- [`Audit254.lean`](../Audit254.lean)

Audit254 is a collection of local audit lemmas. The Paper254 library has separate regret and computational interfaces; primitive/oracle and finite-precision hypotheses must be checked in the selected theorem.

## Audit entry points

- [`proof/Audit.lean`](../proof/Audit.lean)

The inventory distinguishes production sources from other retained Lean files. Files outside the configured production and audit lists are available for inspection but are not automatically covered by the standard verification command. A default `lake build` and an explicit Lean audit serve different purposes: the former compiles its import closure, while the latter runs the checks encoded in that audit file.

## Interpreting verification

- Source checks validate the files and pinned configuration recorded by the repository verifier.
- A successful build establishes that the selected Lean code elaborates with its dependencies.
- An axiom audit establishes only the dependency conditions implemented by that audit; inspect its source for the selected declarations and allowed axioms.
- A conditional theorem retains its premises after verification. Source hashes and file counts do not establish mathematical correspondence with an external document.

Run `python scripts/verify.py --project 2610.20187` from the repository root for current build and audit results. Add `--static` to run source checks without executing Lean. See the [package README](../README.md) for setup.
