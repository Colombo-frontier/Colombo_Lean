# Code coverage: 2610.00275

This guide describes the current Lean package for **Goldstein stationarity on Euclidean balls**. It is a map of code and verification entry points, not a claim that an external text has been formalized in full.

## Production scope

The Lake directory is `.`. Its default targets are `NCBall`; its declared libraries are `NCBall`. [project.json](../project.json) lists **154 production source files**, **156 inventoried Lean files**, and **2 audit/check entry files**. Production and inventory counts describe files, not distinct mathematical results.

Start with:

- [`NCBall/MainLower.lean`](../NCBall/MainLower.lean)
- [`NCBall/MainUpper.lean`](../NCBall/MainUpper.lean)

The upper construction requires a positive ball radius. Lower and upper statements use their own radius constants; no same-fixed-radius minimax equality is asserted here.

## Audit entry points

- [`proof/Audit.lean`](../proof/Audit.lean)
- [`proof/SourceAudit.lean`](../proof/SourceAudit.lean)

The inventory distinguishes production sources from other retained Lean files. Files outside the configured production and audit lists are available for inspection but are not automatically covered by the standard verification command. A default `lake build` and an explicit Lean audit serve different purposes: the former compiles its import closure, while the latter runs the checks encoded in that audit file.

## Interpreting verification

- Source checks validate the files and pinned configuration recorded by the repository verifier.
- A successful build establishes that the selected Lean code elaborates with its dependencies.
- An axiom audit establishes only the dependency conditions implemented by that audit; inspect its source for the selected declarations and allowed axioms.
- A conditional theorem retains its premises after verification. Source hashes and file counts do not establish mathematical correspondence with an external document.

Run `python scripts/verify.py --project 2610.00275` from the repository root for current build and audit results. Add `--static` to run source checks without executing Lean. See the [package README](../README.md) for setup.
