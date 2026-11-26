import NCConcave16991.AxiomAudit
import Lean.Util.CollectAxioms

/-! Re-execute the original public-namespace audit against the imported project.
The original build-time AxiomAudit.lean remains byte-for-byte intact. Lean 4.34
collectAxioms uses precomputed imported axiom data; its internal collector is
private, so this adapter uses the supported public API. -/
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`NCConcave16991).isPrefixOf name then
      match info with
      | .axiomInfo _ => throwError "Paper-specific axiom declaration {name}"
      | _ => pure ()
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Unapproved axiom {ax} in declaration {name}"
      checked := checked + 1
      if info.isTheorem then theorems := theorems + 1
  if checked == 0 || theorems == 0 then throwError "No source declarations audited."
  logInfo m!"SOURCE AUDIT PASSED: {checked} public declarations; {theorems} theorems; standard axioms only."
