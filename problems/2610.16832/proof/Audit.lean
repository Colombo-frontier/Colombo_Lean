import SampleReuse
import SecondOrder
import RandomizedFO2003
import GradientHessian
import LowRank
import Lean.Util.CollectAxioms

/-! Audit every safe declaration by its originating module, including
private/generated declarations and all four vendored library closures.
The preserved SourceAudit separately audits the original SampleReuse scope. -/
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[`SampleReuse, `SecondOrder, `RandomizedFO2003, `GradientHessian, `LowRank]
  let mut names : Array Name := #[]
  let mut theoremCount := 0
  let mut compilerCount := 0
  for root in roots do
    let mut localCount := 0
    let mut localTheorems := 0
    for (name, info) in env.constants.toList do
      let moduleName := (env.getModuleIdxFor? name |>.map
        (fun i => env.header.moduleNames[i.toNat]!)).getD Name.anonymous
      if moduleName.getRoot == root then
        if info.isUnsafe then
          compilerCount := compilerCount + 1
        else
          unless (env.checked.get.find? name).isSome do
            throwError "Declaration absent from the kernel-checked environment: {name}"
          names := names.push name
          localCount := localCount + 1
          match info with
          | .thmInfo _ =>
            theoremCount := theoremCount + 1
            localTheorems := localTheorems + 1
          | .axiomInfo _ => throwError "Custom unproved axiom: {name}"
          | _ => pure ()
    if localCount == 0 || localTheorems == 0 then
      throwError "No safe declarations or theorems found for library {root}"
    logInfo m!"AUDIT LIBRARY: {root}; {localCount} declarations; {localTheorems} theorems"
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut closure : Lean.CollectAxioms.State := {}
  for name in names do
    let (_, next) := ((Lean.CollectAxioms.collect name).run env).run closure
    closure := next
    let unexpected := closure.axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected transitive axioms {unexpected}"
    logInfo m!"PASS {name}: transitive closure checked"
  logInfo m!"AXIOM UNION: {closure.axioms}"
  logInfo m!"AUDIT PASSED: {names.size} declarations; {theoremCount} theorems; standard axioms only."
  logInfo m!"COMPILER ARTIFACTS: {compilerCount} unsafe declarations, unavailable to kernel proofs."
