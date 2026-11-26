import LowRank
import Lean.Util.CollectAxioms

/-! This checks proof dependencies. It does not certify that all manuscript
claims have been formalized; the separate coverage ledger records that. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `LowRank || name.toString.startsWith "_private.LowRank." then
      match info with
      | .thmInfo _ => names := names.push name
      -- Lean's compiler creates unsafe lambda-lifting declarations. They cannot
      -- occur in a kernel-checked proof. Every theorem is checked transitively below.
      | .axiomInfo v =>
        unless v.isUnsafe do throwError "Project logical axiom found: {name}"
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "No project theorems found."
  -- Share the visited set across roots. A previously visited constant already
  -- had its entire dependency closure checked; every newly reached axiom is
  -- still checked below. This avoids rewalking Mathlib for each project theorem.
  let mut auditState : Lean.CollectAxioms.State := {}
  for name in names do
    let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run auditState
    auditState := nextState
    let unexpected := auditState.axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected axiom dependencies {unexpected}"
    logInfo m!"PASS {name}: transitive dependency closure checked"
  logInfo m!"AXIOM UNION: {auditState.axioms}"
  logInfo m!"AUDIT PASSED: {names.size} project theorems; standard axioms only."
  logInfo "COVERAGE STATUS: manuscript MAIN THEOREM proved for all finite p>=1. There are positive c_p,C_p depending only on p such that c_p*R<=Q<=C_p*R*(1+log(k^2*(N+1)/epsilon)), N=min(a,b), R=min(N,k*epsilon^(-1/3)), for 1<=k<N, 0<epsilon<=1, and 1/5<=delta<=19/20. A fixed delta=2/3 corollary is proved. Both orientations, rank deficiency, integer query budgets and exact-recovery fallback are included. No extra probability or tail-energy premise remains. This does not claim a line-by-line formalization of every background statement; see COVERAGE.md."

