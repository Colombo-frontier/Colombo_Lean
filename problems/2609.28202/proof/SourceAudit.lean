import FullJet
import Lean.Util.CollectAxioms

/-! This checks proof dependencies, not completeness of the paper formalization.
The latter is reported separately in COVERAGE.md. -/

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  match env.find? `FullJet.main_complexity_lower_bound with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Main complexity lower bound theorem missing."
  match env.find? `FullJet.Admissible.upperCandidate_failure_quarter with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Constant-success macro-algorithm theorem missing."
  match env.find? `FullJet.main_complexity_theorem with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Matching main complexity theorem missing."
  match env.find? `FullJet.verifiedJetMethod_succeeds with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Validated oracle method theorem missing."
  match env.find? `FullJet.main_expected_complexity_theorem with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Matching expected complexity theorem missing."
  match env.find? `FullJet.expectedJetMethod_guarantee with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Actual stopping method guarantee missing."
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `FullJet || name.toString.startsWith "_private.FullJet." then
      match info with
      | .thmInfo _ => names := names.push name
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "No project theorems found."
  -- Reuse the visited dependency closure; every visited dependency was already checked.
  let mut closure : Lean.CollectAxioms.State := {}
  for name in names do
    let (_, next) := ((Lean.CollectAxioms.collect name).run env).run closure
    closure := next
    let unexpected := closure.axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected axiom dependencies {unexpected}"
    logInfo m!"PASS {name}: cumulative dependency axioms {closure.axioms}"
  logInfo m!"AUDIT PASSED: {names.size} project theorems; standard axioms only."
  logInfo "MAIN LOWER BOUND PRESENT: FullJet.main_complexity_lower_bound"
  logInfo "CONSTANT SUCCESS PRESENT: FullJet.Admissible.upperCandidate_failure_quarter"
  logInfo "MATCHING MAIN THEOREM PRESENT: FullJet.main_complexity_theorem"
  logInfo "VALIDATED ORACLE METHOD PRESENT: FullJet.verifiedJetMethod_succeeds"
  logInfo "MATCHING EXPECTED THEOREM PRESENT: FullJet.main_expected_complexity_theorem"
  logInfo "EXPECTED STOPPING METHOD PRESENT: FullJet.expectedJetMethod_guarantee"
