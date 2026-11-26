import SecondOrder
import Lean.Util.CollectAxioms

/-! Kernel trust audit. Completeness is deliberately recorded separately. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut theoremCount := 0
  for (name, info) in env.constants.toList do
    if name.getRoot == `SecondOrder || name.toString.startsWith "_private.SecondOrder." then
      match info with
      | .axiomInfo val =>
        -- Lean emits unsafe compiler-only lambda placeholders; these cannot
        -- enter safe declarations. Every safe declaration is audited below.
        unless val.isUnsafe do throwError "Project axiom found: {name}"
      | .thmInfo _ =>
        names := names.push name
        theoremCount := theoremCount+1
      | .defnInfo val =>
        unless val.safety == .unsafe do names := names.push name
      | .opaqueInfo _ => names := names.push name
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  if theoremCount == 0 then throwError "No project theorems found."
  -- The environment is immutable during this traversal. Reuse the official
  -- collector's visited set across roots, while retaining its full cumulative
  -- axiom set. Every root is visited; no dependency or disallowed axiom is lost.
  -- This avoids re-traversing the same large mathlib proof once per theorem.
  let mut dependencies : Lean.CollectAxioms.State := {}
  for name in names do
    let (_, next) := ((Lean.CollectAxioms.collect name).run env).run dependencies
    dependencies := next
    let axioms := dependencies.axioms
    let unexpected := axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected dependencies {unexpected}"
    logInfo m!"PASS {name}: cumulative dependency axioms {axioms}"
  logInfo m!"AUDIT PASSED: {names.size} declarations, {theoremCount} theorem declarations."
  logInfo "This audit does not certify completeness of the manuscript formalization."
