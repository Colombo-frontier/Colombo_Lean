import Main
import Lean

/- Enumerate actual declarations by their source-module origin, including
   private names and generated logical auxiliaries. Independently traverse
   checked proof/definition bodies and compare with Lean.collectAxioms. -/
namespace Kimi002AuditInfrastructure
open Lean

structure BodyState where
  seen : NameSet := {}
  axioms : NameSet := {}
  missing : NameSet := {}
  unsafeConstants : NameSet := {}

/-- Traverse actual kernel bodies without using Lean's axiom collector/cache. -/
partial def visit (env : Environment) (name : Name) : StateM BodyState Unit := do
  if (← get).seen.contains name then return
  modify fun s => { s with seen := s.seen.insert name }
  let some info := env.checked.get.find? name |
    modify fun s => { s with missing := s.missing.insert name }
  if info.isUnsafe then
    modify fun s => { s with unsafeConstants := s.unsafeConstants.insert name }
  let visitExpr (e : Expr) := e.getUsedConstants.forM (visit env)
  match info with
  | .axiomInfo v =>
      modify fun s => { s with axioms := s.axioms.insert name }
      visitExpr v.type
  | .defnInfo v => visitExpr v.type *> visitExpr v.value
  | .thmInfo v => visitExpr v.type *> visitExpr v.value
  | .opaqueInfo v => visitExpr v.type *> visitExpr v.value
  | .quotInfo _ => pure ()
  | .ctorInfo v => visitExpr v.type
  | .recInfo v => visitExpr v.type
  | .inductInfo v => visitExpr v.type *> v.ctors.forM (visit env)

end Kimi002AuditInfrastructure

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let text ← liftIO (IO.FS.readFile "../proof/declarations.json")
  let json ← match Json.parse text with
    | .ok value => pure value
    | .error message => throwError "Invalid theorem inventory JSON: {message}"
  let originalNames ← match (fromJson? json : Except String (Array String)) with
    | .ok value => pure value
    | .error message => throwError "Invalid original theorem names: {message}"
  unless originalNames.size == 1236 do throwError "Expected 1236 original theorems"
  let mut names : Array Name := #[]
  let mut nameSet : NameSet := {}
  let mut theoremCount := 0
  let mut excludedUnsafe : Array String := #[]
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    let moduleName := (env.getModuleIdxFor? name |>.map
      (fun i => env.header.moduleNames[i.toNat]!)).getD Name.anonymous
    if moduleName == `Main then
      if info.isUnsafe then
        -- Unsafe executable compiler artifacts cannot occur in a checked proof.
        excludedUnsafe := excludedUnsafe.push name.toString
      else
        match info with
        | .axiomInfo _ => throwError "Custom unproved Main axiom: {name}"
        | .thmInfo _ => theoremCount := theoremCount + 1
        | _ => pure ()
        if info.type.hasExprMVar || info.type.hasFVar then
          throwError "Open declaration type: {name}"
        let some checked := env.checked.get.find? name |
          throwError "Main logical declaration is not kernel checked: {name}"
        match checked with
        | .defnInfo v =>
            if v.value.hasExprMVar || v.value.hasFVar then throwError "Open definition body: {name}"
        | .thmInfo v =>
            if v.value.hasExprMVar || v.value.hasFVar then throwError "Open theorem body: {name}"
        | .opaqueInfo v =>
            if v.value.hasExprMVar || v.value.hasFVar then throwError "Open opaque body: {name}"
        | _ => pure ()
        names := names.push name
        nameSet := nameSet.insert name
        rows := rows.push (Json.mkObj [
          ("name", toJson name.toString), ("module", toJson "Main"),
          ("is_theorem", toJson (match info with | .thmInfo _ => true | _ => false))])
  if names.isEmpty || theoremCount < 1236 then throwError "Missing Main logical declarations"
  let mut originals : NameSet := {}
  for entry in originalNames do
    let name := entry.toName
    if originals.contains name then throwError "Duplicate original theorem: {name}"
    originals := originals.insert name
    unless nameSet.contains name do throwError "Missing original Main theorem: {name}"
    let some (.thmInfo _) := env.checked.get.find? name |
      throwError "Original declaration lacks a kernel theorem proof: {name}"
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut closure : NameSet := {}
  let mut axiomRows : Array Json := #[]
  for name in names do
    let axioms ← Lean.collectAxioms name
    axiomRows := axiomRows.push (Json.mkObj [
      ("name", toJson name.toString), ("axioms", toJson (axioms.map Name.toString))])
    for ax in axioms do closure := closure.insert ax
    unless axioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "Unexpected transitive axiom at {name}: {axioms}"
  let (_, bodyState) := (names.forM (Kimi002AuditInfrastructure.visit env)).run {}
  unless bodyState.missing.isEmpty do
    throwError "Independent body traversal found missing constants: {bodyState.missing.toArray}"
  unless bodyState.unsafeConstants.isEmpty do
    throwError "Unsafe dependency in a checked body: {bodyState.unsafeConstants.toArray}"
  let bodyAxioms := bodyState.axioms.toArray
  unless bodyAxioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
    throwError "Independent body traversal found unexpected axioms: {bodyAxioms}"
  unless closure.toArray.all (fun a => bodyState.axioms.contains a) &&
      bodyAxioms.all (fun a => closure.contains a) do
    throwError "Lean axiom collector and independent body traversal disagree"
  let report := Json.mkObj [
    ("status", toJson "passed"), ("audit_kind", toJson "complete_module_origin_and_bodies"),
    ("source_module", toJson "Main"), ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount), ("original_named_theorem_count", toJson originals.size),
    ("unsafe_compiler_artifacts_excluded", toJson excludedUnsafe.size),
    ("excluded_unsafe_names", toJson excludedUnsafe),
    ("transitive_axioms", toJson (closure.toArray.map Name.toString)),
    ("independent_body_axioms", toJson (bodyAxioms.map Name.toString)),
    ("independent_body_visited", toJson bodyState.seen.size),
    ("declarations", Json.arr rows), ("per_declaration_axioms", Json.arr axiomRows)]
  liftIO (IO.println ("KERNEL_AUDIT_JSON:" ++ report.compress))
  logInfo m!"KERNEL AUDIT PASSED: {names.size} Main logical declarations, {theoremCount} theorems"
