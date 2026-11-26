import Main
import Lean

/-! Complete production-module audit, including private and generated logical
constants and the vendored SLT modules. The independent body walk does not call
Lean.collectAxioms. Unsafe compiler artifacts are recorded and excluded from
logical roots; any unsafe dependency of a checked root is rejected. -/
namespace Kimi003AuditInfrastructure
open Lean

structure BodyState where
  seen : NameSet := {}
  axioms : NameSet := {}
  missing : NameSet := {}
  unsafeConstants : NameSet := {}

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

end Kimi003AuditInfrastructure

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modulesText ← liftIO (IO.FS.readFile "../proof/modules.json")
  let modulesJson ← match Json.parse modulesText with
    | .ok value => pure value
    | .error message => throwError "Invalid module inventory JSON: {message}"
  let modules ← match (fromJson? modulesJson : Except String (Array String)) with
    | .ok value => pure value
    | .error message => throwError "Invalid module inventory array: {message}"
  unless modules.size == 231 do throwError "Expected 231 production modules"
  let mut moduleSet : NameSet := {}
  for entry in modules do
    let name := entry.toName
    if moduleSet.contains name then throwError "Duplicate production module: {name}"
    moduleSet := moduleSet.insert name
    unless env.header.moduleNames.contains name do
      throwError "Production module was not imported: {name}"
  let coverageText ← liftIO (IO.FS.readFile "../proof/declarations.json")
  let coverageJson ← match Json.parse coverageText with
    | .ok value => pure value
    | .error message => throwError "Invalid coverage inventory JSON: {message}"
  let coverageArray ← match coverageJson.getObjVal? "declarations" with
    | .ok value => pure value
    | .error message => throwError "Missing coverage declarations: {message}"
  let coverageNames ← match (fromJson? coverageArray : Except String (Array String)) with
    | .ok value => pure value
    | .error message => throwError "Invalid coverage declarations: {message}"
  unless coverageNames.size == 217 do throwError "Expected 217 coverage declarations"
  let mut names : Array Name := #[]
  let mut nameSet : NameSet := {}
  let mut theoremCount := 0
  let mut excludedUnsafe : Array String := #[]
  let mut rows : Array Json := #[]
  let mut observedModules : NameSet := {}
  for (name, info) in env.constants.toList do
    let moduleName := (env.getModuleIdxFor? name |>.map
      (fun i => env.header.moduleNames[i.toNat]!)).getD Name.anonymous
    if moduleSet.contains moduleName then
      if info.isUnsafe then
        excludedUnsafe := excludedUnsafe.push name.toString
      else
        match info with
        | .axiomInfo _ => throwError "Custom unproved production axiom: {name}"
        | .thmInfo _ => theoremCount := theoremCount + 1
        | _ => pure ()
        if info.type.hasExprMVar || info.type.hasFVar then
          throwError "Open declaration type: {name}"
        let some checked := env.checked.get.find? name |
          throwError "Production logical declaration is not kernel checked: {name}"
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
        observedModules := observedModules.insert moduleName
        rows := rows.push (Json.mkObj [
          ("name", toJson name.toString), ("module", toJson moduleName.toString),
          ("is_theorem", toJson (match info with | .thmInfo _ => true | _ => false))])
  if names.isEmpty || theoremCount == 0 then throwError "Missing production logical declarations"
  let mut coverageSet : NameSet := {}
  for entry in coverageNames do
    let name := entry.toName
    if coverageSet.contains name then throwError "Duplicate coverage declaration: {name}"
    coverageSet := coverageSet.insert name
    unless nameSet.contains name do throwError "Coverage declaration outside safe production modules: {name}"
    let some _ := env.checked.get.find? name |
      throwError "Coverage declaration is not kernel checked: {name}"
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
  let (_, bodyState) := (names.forM (Kimi003AuditInfrastructure.visit env)).run {}
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
    ("source_module_count", toJson modules.size), ("source_modules", toJson modules),
    ("modules_with_logical_declarations", toJson (observedModules.toArray.map Name.toString)),
    ("declaration_count", toJson names.size), ("theorem_count", toJson theoremCount),
    ("coverage_declaration_count", toJson coverageSet.size),
    ("unsafe_compiler_artifacts_excluded", toJson excludedUnsafe.size),
    ("excluded_unsafe_names", toJson excludedUnsafe),
    ("transitive_axioms", toJson (closure.toArray.map Name.toString)),
    ("independent_body_axioms", toJson (bodyAxioms.map Name.toString)),
    ("independent_body_visited", toJson bodyState.seen.size),
    ("declarations", Json.arr rows), ("per_declaration_axioms", Json.arr axiomRows)]
  liftIO (IO.println ("KERNEL_AUDIT_JSON:" ++ report.compress))
  logInfo m!"KERNEL AUDIT PASSED: {names.size} safe production declarations, {theoremCount} theorems, {modules.size} imported modules"
