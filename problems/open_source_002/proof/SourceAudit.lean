import Main
import Lean

/- Current audit of the frozen list of 1,236 original theorem names.
   This uses ConstantInfo directly; pretty-printer prefixes such as @[defeq]
   have no effect on whether a declaration is a proved theorem. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let text ← liftIO (IO.FS.readFile "../proof/declarations.json")
  let json ← match Json.parse text with
    | .ok value => pure value
    | .error message => throwError "Invalid theorem inventory JSON: {message}"
  let entries ← match (fromJson? json : Except String (Array String)) with
    | .ok value => pure value
    | .error message => throwError "Invalid theorem inventory: {message}"
  unless entries.size == 1236 do throwError "Expected 1236 original theorem names"
  let mut seen : NameSet := {}
  let mut closure : NameSet := {}
  let mut rows : Array Json := #[]
  for entry in entries do
    let name := entry.toName
    if seen.contains name then throwError "Duplicate original theorem: {name}"
    seen := seen.insert name
    let some info := env.checked.get.find? name |
      throwError "Original theorem is absent from the kernel-checked environment: {name}"
    let .thmInfo thm := info | throwError "Original declaration is not thmInfo: {name}"
    if info.isUnsafe || thm.type.hasExprMVar || thm.type.hasFVar ||
        thm.value.hasExprMVar || thm.value.hasFVar then
      throwError "Unsafe or open theorem/proof: {name}"
    let moduleName := (env.getModuleIdxFor? name |>.map
      (fun i => env.header.moduleNames[i.toNat]!)).getD Name.anonymous
    unless moduleName == `Main do throwError "Original theorem has unexpected module origin: {name}"
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "Unexpected theorem axiom: {name}: {axioms}"
    for ax in axioms do closure := closure.insert ax
    rows := rows.push (Json.mkObj [
      ("name", toJson entry), ("module", toJson moduleName.toString),
      ("declaration_kind", toJson "thmInfo"), ("has_proof_value", toJson true),
      ("axioms", toJson (axioms.map Name.toString))])
  let report := Json.mkObj [
    ("status", toJson "passed"), ("audit_kind", toJson "original_named_theorems"),
    ("declaration_count", toJson rows.size), ("theorem_count", toJson rows.size),
    ("transitive_axioms", toJson (closure.toArray.map Name.toString)),
    ("declarations", Json.arr rows)]
  liftIO (IO.println ("SOURCE_AUDIT_JSON:" ++ report.compress))
  logInfo m!"SOURCE AUDIT PASSED: {rows.size} original theorems have kernel proof values"
