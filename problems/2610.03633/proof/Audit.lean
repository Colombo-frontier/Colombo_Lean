import PolishedCertification
import Lean.Util.CollectAxioms
import Lean.Data.Json

/-! Audit trusted metaprogram, not mathematical source. Module ownership
comes from Lean's imported environment; every audited proof is read from
its checked kernel environment. One shared visited set traverses the whole
axiom graph once, including generated/private project theorem constants. -/
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificationAudit
open Lean Elab Command

private def need {α : Type} (result : Except String α) : CommandElabM α :=
  match result with
  | .ok x => pure x
  | .error e => throwError "Invalid proof manifest: {e}"

private def field (j : Json) (key : String) : CommandElabM Json := need (j.getObjVal? key)
private def arr (j : Json) : CommandElabM (Array Json) := need j.getArr?
private def str (j : Json) : CommandElabM String := need j.getStr?
private def nameOf (s : String) : Name := (s.splitOn ".").foldl Name.str Name.anonymous
private def owner (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive_or_structure"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

run_cmd do
  let env ← getEnv
  let source ← need (Json.parse (← IO.FS.readFile "proof/source-fingerprints.json"))
  let declarations ← need (Json.parse (← IO.FS.readFile "proof/declarations.json"))
  let moduleRows ← arr (← field source "math_modules")
  let mappedRows ← arr (← field declarations "declarations")
  let claimRows ← arr (← field declarations "claims")
  unless moduleRows.size == 1694 && mappedRows.size == 265 && claimRows.size == 55 do
    throwError "Unexpected audit manifest counts: modules={moduleRows.size}, declarations={mappedRows.size}, claims={claimRows.size}"
  let mut modules : NameSet := {}
  let mut moduleNames : Array Name := #[]
  let mut ownPrefixes : NameSet := {}
  for row in moduleRows do
    let m := nameOf (← str (← field row "module"))
    if modules.contains m then throwError "Duplicate mathematical module {m}"
    unless env.header.moduleNames.contains m do throwError "Mathematical module was not imported: {m}"
    modules := modules.insert m
    ownPrefixes := ownPrefixes.insert m.getRoot
    moduleNames := moduleNames.push m
  -- No untracked project module can enter through an extra prebuilt import.
  for m in env.header.moduleNames do
    if ownPrefixes.contains m.getRoot && !modules.contains m then
      throwError "Imported project module missing from source fingerprint map: {m}"
  let mut roots : Array Name := #[]
  let mut theoremNames : Array Name := #[]
  let mut localAxioms : Array Name := #[]
  let mut projectConstants := 0
  let mut compilerArtifacts := 0
  let mut compilerAxioms := 0
  let mut moduleTheorems : Std.HashMap Name Nat := {}
  let mut moduleConstants : Std.HashMap Name Nat := {}
  let mut moduleCompiler : Std.HashMap Name Nat := {}
  let checked := env.checked.get
  for (n, info) in env.constants.toList do
    if let some m := owner env n then
      if modules.contains m then
        projectConstants := projectConstants + 1
        moduleConstants := moduleConstants.insert m ((moduleConstants[m]?).getD 0 + 1)
        match info with
        | .axiomInfo _ =>
          -- Native code generation inserts unsafe implementation placeholders
          -- in the environment (including its checked view). Such unsafe
          -- implementation declarations cannot be used in safe proofs. They
          -- are counted separately; every safe axiom and every unexpected
          -- axiom reachable from a theorem/mapped declaration is rejected.
          if info.isUnsafe then
            compilerAxioms := compilerAxioms + 1
          else
            localAxioms := localAxioms.push n
        | _ => pure ()
        if info.isUnsafe then
          -- Lean may generate unsafe compiler-only implementations. They are
          -- never counted as kernel proofs and cannot be mapped declarations.
          compilerArtifacts := compilerArtifacts + 1
          moduleCompiler := moduleCompiler.insert m ((moduleCompiler[m]?).getD 0 + 1)
        else
          unless (checked.find? n).isSome do throwError "Project declaration is not kernel checked: {n}"
        if info.isTheorem then
          unless (checked.find? n).isSome do throwError "Theorem is not in checked kernel environment: {n}"
          theoremNames := theoremNames.push n
          roots := roots.push n
          moduleTheorems := moduleTheorems.insert m ((moduleTheorems[m]?).getD 0 + 1)
  unless localAxioms.isEmpty do throwError "Custom local axiom declarations: {localAxioms}"
  unless !theoremNames.isEmpty do throwError "No project theorem constants were found"
  let mut mapped : Array Json := #[]
  let mut mappedNames : NameSet := {}
  for row in mappedRows do
    let n := nameOf (← str (← field row "name"))
    let expected := nameOf (← str (← field row "module"))
    if mappedNames.contains n then throwError "Duplicate mapped declaration {n}"
    mappedNames := mappedNames.insert n
    unless modules.contains expected do throwError "Mapped owner is not a mathematical project module: {n}"
    let some info := checked.find? n | throwError "Mapped declaration does not exist in checked kernel environment: {n}"
    let some actual := owner env n | throwError "Mapped declaration has no imported module ownership: {n}"
    unless actual == expected do throwError "Mapped declaration owner mismatch: {n}, expected {expected}, got {actual}"
    if info.isUnsafe then throwError "Unsafe compiler artifact cannot be a mapped mathematical declaration: {n}"
    match info with
    | .axiomInfo _ => throwError "Mapped declaration is an unproved axiom: {n}"
    | _ => pure ()
    roots := roots.push n
    mapped := mapped.push (Json.mkObj [
      ("name", Json.str n.toString), ("module", Json.str actual.toString),
      ("kind", Json.str (kind info)), ("kernel_checked", Json.bool true)])
  -- Official collector, one shared state across every local theorem and all
  -- explicitly mapped definitions/structures. It reads checked kernel terms.
  let mut closure : Lean.CollectAxioms.State := {}
  for n in roots do
    let (_, next) := ((Lean.CollectAxioms.collect n).run env).run closure
    closure := next
  let unexpected := closure.axioms.filter (fun n =>
    n != `propext && n != `Classical.choice && n != `Quot.sound)
  unless unexpected.isEmpty do throwError "Nonstandard transitive axiom union: {unexpected}"
  let mut visited := 0
  for _ in closure.visited do visited := visited + 1
  let moduleCounts := moduleNames.map (fun m => Json.mkObj [
    ("module", Json.str m.toString),
    ("constants", toJson ((moduleConstants[m]?).getD 0)),
    ("theorems", toJson ((moduleTheorems[m]?).getD 0)),
    ("unsafe_compiler_artifacts", toJson ((moduleCompiler[m]?).getD 0))])
  let result := Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("passed", Json.bool true),
    ("math_modules_loaded", toJson moduleRows.size),
    ("project_constants", toJson projectConstants),
    ("project_theorems", toJson theoremNames.size),
    ("private_and_generated_theorems_included", Json.bool true),
    ("mapped_declarations", toJson mappedRows.size), ("claims", toJson claimRows.size),
    ("unsafe_compiler_artifacts", toJson compilerArtifacts),
    ("unsafe_compiler_axiom_artifacts", toJson compilerAxioms),
    ("visited_constants", toJson visited),
    ("local_axioms", Json.arr #[]),
    ("axioms", Json.arr (closure.axioms.map (fun n => Json.str n.toString))),
    ("module_counts", Json.arr moduleCounts), ("mapped", Json.arr mapped),
    ("scope", Json.str "All project theorem constants, including generated/private, plus mapped definitions/structures; checked kernel ownership; shared official CollectAxioms traversal.")]
  IO.FS.writeFile "proof/axiom-audit.json" (result.pretty ++ "\n")
  IO.println ("AUDIT_JSON " ++ result.compress)
  IO.println s!"AUDIT PASSED: {moduleRows.size} modules; {theoremNames.size} project theorems; {mappedRows.size} mapped declarations; standard axiom union only."

end CertificationAudit
