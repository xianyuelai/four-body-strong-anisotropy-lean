import Paper
import Lean
import Lean.Util.CollectAxioms

/-!
Environment audit instrumentation, not a mathematical proof.
This intentionally remains a legacy (non `module`) file: Lean 4.33.1's
environment header says that this loads all imported private module data.
Declaration selection uses the imported module index, never namespace names.
The Python preparation step supplies the exact local source-module inventory.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open Lean Elab Command Meta

namespace FourBodyAudit

def nameJson (n : Name) : Json :=
  Json.mkObj [("name", toJson n.toString), ("repr", toJson (reprStr n))]

def levelJson : Level → Json
  | .zero => Json.mkObj [("tag", toJson "zero")]
  | .succ l => Json.mkObj [("tag", toJson "succ"), ("arg", levelJson l)]
  | .max l r => Json.mkObj [("tag", toJson "max"), ("left", levelJson l),
      ("right", levelJson r)]
  | .imax l r => Json.mkObj [("tag", toJson "imax"), ("left", levelJson l),
      ("right", levelJson r)]
  | .param n => Json.mkObj [("tag", toJson "param"), ("name", nameJson n)]
  | .mvar n => Json.mkObj [("tag", toJson "mvar"), ("name", nameJson n.name)]

/-- Lossless semantic type AST; source metadata is omitted. -/
def exprJson : Expr → Json
  | .bvar i => Json.mkObj [("tag", toJson "bvar"), ("index", toJson i)]
  | .fvar i => Json.mkObj [("tag", toJson "fvar"), ("name", nameJson i.name)]
  | .mvar i => Json.mkObj [("tag", toJson "mvar"), ("name", nameJson i.name)]
  | .sort l => Json.mkObj [("tag", toJson "sort"), ("level", levelJson l)]
  | .const n ls => Json.mkObj [("tag", toJson "const"), ("name", nameJson n),
      ("levels", toJson (ls.toArray.map levelJson))]
  | .app f a => Json.mkObj [("tag", toJson "app"), ("fn", exprJson f),
      ("arg", exprJson a)]
  | .lam n t b bi => Json.mkObj [("tag", toJson "lam"), ("binder", nameJson n),
      ("binderInfo", toJson (reprStr bi)), ("domain", exprJson t), ("body", exprJson b)]
  | .forallE n t b bi => Json.mkObj [("tag", toJson "forall"), ("binder", nameJson n),
      ("binderInfo", toJson (reprStr bi)), ("domain", exprJson t), ("body", exprJson b)]
  | .letE n t v b nonDep => Json.mkObj [("tag", toJson "let"),
      ("binder", nameJson n), ("type", exprJson t), ("value", exprJson v),
      ("body", exprJson b), ("nonDependent", toJson nonDep)]
  | .lit (.natVal n) => Json.mkObj [("tag", toJson "nat"), ("value", toJson n)]
  | .lit (.strVal s) => Json.mkObj [("tag", toJson "string"), ("value", toJson s)]
  | .mdata _ b => exprJson b
  | .proj n i b => Json.mkObj [("tag", toJson "proj"), ("typeName", nameJson n),
      ("index", toJson i), ("arg", exprJson b)]

def allowedAxiom (n : Name) : Bool :=
  n == ``Classical.choice || n == ``propext || n == ``Quot.sound

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotientPrimitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Imported declarations are assigned by module index, including private names. -/
def owningModule (env : Environment) (currentSourceModule : Name) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i]!
  | none => currentSourceModule

/-- Two exact compiler-generated recursion implementations of the read-only
JSON serializers. They are instrumentation, never mathematical roots.
The names, owner, declaration kind and complete function type must match;
unsafe declarations and all mathematical partial declarations remain denied. -/
def generatedSerializerImplementation (n : Name) (ci : ConstantInfo) : Bool :=
  if ci.isUnsafe || !ci.isPartial then false else
  match ci with
  | .defnInfo _ =>
    match ci.type with
    | .forallE _ domain body .default =>
      body == mkConst ``Lean.Json &&
        ((n == `FourBodyAudit.exprJson._unsafe_rec && domain == mkConst ``Lean.Expr) ||
         (n == `FourBodyAudit.levelJson._unsafe_rec && domain == mkConst ``Lean.Level))
    | _ => false
  | _ => false

def readStringArray (j : Json) (key : String) : Except String (Array String) := do
  let a ← (← j.getObjVal? key).getArr?
  a.mapM Json.getStr?

def prettyOptions (opts : Options) : Options :=
  opts.setBool `pp.all true |>.setBool `pp.fullNames true |>.setBool `pp.universes true
    |>.setBool `pp.notation false |>.setBool `pp.proofs true |>.setBool `pp.deepTerms true
    |>.set `pp.maxSteps (1000000 : Nat) |>.set `format.width (160 : Nat)

/-- Adapted from the already implemented traversal in the authorized old
project's Audit/Environment.lean. It reads actual checked types and bodies,
independently of collectAxioms' imported summary extension. Instrumentation
is audited separately; these roots are all mathematical local declarations. -/
def checkedTrustClosure (env : Environment) (seeds : Array Name) : CommandElabM Json := do
  let kernelEnv := env.checked.get
  let mut todo := seeds
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  let mut edges : Nat := 0
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := kernelEnv.find? name
      | throwError "Missing reachable checked declaration: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial reachable mathematical declaration: {name}"
    if let .axiomInfo _ := info then
      unless allowedAxiom name do
        throwError "Disallowed reachable checked axiom: {name}"
      axioms := axioms.insert name
    if let .thmInfo _ := info then
      if (info.value? true).isNone then
        throwError "Reachable theorem body unavailable: {name}"
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? true then
      deps := deps ++ value.getUsedConstants
    if let .inductInfo ind := info then
      deps := deps ++ ind.ctors.toArray
    edges := edges + deps.size
    todo := todo ++ deps
  return Json.mkObj [
    ("passed", toJson true),
    ("method", toJson "actual checked types and bodies; no cached axiom summary"),
    ("mathematical_roots", toJson (seeds.map Name.toString)),
    ("reachable_constant_count", toJson seen.size),
    ("dependency_edges", toJson edges),
    ("axioms", toJson (axioms.toArray.qsort Name.lt |>.map Name.toString))]

def auditEnvironment (input : Json) : CommandElabM Json := do
  let localModules ← match readStringArray input "local_modules" with
    | .ok ms => pure ms
    | .error e => throwError "audit input: {e}"
  let inputSnapshot ← match input.getObjVal? "source_snapshot_sha256" >>= Json.getStr? with
    | .ok s => pure s
    | .error e => throwError "audit input: {e}"
  -- With the supported `lake env lean Audit.lean` invocation, Lean 4.33.1
  -- reports `_stdin` for the current frontend module. Imported ownership
  -- indices remain genuine. The launcher binds this exact current source
  -- file to the source snapshot and supplies its explicit inventory name.
  let currentSourceName ← match input.getObjVal? "audit_source_module" >>= Json.getStr? with
    | .ok s => pure s
    | .error e => throwError "audit input: {e}"
  let currentSourceModule := currentSourceName.toName
  let env := (← getEnv).setExporting false
  let importedModules := env.header.moduleNames.map Name.toString
  let missingModules := localModules.filter fun m =>
    m != currentSourceName && !importedModules.contains m
  let localConstants := env.checked.get.constants.toList.toArray.filter fun (n, _) =>
    localModules.contains (owningModule env currentSourceModule n).toString
  let localConstants := localConstants.qsort fun a b => Name.lt a.1 b.1
  let mathSeeds := localConstants.filterMap fun (n, _) =>
    if owningModule env currentSourceModule n == currentSourceModule then none else some n
  let checkedClosure ← checkedTrustClosure env mathSeeds
  -- Compiler ownership maps also contain code-only helpers which have no
  -- kernel ConstantInfo. List them explicitly; do not claim to audit a
  -- nonexistent mathematical declaration/type for these native-code entries.
  let codeOnlyNames := env.const2ModIdx.toList.filterMap fun (n, _) =>
    if localModules.contains (owningModule env currentSourceModule n).toString && (env.find? n).isNone then
      some <| Json.mkObj [("name", toJson n.toString),
        ("module", toJson (owningModule env currentSourceModule n).toString),
        ("reason", toJson "compiler ownership entry without kernel ConstantInfo")]
    else none
  let mut rows : Array Json := #[]
  let mut violations : Array String := #[]
  for (n, ci) in localConstants do
    let auditSerializer := owningModule env currentSourceModule n == currentSourceModule &&
      generatedSerializerImplementation n ci
    let axs ← collectAxioms n
    let forbidden := axs.filter fun ax => !allowedAxiom ax
    if !forbidden.isEmpty then
      violations := violations.push s!"{n}: forbidden transitive axioms {forbidden}"
    if declarationKind ci == "axiom" then
      violations := violations.push s!"{n}: locally declared axiom"
    if ci.type.hasMVar || ci.type.hasFVar then
      violations := violations.push s!"{n}: open variable in declaration type"
    if ci.isUnsafe || (ci.isPartial && !auditSerializer) then
      violations := violations.push s!"{n}: unsafe/partial local declaration"
    let pretty ← liftTermElabM <| withOptions prettyOptions do
      return (← Meta.ppExpr ci.type).pretty
    let definitionValue := match ci with
      | .defnInfo v => exprJson v.value
      | _ => Json.null
    rows := rows.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("name_repr", toJson (reprStr n)),
      ("module", toJson (owningModule env currentSourceModule n).toString),
      ("kind", toJson (declarationKind ci)),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("type_pretty", toJson pretty),
      ("type_expr", exprJson ci.type),
      ("definition_value_expr", definitionValue),
      ("proof_body_available", toJson (ci.value? true |>.isSome)),
      ("axioms", toJson (axs.map Name.toString)),
      ("forbidden_axioms", toJson (forbidden.map Name.toString)),
      ("unsafe", toJson ci.isUnsafe),
      ("partial", toJson ci.isPartial),
      ("audit_serialization_helper", toJson auditSerializer)]
  return Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("scope", toJson "all local constants selected by module ownership, including audit instrumentation"),
    ("source_snapshot_sha256", toJson inputSnapshot),
    ("main_module", toJson env.header.mainModule.toString),
    ("audit_source_module", toJson currentSourceName),
    ("legacy_import_all", toJson (!env.header.isModule)),
    ("local_modules", toJson localModules),
    ("imported_modules", toJson importedModules),
    ("missing_local_modules", toJson missingModules),
    ("declaration_count", toJson rows.size),
    ("declarations", toJson rows),
    ("actual_checked_mathematical_dependency_closure", checkedClosure),
    ("non_kernel_generated_ownership_entries", toJson codeOnlyNames),
    ("violations", toJson violations),
    ("passes_axiom_audit", toJson (violations.isEmpty && missingModules.isEmpty))]

end FourBodyAudit

run_cmd do
  let inputText ← IO.FS.readFile "audit-input.json"
  let input ← match Json.parse inputText with
    | .ok j => pure j
    | .error e => throwError "audit-input.json: {e}"
  let result ← FourBodyAudit.auditEnvironment input
  IO.FS.writeFile "environment-audit.json" (result.compress ++ "\n")
  match result.getObjVal? "passes_axiom_audit" >>= Json.getBool? with
  | .ok true => logInfo "Environment axiom audit passed; paper completion is checked separately."
  | _ => throwError "Environment axiom audit failed; see environment-audit.json"
