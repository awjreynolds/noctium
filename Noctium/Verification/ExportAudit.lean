import Noctium.Verification
import Lean.Replay
import LeanExport.Parse

namespace Noctium.Verification.ExportAudit
open Lean

private def load (path : System.FilePath) : IO LeanExport.ExportedEnv := do
  let metadata ← path.metadata
  unless metadata.byteSize ≤ 64 * 1024 * 1024 do
    throw <| IO.userError "export_limit"
  IO.FS.withFile path .read fun handle => LeanExport.parseStream (.ofHandle handle)

private def mergeModel (model candidate : Std.HashMap Name ConstantInfo) :
    Except String (Std.HashMap Name ConstantInfo) := do
  let mut result := candidate
  for (name, trusted) in model.toList do
    if let some supplied := candidate[name]? then
      unless supplied == trusted do throw s!"model_declaration_mismatch: {name}"
    result := result.insert name trusted
  return result

private def replay (constants : Std.HashMap Name ConstantInfo) : IO Environment := do
  let primitiveMembers := [`Quot.mk, `Quot.lift, `Quot.ind]
  let input := primitiveMembers.foldl (fun map name => map.erase name) constants
  let checked ← (← mkEmptyEnvironment).toKernelEnv.replay input
  for name in `Quot :: primitiveMembers do
    if let some supplied := constants[name]? then
      unless checked.find? name == some supplied do
        throw <| IO.userError "quotient_declaration_mismatch"
  return .ofKernelEnv checked

private def roleName : Audit.Role → String
  | .functional => "functional"
  | .privacy => "privacy"

private def roleRecordJson (registration : Audit.Registration) : Json :=
  Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)),
    ("role", toJson (roleName registration.role)),
    ("obligation", toJson registration.role.obligation.toString),
    ("policy", toJson registration.policy.toString),
    ("proof", toJson registration.proof.toString),
    ("axioms", toJson (registration.axioms.toList.map Name.toString))]

private def checked (environment : Environment) (policy proof : Name) (role : Audit.Role) : IO Audit.Registration :=
  match Audit.check environment policy proof role with
  | .ok result => pure result
  | .error error => do
    if error == "unknown_proof" then
      throw <| IO.userError s!"unknown_proof: {roleName role}"
    else if error == "wrong_obligation" then
      throw <| IO.userError s!"wrong_obligation: {roleName role}"
    else
      throw <| IO.userError error

private def parseName (text : String) : IO Name :=
  match Syntax.decodeNameLit ("`" ++ text) with
  | some name => if name.isAnonymous then throw <| IO.userError "invalid_name" else pure name
  | none => throw <| IO.userError "invalid_name"

private def pretty (environment : Environment) (expression : Lean.Expr) : IO String := do
  let options := ({} : Options).setBool `pp.fullNames true |>.setBool `pp.explicit true
  -- A fresh kernel environment has no candidate syntax/formatter metadata.
  -- Numeral syntax, for example rawNatLit, need not exist in the model closure.
  try
    return (← PrettyPrinter.ppExprLegacy environment {} {} options expression).pretty
  catch _ => return "kernel-expression: " ++ toString expression

private def reduced (environment : Environment) (expression : Lean.Expr) : IO Lean.Expr :=
  match Kernel.whnf environment {} expression with
  | .ok result => pure result
  | .error _ => throw <| IO.userError "policy_projection_failed"

private def operationName (environment : Environment) (policy : Name) : IO (Option String) := do
  let policyExpr := mkConst policy
  let subject := mkApp (mkConst ``AuditPolicy.subject) policyExpr
  let contract ← reduced environment (mkApp (mkConst ``Subject.contract) subject)
  let entry ← reduced environment (mkApp (mkConst ``Subject.entry) subject)
  let contractName ← reduced environment (mkApp (mkConst ``Contract.name) contract)
  let entryName ← reduced environment (mkApp (mkConst ``Entrypoint.name) entry)
  match contractName, entryName with
  | .lit (.strVal contractName), .lit (.strVal entryName) => pure (some s!"{contractName}.{entryName}")
  | _, _ => pure none

private def definitionView (environment : Environment) (expression : Lean.Expr) : IO Json := do
  let mut fields := [
    ("term", toJson (← pretty environment expression)),
    ("headNormalForm", toJson (← pretty environment (← reduced environment expression))),
    ("machineIdentity", toJson ("declarations and expressions in the externally pinned model export" : String))]
  if let some name := expression.getAppFn.constName? then
    if let some info := environment.toKernelEnv.find? name then
      fields := fields ++ [("rootDeclaration", toJson name.toString),
        ("rootType", toJson (← pretty environment info.type))]
      if let some value := info.value? (allowOpaque := true) then
        fields := fields ++ [("rootBody", toJson (← pretty environment value)),
          ("dependencies", toJson (value.getUsedConstants.toList.map Name.toString))]
  return Json.mkObj fields

private def descriptions (environment : Environment) (policy : Name) : IO Json := do
  let policyExpr := mkConst policy
  let subject := mkApp (mkConst ``AuditPolicy.subject) policyExpr
  let spec := mkApp (mkConst ``Subject.specification) subject
  let body ← reduced environment spec
  let args := body.getAppArgs
  unless body.getAppFn.constName? == some ``Specification.mk && args.size == 5 do
    throw <| IO.userError "specification_must_be_inspectable"
  let privacy := mkApp (mkConst ``AuditPolicy.privacy) policyExpr
  let release ← reduced environment (mkApp (mkConst ``PrivacySpec.releases) privacy)
  let scope ← reduced environment (mkApp (mkConst ``PrivacySpec.scope) privacy)
  let releaseKind := if release.getAppFn.constName? == some ``ReleasePolicy.none then "none"
    else if release.getAppFn.constName? == some ``ReleasePolicy.declared then "declared-function-unlinked-to-source-authorization"
    else "uninspectable"
  let scopeName := if scope.constName? == some ``ObservationScope.successfulOnly then "successful-only-under-pinned-precondition"
    else if scope.constName? == some ``ObservationScope.allOutcomes then "all-outcomes-under-pinned-precondition"
    else "uninspectable"
  if releaseKind == "uninspectable" || scopeName == "uninspectable" then
    throw <| IO.userError "privacy_policy_must_be_inspectable"
  return Json.mkObj [
    ("initial", ← definitionView environment args[0]!),
    ("invariant", ← definitionView environment args[1]!),
    ("precondition", ← definitionView environment args[2]!),
    ("enabled", ← definitionView environment args[3]!),
    ("postcondition", ← definitionView environment args[4]!),
    ("releasePolicy", toJson releaseKind),
    ("releaseDefinition", ← definitionView environment
      (if releaseKind == "none" then release else release.getAppArgs[0]!)),
    ("privacyScope", toJson scopeName),
    ("publicObserver", toJson ("source public outputs and final public LedgerState; errors only within selected scope" : String)),
    ("publicEquivalence", toJson ("declared public inputs in declaration order, identical public state and EvalContext" : String)),
    ("privacyDomain", toJson ("exact pinned functional invariant and precondition; invalid/ineligible attempts are not implied covered" : String))]

/-- Parses data and replays declarations. It never imports candidate modules or runs
their initializers. The external caller must authenticate the trusted model file. -/
def run (args : List String) : IO UInt32 := do
  try
    let (modelPath, proofPath, policyText, functionalText, privacyText) ←
      match args with
      | [model, proof, policy, functional] => pure (model, proof, policy, functional, none)
      | [model, proof, policy, functional, privacy] => pure (model, proof, policy, functional, some privacy)
      | _ => throw <| IO.userError "usage: AuditExport MODEL.ndjson PROOFS.ndjson POLICY FUNCTIONAL_PROOF [PRIVACY_PROOF]"
    let model ← load modelPath
    let candidate ← load proofPath
    let policyName ← parseName policyText
    let functionalName ← parseName functionalText
    for name in Audit.approvedAxioms do
      unless model.constMap.contains name do throw <| IO.userError "missing_foundational_model_declaration"
    for name in [``FunctionalObligation, ``PrivacyObligation, policyName] do
      unless model.constMap.contains name do throw <| IO.userError "missing_trusted_model_root"
    let merged ← match mergeModel model.constMap candidate.constMap with
      | .ok result => pure result
      | .error error => throw <| IO.userError error
    let environment ← replay merged
    let operation ← try operationName environment policyName catch _ => pure none
    let functional ← checked environment policyName functionalName .functional
    let mut proofRoles := #[functional]
    if let some privacy := privacyText then
      let result ← checked environment policyName (← parseName privacy) .privacy
      proofRoles := proofRoles.push result
    let allAxioms := proofRoles.toList.flatMap (·.axioms.toList)
    let scope ← descriptions environment policyName
    IO.println <| (Json.mkObj [
      ("status", toJson (if privacyText.isSome then "source-functional-and-scoped-privacy-checked" else "source-functional-only")),
      ("sourceFunctionalChecked", toJson true),
      ("sourcePrivacyChecked", toJson privacyText.isSome),
      ("operation", toJson operation),
      ("policy", toJson policyText), ("functionalProof", toJson functionalText),
      ("privacyProof", toJson privacyText),
      ("proofRoles", toJson (proofRoles.map roleRecordJson)),
      ("axioms", toJson ((allAxioms.eraseDups.mergeSort Name.lt).map Name.toString)),
      ("specification", scope),
      ("externalModelPinRequired", toJson true),
      ("specificationReviewVerified", toJson false),
      ("sourceAuthorizationCorrespondenceProved", toJson false),
      ("compiledContractVerified", toJson false),
      ("remainingGates", toJson (["native preservation", "exact artifact certificate", "deployed identity", "reviewed privacy/native observation correspondence"] : List String))]).compress
    return 0
  catch error =>
    IO.eprintln <| (Json.mkObj [("status", toJson ("rejected" : String)),
      ("error", toJson (toString error))]).compress
    return 1

end Noctium.Verification.ExportAudit
