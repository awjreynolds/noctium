import Noctium.Semantics
import Lean

namespace Noctium.Verification

/-- These predicates are the reviewed specification, not inferred business intent. -/
structure Specification where
  initial : LedgerState → Prop
  invariant : LedgerState → Prop
  precondition : EvalContext → EvalEnv → LedgerState → Prop
  enabled : EvalContext → EvalEnv → LedgerState → Prop
  postcondition : EvalContext → EvalEnv → LedgerState → EvalEnv → LedgerState → Prop

/-- A finite index binds the obligation to an actual source contract entrypoint. -/
structure Subject where
  contract : Contract
  entrypoint : Fin contract.entrypoints.length
  specification : Specification

def Subject.entry (subject : Subject) : Entrypoint :=
  subject.contract.entrypoints[subject.entrypoint]

structure Correctness (subject : Subject) : Prop where
  initialization : ∀ before, subject.specification.initial before →
    subject.specification.invariant before
  preservation : ∀ ctx inputs before outputs after,
    subject.specification.invariant before →
    subject.specification.precondition ctx inputs before →
    subject.entry.run ctx inputs before = .ok (outputs, after) →
    subject.specification.postcondition ctx inputs before outputs after ∧
      subject.specification.invariant after
  progress : ∀ ctx inputs before,
    subject.specification.invariant before →
    subject.specification.precondition ctx inputs before →
    subject.specification.enabled ctx inputs before →
    ∃ outputs after, subject.entry.run ctx inputs before = .ok (outputs, after)
  nonvacuity : ∃ ctx inputs before,
    subject.specification.initial before ∧
    subject.specification.precondition ctx inputs before ∧
    subject.specification.enabled ctx inputs before

structure Invocation where
  context : EvalContext
  inputs : EvalEnv
  state : LedgerState

abbrev Outcome := Except String (EvalEnv × LedgerState)

def Subject.execute (subject : Subject) (invocation : Invocation) : Outcome :=
  subject.entry.run invocation.context invocation.inputs invocation.state

inductive ObservationScope where
  | successfulOnly
  | allOutcomes
  deriving Repr, BEq, DecidableEq

def ObservationScope.covers (scope : ObservationScope) (left right : Outcome) : Prop :=
  match scope with
  | .allOutcomes => True
  | .successfulOnly =>
    (∃ outputs state, left = .ok (outputs, state)) ∧
    (∃ outputs state, right = .ok (outputs, state))

def Subject.publicInputs (subject : Subject) (inputs : EvalEnv) : List (String × Option Value) :=
  (subject.entry.circuit.inputs.filter (·.visibility == .«public»)).map fun input =>
    (input.name, inputs.lookup input.name)

def Subject.publicEquivalent (subject : Subject) (left right : Invocation) : Prop :=
  left.context = right.context ∧ left.state = right.state ∧
    subject.publicInputs left.inputs = subject.publicInputs right.inputs

def Subject.admissible (subject : Subject) (invocation : Invocation) : Prop :=
  subject.specification.invariant invocation.state ∧
    subject.specification.precondition invocation.context invocation.inputs invocation.state

/-- A declared function is an explicit release assumption, not a source-authorization
certificate. Its equality cannot be an always-false hand-written relation. -/
inductive ReleasePolicy where
  | none
  | declared (release : Invocation → List Value)

def ReleasePolicy.agrees (policy : ReleasePolicy) (left right : Invocation) : Prop :=
  match policy with
  | .none => True
  | .declared release => release left = release right

theorem ReleasePolicy.agrees_refl (policy : ReleasePolicy) (invocation : Invocation) :
    policy.agrees invocation invocation := by cases policy <;> simp [agrees]

theorem Subject.publicEquivalent_refl (subject : Subject) (invocation : Invocation) :
    subject.publicEquivalent invocation invocation := ⟨rfl, rfl, rfl⟩

structure PrivacySpec where
  releases : ReleasePolicy := .none
  scope : ObservationScope

def PrivacyCorrect (subject : Subject) (privacy : PrivacySpec) : Prop :=
  ∀ left right,
    subject.admissible left → subject.admissible right →
    subject.publicEquivalent left right →
    privacy.releases.agrees left right →
    privacy.scope.covers (subject.execute left) (subject.execute right) →
    subject.execute left = subject.execute right

/-- The external audit authority pins this definition and its dependency closure. -/
structure AuditPolicy where
  subject : Subject
  privacy : PrivacySpec
  functionalGuarantee : String
  privacyGuarantee : String

def FunctionalObligation (policy : AuditPolicy) : Prop := Correctness policy.subject
def PrivacyObligation (policy : AuditPolicy) : Prop := PrivacyCorrect policy.subject policy.privacy

namespace Audit
open Lean

inductive Role where
  | functional
  | privacy
  deriving Repr, BEq

def Role.obligation : Role → Name
  | .functional => ``FunctionalObligation
  | .privacy => ``PrivacyObligation

structure Registration where
  policy : Name
  proof : Name
  role : Role
  axioms : Array Name
  deriving Repr

def approvedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Walk actual checked bodies, including imports. Do not use imported axiom metadata. -/
partial def axiomsIn (environment : Environment) (root : Name) : Except String (Array Name) :=
  visit [root] {} #[]
where
  visit : List Name → NameSet → Array Name → Except String (Array Name)
    | [], _, found => .ok (found.qsort Name.lt)
    | name :: rest, seen, found => do
      if seen.contains name then return ← visit rest seen found
      let some info := environment.toKernelEnv.find? name
        | throw s!"unknown_dependency: {name}"
      if info.isUnsafe || info.isPartial then throw s!"unsafe_dependency: {name}"
      let seen := seen.insert name
      let dependencies := info.type.getUsedConstants.toList ++
        (info.value? (allowOpaque := true)).toList.flatMap (·.getUsedConstants.toList)
      match info with
      | .axiomInfo _ =>
        unless approvedAxioms.contains name do throw s!"forbidden_axiom: {name}"
        visit (dependencies ++ rest) seen (found.push name)
      | .inductInfo value => visit (value.ctors ++ dependencies ++ rest) seen found
      | _ => visit (dependencies ++ rest) seen found

/-- This checks proof type and axioms in a checked environment. The caller must first
bind model declarations to the independently trusted export and replay candidate terms. -/
def check (environment : Environment) (policy proof : Name) (role : Role) : Except String Registration := do
  let some policyInfo := environment.toKernelEnv.find? policy | throw "unknown_policy"
  unless policyInfo.levelParams.isEmpty do throw "polymorphic_policy"
  match Kernel.isDefEq environment {} policyInfo.type (mkConst ``AuditPolicy) with
  | .ok true => pure ()
  | _ => throw "wrong_policy_type"
  let some proofInfo := environment.toKernelEnv.find? proof | throw "unknown_proof"
  unless proofInfo.levelParams.isEmpty do throw "polymorphic_proof"
  let expected := mkApp (mkConst role.obligation) (mkConst policy)
  match Kernel.isDefEq environment {} proofInfo.type expected with
  | .ok true => pure ()
  | _ => throw "wrong_obligation"
  let axioms ← axiomsIn environment proof
  return {policy, proof, role, axioms}

end Audit

private def roleLabel : Audit.Role → String
  | .functional => "functional"
  | .privacy => "privacy"

open Lean Elab Command

initialize proofRegistry : SimplePersistentEnvExtension Audit.Registration (Array Audit.Registration) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

private def reduceDiagnosticProjection (environment : Environment)
    (expression : Lean.Expr) : Option Lean.Expr :=
  match Kernel.whnf environment {} expression with
  | .ok result => some result
  | .error _ => none

private def diagnosticNatLiteral (expression : Lean.Expr) : Option Nat := do
  match expression with
  | .lit (.natVal value) => some value
  | _ =>
    let (head, arguments) := expression.getAppFnArgs
    guard (head == ``OfNat.ofNat)
    guard (arguments.size == 3)
    guard (arguments[0]! == mkConst ``Nat)
    let .lit (.natVal value) := arguments[1]! | none
    let .app (.const `instOfNatNat _) (.lit (.natVal instanceValue)) := arguments[2]! | none
    guard (value == instanceValue)
    pure value

private def registrationOperation (environment : Environment) (policy : Name) :
    Option (String × Option SourceSpan) := do
  let policyExpr := mkConst policy
  let subject := mkApp (mkConst ``AuditPolicy.subject) policyExpr
  let contract ← reduceDiagnosticProjection environment
    (mkApp (mkConst ``Subject.contract) subject)
  let entry ← reduceDiagnosticProjection environment
    (mkApp (mkConst ``Subject.entry) subject)
  let contractName ← reduceDiagnosticProjection environment
    (mkApp (mkConst ``Contract.name) contract)
  let entryName ← reduceDiagnosticProjection environment
    (mkApp (mkConst ``Entrypoint.name) entry)
  let Lean.Expr.lit (.strVal contractName) := contractName | none
  let Lean.Expr.lit (.strVal entryName) := entryName | none
  let sourceSpan := do
    let span ← reduceDiagnosticProjection environment
      (mkApp (mkConst ``Entrypoint.span) entry)
    let fields := span.getAppArgs
    guard (fields.size == 3)
    let Lean.Expr.lit (.strVal file) := fields[0]! | none
    let line ← diagnosticNatLiteral fields[1]!
    let column ← diagnosticNatLiteral fields[2]!
    guard (!file.isEmpty)
    pure {file, line, column}
  return (s!"{contractName}.{entryName}", sourceSpan)

private def ppAuditType (expression : Lean.Expr) : CommandElabM Format :=
  liftTermElabM <| withOptions
    (fun options => options.setBool `pp.fullNames true |>.setBool `pp.explicit true)
    (Meta.ppExpr expression)

private def wrongObligationMessage (environment : Environment) (policy proof : Name)
    (role : Audit.Role) : CommandElabM MessageData := do
  let some proofInfo := environment.toKernelEnv.find? proof
    | return m!"wrong_obligation: unknown proof {proof}"
  let submitted ← ppAuditType proofInfo.type
  let expectedType := mkApp (mkConst role.obligation) (mkConst policy)
  let expected ← ppAuditType expectedType
  let (operation, sourceSpan) :=
    (registrationOperation environment policy).getD ("<unavailable>", none)
  let location := (sourceSpan.map fun span =>
    s!"\noperation source location: {span.file}:{span.line}:{span.column}").getD ""
  return m!"wrong_obligation: submitted proof '{proof}' has proposition:\n  {submitted}\nexpected {roleLabel role} proposition:\n  {expected}\ncontract/operation: {operation}{location}"

private def register (proof policy : TSyntax `ident) (role : Audit.Role) : CommandElabM Unit := do
  let proofName ← liftCoreM <| resolveGlobalConstNoOverload proof
  let policyName ← liftCoreM <| resolveGlobalConstNoOverload policy
  let environment ← getEnv
  match Audit.check environment policyName proofName role with
  | .error "wrong_obligation" =>
    throwErrorAt proof (← wrongObligationMessage environment policyName proofName role)
  | .error message => throwError "{message}"
  | .ok registration =>
    modifyEnv fun environment => proofRegistry.addEntry environment registration
    logInfo m!"provisional source {repr role} proof registered: {proofName}; external model pin and export replay required"

elab "#noctium_register_functional " proof:ident " for " policy:ident : command =>
  register proof policy .functional

elab "#noctium_register_privacy " proof:ident " for " policy:ident : command =>
  register proof policy .privacy

syntax (name := noctiumProofScaffoldCommand)
  "#noctium_proof_scaffold " ident " for " ident " on " ident
    " operation " str : command

private def proofScaffoldBody (role : Audit.Role) : String :=
  match role with
  | .functional =>
    "by\n  constructor\n  · intro before hInitial\n    exact ?_\n" ++
    "  · intro ctx inputs before outputs after hInvariant hPrecondition hRun\n    exact ?_\n" ++
    "  · intro ctx inputs before hInvariant hPrecondition hEnabled\n    exact ?_\n" ++
    "  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩"
  | .privacy =>
    "by\n  intro left right hLeftAdmissible hRightAdmissible hPublicEquivalent " ++
    "hReleaseAgreement hScope\n  exact ?_"

private def scaffoldTheorem (policy : Name)
    (role : Audit.Role) (opName : String) (entryIndexValue : Nat) : CommandElabM MessageData := do
  let conclusion ← ppAuditType <| mkApp (mkConst role.obligation) (mkConst policy)
  let theoremName := (policy ++ Name.str .anonymous s!"{roleLabel role}Scaffold").toString
  return m!"NOCTIUM_PROOF_SCAFFOLD\noperation: {opName} (entrypoint index {entryIndexValue})\ntheorem {theoremName} : {conclusion} := {proofScaffoldBody role}"

@[command_elab noctiumProofScaffoldCommand] unsafe def elabProofScaffold : CommandElab := fun stx => do
  match stx with
  | `(#noctium_proof_scaffold $roleSyntax:ident for $policySyntax:ident on $contractSyntax:ident
      operation $operationSyntax:str) => do
    let role ← match roleSyntax.getId.toString with
      | "functional" => pure Audit.Role.functional
      | "privacy" => pure Audit.Role.privacy
      | _ => throwErrorAt roleSyntax "proof_scaffold_role: expected functional or privacy"
    let policyName ← liftCoreM <| resolveGlobalConstNoOverload policySyntax
    let contractName ← liftCoreM <| resolveGlobalConstNoOverload contractSyntax
    let environment ← getEnv
    let some policyInfo := environment.toKernelEnv.find? policyName
      | throwErrorAt policySyntax "unknown_policy"
    unless policyInfo.levelParams.isEmpty do
      throwErrorAt policySyntax "polymorphic_policy"
    match Kernel.isDefEq environment {} policyInfo.type (mkConst ``AuditPolicy) with
    | .ok true => pure ()
    | _ => throwErrorAt policySyntax "wrong_policy_type"
    let policyValue ← evalConstCheck AuditPolicy ``AuditPolicy policyName
    let policyContract := mkApp (mkConst ``Subject.contract)
      (mkApp (mkConst ``AuditPolicy.subject) (mkConst policyName))
    match Kernel.isDefEq environment {} policyContract (mkConst contractName) with
    | .ok true => pure ()
    | _ => throwErrorAt contractSyntax
      "proof_scaffold_contract_mismatch: selected contract is not kernel-equal to the policy contract"
    let contractValue ← evalConstCheck Contract ``Contract contractName
    let matchingIndices := contractValue.entrypoints.zipIdx.filterMap fun (entry, entryIndex) =>
      if entry.name == operationSyntax.getString then some entryIndex else none
    unless matchingIndices.length == 1 do
      throwErrorAt operationSyntax
        (if matchingIndices.isEmpty then "proof_scaffold_operation_missing"
         else "proof_scaffold_operation_ambiguous")
    let some operationIndex := matchingIndices[0]? | throwError "proof_scaffold_operation_missing"
    unless policyValue.subject.entrypoint.val == operationIndex do
      throwErrorAt operationSyntax
        s!"proof_scaffold_policy_entrypoint_mismatch: policy selects index {policyValue.subject.entrypoint.val}, named operation is at index {operationIndex}"
    logInfo (← scaffoldTheorem policyName role
      s!"{contractValue.name}.{operationSyntax.getString}" operationIndex)
  | _ => throwUnsupportedSyntax

private def coverageRegistrationJson (registration : Audit.Registration) : Lean.Json :=
  Lean.Json.mkObj [
    ("policy", toJson registration.policy.toString),
    ("proof", toJson registration.proof.toString)]

private def distinctRegistrations (registrations : Array Audit.Registration) :
    Array Audit.Registration :=
  registrations.foldl (fun found registration =>
    if found.any (fun existing =>
        existing.policy == registration.policy && existing.proof == registration.proof &&
          existing.role == registration.role) then found
    else found.push registration) #[]

private def sourceCoverageRoleJson (role : Audit.Role)
    (registrations : Array Audit.Registration) : Lean.Json := Id.run do
  let distinct := distinctRegistrations registrations
  let status := if distinct.isEmpty then "missing"
    else if distinct.size > 1 then "ambiguous"
    else "covered"
  return Lean.Json.mkObj [
    ("role", toJson (roleLabel role)),
    ("status", toJson status),
    ("registrations", toJson (distinct.map coverageRegistrationJson)),
    ("duplicateRegistrationCount", toJson (registrations.size - distinct.size))]

private def coverageRoleStatus (role : Audit.Role) (entrypointIndex : Nat)
    (coverageMatches : Array (Nat × Audit.Registration)) : Array Audit.Registration :=
  coverageMatches.filterMap fun (index, registration) =>
    if index == entrypointIndex && registration.role == role then some registration else none

private def policyDefEq (environment : Environment) (left right : Name) : Bool :=
  match Kernel.isDefEq environment {} (mkConst left) (mkConst right) with
  | .ok true => true
  | _ => false

syntax (name := noctiumSourceProofCoverageCommand)
  "#noctium_source_proof_coverage " ident : command

@[command_elab noctiumSourceProofCoverageCommand] unsafe def elabSourceProofCoverage :
    CommandElab := fun stx => do
  match stx with
  | `(#noctium_source_proof_coverage $contractName:ident) => do
    let contractDeclaration ← liftCoreM <| resolveGlobalConstNoOverload contractName
    let contract ← evalConstCheck Contract ``Contract contractDeclaration
    let environment ← getEnv
    let mut coverageMatches : Array (Nat × Audit.Registration) := #[]
    let mut invalidRegistrations : Array Lean.Json := #[]
    for registration in proofRegistry.getState environment do
      match Audit.check environment registration.policy registration.proof registration.role with
      | .error message =>
        invalidRegistrations := invalidRegistrations.push <| Lean.Json.mkObj [
          ("policy", toJson registration.policy.toString),
          ("proof", toJson registration.proof.toString),
          ("role", toJson (roleLabel registration.role)),
          ("error", toJson message)]
      | .ok _ =>
        let policy := mkConst registration.policy
        let policySubject := mkApp (mkConst ``AuditPolicy.subject) policy
        let policyContract := mkApp (mkConst ``Subject.contract) policySubject
        let contractTerm := mkConst contractDeclaration
        match Kernel.isDefEq environment {} policyContract contractTerm with
        | .ok true =>
          let policyValue ← evalConstCheck AuditPolicy ``AuditPolicy registration.policy
          let index := policyValue.subject.entrypoint.val
          if index < contract.entrypoints.length then
            coverageMatches := coverageMatches.push (index, registration)
        | _ => pure ()
    let entryRows ← contract.entrypoints.zipIdx.mapM fun (entrypoint, index) => do
      let roles := [Audit.Role.functional, Audit.Role.privacy]
      let roleRegistrations := roles.map fun role =>
        (role, coverageRoleStatus role index coverageMatches)
      let roleRows := roleRegistrations.map fun (role, registrations) =>
        sourceCoverageRoleJson role registrations
      let functionalPolicies := (coverageRoleStatus .functional index coverageMatches)
        |> distinctRegistrations
      let privacyPolicies := (coverageRoleStatus .privacy index coverageMatches)
        |> distinctRegistrations
      let mut compatiblePolicyPairs : Array Lean.Json := #[]
      let mut mismatchedPolicyPairs : Array Lean.Json := #[]
      for functional in functionalPolicies do
        for privacy in privacyPolicies do
          let pair := Lean.Json.mkObj [
            ("functionalPolicy", toJson functional.policy.toString),
            ("privacyPolicy", toJson privacy.policy.toString)]
          if policyDefEq environment functional.policy privacy.policy then
            compatiblePolicyPairs := compatiblePolicyPairs.push pair
          else
            mismatchedPolicyPairs := mismatchedPolicyPairs.push pair
      let policyPairing := if functionalPolicies.isEmpty || privacyPolicies.isEmpty then "incomplete"
        else if compatiblePolicyPairs.isEmpty then "mismatch"
        else if functionalPolicies.size > 1 || privacyPolicies.size > 1 then "ambiguous"
        else "matched"
      let missing := roleRegistrations.filterMap fun (role, registrations) =>
        if distinctRegistrations registrations |>.isEmpty then some (roleLabel role) else none
      let ambiguous := roleRegistrations.filterMap fun (role, registrations) =>
        if (distinctRegistrations registrations).size > 1 then some (roleLabel role) else none
      let status := if !ambiguous.isEmpty then "ambiguous"
        else if policyPairing == "mismatch" then "policy-mismatch"
        else if policyPairing == "ambiguous" then "ambiguous"
        else if !missing.isEmpty then "incomplete"
        else "covered"
      pure (status, Lean.Json.mkObj [
        ("index", toJson index),
        ("entrypoint", toJson entrypoint.name),
        ("status", toJson status),
        ("roles", toJson roleRows),
        ("policyPairing", toJson policyPairing),
        ("compatiblePolicyPairs", toJson compatiblePolicyPairs),
        ("mismatchedPolicyPairs", toJson mismatchedPolicyPairs),
        ("missingRoles", toJson missing),
        ("ambiguousRoles", toJson ambiguous)])
    let overallStatus := if entryRows.isEmpty then "no-entrypoints"
      else if entryRows.any (·.1 == "ambiguous") then "ambiguous"
      else if entryRows.any (·.1 == "policy-mismatch") then "policy-mismatch"
      else if entryRows.any (·.1 == "incomplete") then "incomplete"
      else "covered"
    let report := Lean.Json.mkObj [
      ("schemaVersion", toJson (1 : Nat)),
      ("kind", toJson ("source-proof-coverage" : String)),
      ("contract", toJson contractDeclaration.toString),
      ("status", toJson overallStatus),
      ("entrypoints", toJson (entryRows.map Prod.snd)),
      ("invalidRegistrations", toJson invalidRegistrations),
      ("binding", Lean.Json.mkObj [
        ("policyContract", toJson ("kernel-definitional-equality" : String)),
        ("entrypointIndex", toJson ("policy.subject.entrypoint.val" : String)),
        ("rolePairing", toJson ("kernel-definitional-equality-of-full-AuditPolicy" : String))]),
      ("sourceProofsRechecked", toJson true),
      ("nativeVerification", toJson false),
      ("deployedVerification", toJson false)]
    logInfo m!"NOCTIUM_SOURCE_PROOF_COVERAGE {report.compress}"
  | _ => throwUnsupportedSyntax

end Noctium.Verification
