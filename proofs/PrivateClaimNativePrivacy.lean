import proofs.PrivateClaimNativeState
import Noctium.Verification.NativePrivacy

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace Noctium.PrivateClaimNativePrivacy
open PrivateClaimProofs PrivateClaimLowering PrivateClaimNativeState
open Verification Verification.NativeRelation Verification.NativeState Verification.NativePrivacy

/-- This package extends the exact registered source policy with a separate
native observer. The claim authorizes no additional private release. -/
def policy : Verification.NativePrivacy.Policy := {
  source := PrivateClaimVerification.policy
  observer := .successfulClaimPublicTranscriptV1
  scope := .successfulOnly
  excluded := [.rejectedOutcomes, .termination, .timingAndResources, .proofBytes, .hostProviderAccess, .hostLogs]
}

theorem exact_source_policy : policy.source = PrivateClaimVerification.policy := by rfl
theorem exact_source_scope : policy.scope = policy.source.privacy.scope := by rfl
theorem no_private_release : policy.source.privacy.releases = .none := by rfl

def publicEquivalent (left right : Inputs) : Prop :=
  left.root = right.root ∧ left.campaign = right.campaign ∧ left.nullifier = right.nullifier

def invocation (ctx : EvalContext) (input : Inputs) (root campaign : Scalar)
    (entries : List (Scalar × _root_.Bool)) : Invocation :=
  ⟨ctx, inputEnvironment input.source, state root.val campaign.val (sourceValues entries)⟩

def bindingView (host : HostContext) (input : Inputs) (w : Assignment) (root campaign : Scalar)
    (entries : List (Scalar × _root_.Bool)) (statement : PublicStatement) (after : Machine) : BindingView := {
  parentPublicContext := host.parentPublicContext
  publicValues := [input.root, input.campaign, input.nullifier]
  returnValues := [input.nullifier]
  beforeState := (initial root campaign (encodedEntries entries)).stack
  afterState := after.stack
  reads := after.reads
  publicReadValues := statement.readValues
  operations := operations w
  opcodeGroups := statement.opcodeGroups
  activity := statement.activity
  communicationCommitment := statement.communicationCommitment
}

def observe (binding : BindingFunction) (host : HostContext) (input : Inputs) (w : Assignment)
    (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (statement : PublicStatement) (after : Machine) : Observation :=
  let view := bindingView host input w root campaign entries statement after
  ⟨view, queries (operations w), binding view⟩

theorem admitted_source (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (invariant : StateInvariant fixtureContext root.val campaign.val (sourceValues entries)) :
    policy.source.subject.admissible (invocation ctx input root campaign entries) := by
  exact ⟨⟨root.val, campaign.val, sourceValues entries, rfl, invariant⟩,
    agreement.modulus, input.source, rfl, source_canonical ctx input agreement.modulus⟩

theorem source_equivalent (ctx : EvalContext) (left right : Inputs)
    (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (same : publicEquivalent left right) :
    policy.source.subject.publicEquivalent (invocation ctx left root campaign entries)
      (invocation ctx right root campaign entries) := by
  refine ⟨rfl, rfl, ?_⟩
  change PrivateClaimVerification.subject.publicInputs (inputEnvironment left.source) =
    PrivateClaimVerification.subject.publicInputs (inputEnvironment right.source)
  rw [PrivateClaimVerification.actual_public_inputs, PrivateClaimVerification.actual_public_inputs]
  simp only [Inputs.source, same.1, same.2.1, same.2.2]

/-- Opcode payloads depend solely on declared public inputs after all 55 native
constraints hold. Private SSA values need not match between the executions. -/
theorem operations_public (hash : Hash) (input : Inputs) (sr sc presence : Scalar)
    (w : Assignment) (publicGroups : List (List Scalar))
    (sat : CircuitSatisfies hash callProgram (callStreams input sr sc presence) w publicGroups) :
    operations w = plan input.root input.campaign input.nullifier input.root input.campaign one := by
  obtain ⟨bindings, writeOne⟩ := call_bindings hash input sr sc presence w publicGroups sat
  have guards := call_guards hash input sr sc presence w publicGroups sat
  simp only [operations, plan, bindings.root, bindings.campaign, bindings.nullifier, writeOne,
    guards.1, guards.2.1]

/-- Source acceptance is derived from arbitrary native satisfaction and VM
execution. The registered source two-run privacy theorem is then applied. -/
theorem source_privacy_from_native (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (left right : Inputs) (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (invariant : StateInvariant fixtureContext root.val campaign.val (sourceValues entries))
    (same : publicEquivalent left right)
    (lsr lsc lp rsr rsc rp : Scalar) (lw rw : Assignment)
    (lg rg : List (List Scalar)) (la ra : Machine)
    (leftSat : CircuitSatisfies hash callProgram (callStreams left lsr lsc lp) lw lg)
    (rightSat : CircuitSatisfies hash callProgram (callStreams right rsr rsc rp) rw rg)
    (leftRun : Execution lw root campaign entries lg la)
    (rightRun : Execution rw root campaign entries rg ra) :
    policy.source.subject.execute (invocation ctx left root campaign entries) =
      policy.source.subject.execute (invocation ctx right root campaign entries) := by
  have leftSource := (source_native_preservation ctx hash agreement left lsr lsc lp lw lg leftSat root campaign entries la leftRun).1
  have rightSource := (source_native_preservation ctx hash agreement right rsr rsc rp rw rg rightSat root campaign entries ra rightRun).1
  apply PrivateClaimVerification.privacy (invocation ctx left root campaign entries)
    (invocation ctx right root campaign entries)
    (admitted_source ctx hash agreement left root campaign entries invariant)
    (admitted_source ctx hash agreement right root campaign entries invariant)
    (source_equivalent ctx left right root campaign entries same)
  · trivial
  · exact ⟨⟨_, _, leftSource⟩, ⟨_, _, rightSource⟩⟩

/-- Native observations include every supported public opcode, its query path
and aligned read, state, activity, empty communication commitment and binding.
The host context is shared public environment input, not witness-controlled. -/
theorem native_observer_equal (commit : EmptyCommunicationCommitment) (binding : BindingFunction)
    (host : HostContext) (budget : Budget) (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (left right : Inputs) (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (invariant : StateInvariant fixtureContext root.val campaign.val (sourceValues entries))
    (same : publicEquivalent left right)
    (lsr lsc lp rsr rsc rp : Scalar) (lw rw : Assignment)
    (ls rs : PublicStatement) (la ra : Machine)
    (leftRun : Accepted commit host.communicationRandomness budget hash left lsr lsc lp lw root campaign entries ls la)
    (rightRun : Accepted commit host.communicationRandomness budget hash right rsr rsc rp rw root campaign entries rs ra) :
    policy.source.subject.execute (invocation ctx left root campaign entries) =
      policy.source.subject.execute (invocation ctx right root campaign entries) ∧
    observe binding host left lw root campaign entries ls la =
      observe binding host right rw root campaign entries rs ra := by
  have source := source_privacy_from_native ctx hash agreement left right root campaign entries invariant same
    lsr lsc lp rsr rsc rp lw rw ls.opcodeGroups rs.opcodeGroups la ra leftRun.circuit rightRun.circuit
    leftRun.execution rightRun.execution
  have leftSound := native_execution_sound hash left lsr lsc lp lw ls.opcodeGroups leftRun.circuit
    root campaign entries la leftRun.execution
  have rightSound := native_execution_sound hash right rsr rsc rp rw rs.opcodeGroups rightRun.circuit
    root campaign entries ra rightRun.execution
  have leftOps := operations_public hash left lsr lsc lp lw ls.opcodeGroups leftRun.circuit
  have rightOps := operations_public hash right rsr rsc rp rw rs.opcodeGroups rightRun.circuit
  have opsEq : operations lw = operations rw := by
    rw [leftOps, rightOps, same.1, same.2.1, same.2.2]
  have groupsEq : ls.opcodeGroups = rs.opcodeGroups := by
    rw [← leftRun.execution.transcript, ← rightRun.execution.transcript, opsEq]
  have machineEq : la = ra := by
    rw [leftSound.2.2.2, rightSound.2.2.2, same.1, same.2.1, same.2.2]
  have readValuesEq : ls.readValues = rs.readValues := by
    rw [leftRun.reads, rightRun.reads, machineEq]
  have commEq : ls.communicationCommitment = rs.communicationCommitment :=
    leftRun.communication.trans rightRun.communication.symm
  have activityEq : ls.activity = rs.activity := leftRun.activity.trans rightRun.activity.symm
  have viewEq : bindingView host left lw root campaign entries ls la =
      bindingView host right rw root campaign entries rs ra := by
    simp only [bindingView, same.1, same.2.1, same.2.2, opsEq, machineEq, groupsEq, activityEq, commEq, readValuesEq]
  refine ⟨source, ?_⟩
  simp only [observe, viewEq, opsEq]

/-- This scalar is the real proof-phase bound public input, not the zero
binding placeholder carried by a constructor preimage. Agreement with the
public binding view is an explicit native implementation assumption. -/
def BindingAgrees (binding : BindingFunction) (host : HostContext) (input : Inputs) (w : Assignment)
    (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (statement : PublicStatement) (after : Machine) (boundInput : Scalar) : Prop :=
  boundInput = binding (bindingView host input w root campaign entries statement after)

def actualObserve (binding : BindingFunction) (host : HostContext) (input : Inputs) (w : Assignment)
    (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (statement : PublicStatement) (after : Machine) (boundInput : Scalar) : Observation :=
  {observe binding host input w root campaign entries statement after with bindingInput := boundInput}

theorem bound_native_privacy (commit : EmptyCommunicationCommitment) (binding : BindingFunction)
    (host : HostContext) (budget : Budget) (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (left right : Inputs) (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (invariant : StateInvariant fixtureContext root.val campaign.val (sourceValues entries))
    (same : publicEquivalent left right)
    (lsr lsc lp rsr rsc rp : Scalar) (lw rw : Assignment)
    (ls rs : PublicStatement) (la ra : Machine)
    (leftRun : Accepted commit host.communicationRandomness budget hash left lsr lsc lp lw root campaign entries ls la)
    (rightRun : Accepted commit host.communicationRandomness budget hash right rsr rsc rp rw root campaign entries rs ra)
    (leftBinding rightBinding : Scalar)
    (leftAgreement : BindingAgrees binding host left lw root campaign entries ls la leftBinding)
    (rightAgreement : BindingAgrees binding host right rw root campaign entries rs ra rightBinding) :
    policy.source.subject.execute (invocation ctx left root campaign entries) =
      policy.source.subject.execute (invocation ctx right root campaign entries) ∧
    actualObserve binding host left lw root campaign entries ls la leftBinding =
      actualObserve binding host right rw root campaign entries rs ra rightBinding := by
  have canonical := native_observer_equal commit binding host budget ctx hash agreement left right root campaign entries
    invariant same lsr lsc lp rsr rsc rp lw rw ls rs la ra leftRun rightRun
  have bindEq : leftBinding = rightBinding := leftAgreement.trans
    ((congrArg Observation.bindingInput canonical.2).trans rightAgreement.symm)
  refine ⟨canonical.1, ?_⟩
  simp only [actualObserve, canonical.2, bindEq]

/-- The exact policy identity is part of the required proof type. Functional
correctness alone does not construct this native privacy obligation. -/
def NativePrivacyObligation (candidate : Verification.NativePrivacy.Policy) : Prop :=
  candidate = policy ∧
  ∀ (commit : EmptyCommunicationCommitment) (binding : BindingFunction)
    (host : HostContext) (budget : Budget) (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (left right : Inputs) (root campaign : Scalar) (entries : List (Scalar × _root_.Bool)),
    StateInvariant fixtureContext root.val campaign.val (sourceValues entries) →
    publicEquivalent left right →
    ∀ (lsr lsc lp rsr rsc rp : Scalar) (lw rw : Assignment) (ls rs : PublicStatement) (la ra : Machine),
    Accepted commit host.communicationRandomness budget hash left lsr lsc lp lw root campaign entries ls la →
    Accepted commit host.communicationRandomness budget hash right rsr rsc rp rw root campaign entries rs ra →
    ∀ (leftBinding rightBinding : Scalar),
    BindingAgrees binding host left lw root campaign entries ls la leftBinding →
    BindingAgrees binding host right rw root campaign entries rs ra rightBinding →
    policy.source.subject.execute (invocation ctx left root campaign entries) =
      policy.source.subject.execute (invocation ctx right root campaign entries) ∧
    actualObserve binding host left lw root campaign entries ls la leftBinding =
      actualObserve binding host right rw root campaign entries rs ra rightBinding

theorem privacy : NativePrivacyObligation policy := ⟨rfl, bound_native_privacy⟩

/-- An artifact execution starts from independently decoded plan/call trees.
Public statement metadata stays tied to actual VM reads and native constraints. -/
structure DecodedAccepted (planTree callTree : Lean.Json)
    (commit : EmptyCommunicationCommitment) (host : HostContext) (budget : Budget)
    (hash : Hash) (input : Inputs) (sr sc presence : Scalar) (w : Assignment)
    (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (statement : PublicStatement) (after : Machine) : Prop where
  execution : DecodedExecution planTree callTree hash (callStreams input sr sc presence)
    w root campaign entries statement.opcodeGroups after
  reads : statement.readValues = after.reads.map Cell.value
  activity : statement.activity = List.replicate 21 Bool.true
  communication : statement.communicationCommitment = commit host.communicationRandomness
  admitted : Admitted budget (operations w) (encodedEntries entries)

theorem decoded_accepted (planTree callTree : Lean.Json)
    (planCertificate : Verification.NativeStateJson.decode planTree = .ok symbolicPlan)
    (callCertificate : Verification.NativeRelationJson.decode callTree = .ok callProgram)
    (commit : EmptyCommunicationCommitment) (host : HostContext) (budget : Budget)
    (hash : Hash) (input : Inputs) (sr sc presence : Scalar) (w : Assignment)
    (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (statement : PublicStatement) (after : Machine)
    (accepted : DecodedAccepted planTree callTree commit host budget hash input sr sc presence
      w root campaign entries statement after) :
    Accepted commit host.communicationRandomness budget hash input sr sc presence
      w root campaign entries statement after := by
  obtain ⟨target, symbols, cd, pd, sat, trace, transcript, publicReads⟩ := accepted.execution
  have targetEq := Except.ok.inj (cd.symm.trans callCertificate)
  have symbolsEq := Except.ok.inj (pd.symm.trans planCertificate)
  subst target symbols
  have instantiation := symbolic_instantiation w (call_bindings hash input sr sc presence w statement.opcodeGroups sat).2
  rw [instantiation] at trace transcript
  exact ⟨sat, ⟨trace, transcript, publicReads⟩, accepted.reads, accepted.activity, accepted.communication, accepted.admitted⟩

theorem decoded_privacy (planTree callTree : Lean.Json)
    (planCertificate : Verification.NativeStateJson.decode planTree = .ok symbolicPlan)
    (callCertificate : Verification.NativeRelationJson.decode callTree = .ok callProgram)
    (commit : EmptyCommunicationCommitment) (binding : BindingFunction)
    (host : HostContext) (budget : Budget) (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (left right : Inputs) (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (invariant : StateInvariant fixtureContext root.val campaign.val (sourceValues entries))
    (same : publicEquivalent left right)
    (lsr lsc lp rsr rsc rp : Scalar) (lw rw : Assignment)
    (ls rs : PublicStatement) (la ra : Machine)
    (leftRun : DecodedAccepted planTree callTree commit host budget hash left lsr lsc lp lw root campaign entries ls la)
    (rightRun : DecodedAccepted planTree callTree commit host budget hash right rsr rsc rp rw root campaign entries rs ra) :
    policy.source.subject.execute (invocation ctx left root campaign entries) =
      policy.source.subject.execute (invocation ctx right root campaign entries) ∧
    observe binding host left lw root campaign entries ls la =
      observe binding host right rw root campaign entries rs ra := by
  exact native_observer_equal commit binding host budget ctx hash agreement left right root campaign entries invariant same
    lsr lsc lp rsr rsc rp lw rw ls rs la ra
    (decoded_accepted planTree callTree planCertificate callCertificate commit host budget hash left lsr lsc lp
      lw root campaign entries ls la leftRun)
    (decoded_accepted planTree callTree planCertificate callCertificate commit host budget hash right rsr rsc rp
      rw root campaign entries rs ra rightRun)

theorem decoded_bound_privacy (planTree callTree : Lean.Json)
    (planCertificate : Verification.NativeStateJson.decode planTree = .ok symbolicPlan)
    (callCertificate : Verification.NativeRelationJson.decode callTree = .ok callProgram)
    (commit : EmptyCommunicationCommitment) (binding : BindingFunction)
    (host : HostContext) (budget : Budget) (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (left right : Inputs) (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (invariant : StateInvariant fixtureContext root.val campaign.val (sourceValues entries))
    (same : publicEquivalent left right)
    (lsr lsc lp rsr rsc rp : Scalar) (lw rw : Assignment)
    (ls rs : PublicStatement) (la ra : Machine)
    (leftRun : DecodedAccepted planTree callTree commit host budget hash left lsr lsc lp lw root campaign entries ls la)
    (rightRun : DecodedAccepted planTree callTree commit host budget hash right rsr rsc rp rw root campaign entries rs ra)
    (leftBinding rightBinding : Scalar)
    (leftAgreement : BindingAgrees binding host left lw root campaign entries ls la leftBinding)
    (rightAgreement : BindingAgrees binding host right rw root campaign entries rs ra rightBinding) :
    policy.source.subject.execute (invocation ctx left root campaign entries) =
      policy.source.subject.execute (invocation ctx right root campaign entries) ∧
    actualObserve binding host left lw root campaign entries ls la leftBinding =
      actualObserve binding host right rw root campaign entries rs ra rightBinding := by
  have canonical := decoded_privacy planTree callTree planCertificate callCertificate commit binding host budget ctx hash
    agreement left right root campaign entries invariant same lsr lsc lp rsr rsc rp lw rw ls rs la ra leftRun rightRun
  have bindEq : leftBinding = rightBinding := leftAgreement.trans
    ((congrArg Observation.bindingInput canonical.2).trans rightAgreement.symm)
  refine ⟨canonical.1, ?_⟩
  simp only [actualObserve, canonical.2, bindEq]

def DecodedPrivacyObligation (planTree callTree : Lean.Json) : Prop :=
    ∀ (commit : EmptyCommunicationCommitment) (binding : BindingFunction)
    (host : HostContext) (budget : Budget) (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (left right : Inputs) (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (invariant : StateInvariant fixtureContext root.val campaign.val (sourceValues entries))
    (same : publicEquivalent left right)
    (lsr lsc lp rsr rsc rp : Scalar) (lw rw : Assignment)
    (ls rs : PublicStatement) (la ra : Machine)
    (leftRun : DecodedAccepted planTree callTree commit host budget hash left lsr lsc lp lw root campaign entries ls la)
    (rightRun : DecodedAccepted planTree callTree commit host budget hash right rsr rsc rp rw root campaign entries rs ra)
    (leftBinding rightBinding : Scalar)
    (leftAgreement : BindingAgrees binding host left lw root campaign entries ls la leftBinding)
    (rightAgreement : BindingAgrees binding host right rw root campaign entries rs ra rightBinding),
    policy.source.subject.execute (invocation ctx left root campaign entries) =
      policy.source.subject.execute (invocation ctx right root campaign entries) ∧
    actualObserve binding host left lw root campaign entries ls la leftBinding =
      actualObserve binding host right rw root campaign entries rs ra rightBinding

theorem decoded_obligation (planTree callTree : Lean.Json)
    (planCertificate : Verification.NativeStateJson.decode planTree = .ok symbolicPlan)
    (callCertificate : Verification.NativeRelationJson.decode callTree = .ok callProgram) :
    DecodedPrivacyObligation planTree callTree := decoded_bound_privacy planTree callTree planCertificate callCertificate

/-- Generic progress reuses source eligibility and native completeness rather
than postulating that native executions always succeed. -/
theorem native_progress (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (sourceInput : InputValues) (canonical : CanonicalInputs ctx sourceInput) (leaf node : Nat)
    (hashes : HashTrace ctx sourceInput leaf node) (entries : List (Scalar × _root_.Bool))
    (unused : (typedEntries (sourceValues entries)).lookup (.native sourceInput.nullifier) = none)
    (budget : Budget) (operationsBudget : 21 ≤ budget.operations) (entriesBudget : entries.length + 1 ≤ budget.entries)
    (commit : EmptyCommunicationCommitment) (host : HostContext) :
    let input := Inputs.ofSource ctx sourceInput canonical agreement.modulus
    ∃ w after statement, Accepted commit host.communicationRandomness budget hash input input.root input.campaign zero
      w input.root input.campaign entries statement after :=
  eligible_admitted_complete ctx hash agreement sourceInput canonical leaf node hashes entries unused budget
    operationsBudget entriesBudget commit host.communicationRandomness

/-- Two distinct private witnesses succeed in the explicit abstract zero-hash
fixture. This is nonvacuity evidence, never native Poseidon or ZK evidence. -/
theorem different_private_fixture_pair (commit : EmptyCommunicationCommitment) (binding : BindingFunction)
    (host : HostContext) :
    let left := Inputs.ofSource fixtureContext fixtureValues fixture_canonical rfl
    let right := Inputs.ofSource fixtureContext secondFixtureValues second_fixture_canonical rfl
    left.secret ≠ right.secret ∧ ∃ lw rw ls rs la ra,
      Accepted commit host.communicationRandomness ⟨21,1⟩ zeroHash left zero zero zero lw zero zero [] ls la ∧
      Accepted commit host.communicationRandomness ⟨21,1⟩ zeroHash right zero zero zero rw zero zero [] rs ra ∧
      observe binding host left lw zero zero [] ls la = observe binding host right rw zero zero [] rs ra := by
  dsimp only
  let left := Inputs.ofSource fixtureContext fixtureValues fixture_canonical rfl
  let right := Inputs.ofSource fixtureContext secondFixtureValues second_fixture_canonical rfl
  have secondTrace : HashTrace fixtureContext secondFixtureValues 0 0 := by constructor <;> first | decide | rfl
  obtain ⟨lw, la, ls, leftRun⟩ := native_progress fixtureContext zeroHash zero_hash_agreement fixtureValues
    fixture_canonical 0 0 fixture_hash_trace [] (by rfl) ⟨21,1⟩ (by decide) (by decide) commit host
  obtain ⟨rw, ra, rs, rightRun⟩ := native_progress fixtureContext zeroHash zero_hash_agreement secondFixtureValues
    second_fixture_canonical 0 0 secondTrace [] (by rfl) ⟨21,1⟩ (by decide) (by decide) commit host
  have validState : StateInvariant fixtureContext zero.val zero.val (sourceValues []) :=
    initial_state_invariant fixtureContext 0 0 (by decide) (by decide)
  have same : publicEquivalent left right := ⟨rfl,rfl,rfl⟩
  refine ⟨by decide +kernel, lw, rw, ls, rs, la, ra, leftRun, rightRun, ?_⟩
  exact (native_observer_equal commit binding host ⟨21,1⟩ fixtureContext zeroHash zero_hash_agreement left right
    zero zero [] validState same zero zero zero zero zero zero lw rw ls rs la ra leftRun rightRun).2

def flipFirstDirection (input : InputValues) : InputValues :=
  {input with direction0 := !input.direction0}

theorem symmetric_path_flip (ctx : EvalContext) (input : InputValues) (leaf node : Nat)
    (canonical : CanonicalInputs ctx input) (trace : HashTrace ctx input leaf node)
    (symmetric : input.sibling0 = leaf) :
    CanonicalInputs ctx (flipFirstDirection input) ∧
    HashTrace ctx (flipFirstDirection input) leaf node ∧
    input.direction0 ≠ (flipFirstDirection input).direction0 := by
  have first : ctx.poseidon2 2 leaf leaf = .ok node := by
    simpa only [symmetric, ite_self] using trace.firstNode
  refine ⟨⟨canonical.domains, canonical.root, canonical.campaign, canonical.nullifier, canonical.secret, canonical.sibling0, canonical.sibling1⟩, ⟨trace.canonicalLeaf, trace.canonicalNode, trace.leafHash, ?_, trace.secondNode, trace.nullifierHash⟩, ?_⟩
  · simpa only [flipFirstDirection, symmetric, ite_self] using first
  · cases hd : input.direction0 <;> simp [flipFirstDirection, hd]

/-- With sibling0 equal to the leaf, flipping the private first direction leaves
both child pairs unchanged for any agreed native hash. No collision assumption
or artificial zero-hash model is needed for this progress/nonvacuity family. -/
theorem symmetric_eligible_native_pair (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (sourceInput : InputValues) (canonical : CanonicalInputs ctx sourceInput) (leaf node : Nat)
    (trace : HashTrace ctx sourceInput leaf node) (symmetric : sourceInput.sibling0 = leaf)
    (entries : List (Scalar × _root_.Bool))
    (invariant : StateInvariant fixtureContext sourceInput.root sourceInput.campaign (sourceValues entries))
    (unused : (typedEntries (sourceValues entries)).lookup (.native sourceInput.nullifier) = none)
    (budget : Budget) (operationsBudget : 21 ≤ budget.operations) (entriesBudget : entries.length + 1 ≤ budget.entries)
    (commit : EmptyCommunicationCommitment) (binding : BindingFunction) (host : HostContext) :
    let left := Inputs.ofSource ctx sourceInput canonical agreement.modulus
    let rightCanonical := (symmetric_path_flip ctx sourceInput leaf node canonical trace symmetric).1
    let right := Inputs.ofSource ctx (flipFirstDirection sourceInput) rightCanonical agreement.modulus
    left.direction0 ≠ right.direction0 ∧ ∃ lw rw ls rs la ra,
      Accepted commit host.communicationRandomness budget hash left left.root left.campaign zero lw left.root left.campaign entries ls la ∧
      Accepted commit host.communicationRandomness budget hash right right.root right.campaign zero rw left.root left.campaign entries rs ra ∧
      observe binding host left lw left.root left.campaign entries ls la =
        observe binding host right rw left.root left.campaign entries rs ra := by
  dsimp only
  obtain ⟨rightCanonical, rightTrace, different⟩ := symmetric_path_flip ctx sourceInput leaf node canonical trace symmetric
  let left := Inputs.ofSource ctx sourceInput canonical agreement.modulus
  let right := Inputs.ofSource ctx (flipFirstDirection sourceInput) rightCanonical agreement.modulus
  obtain ⟨lw, la, ls, leftRun⟩ := native_progress ctx hash agreement sourceInput canonical leaf node trace entries unused
    budget operationsBudget entriesBudget commit host
  obtain ⟨rw, ra, rs, rightRun⟩ := native_progress ctx hash agreement (flipFirstDirection sourceInput) rightCanonical
    leaf node rightTrace entries unused budget operationsBudget entriesBudget commit host
  have same : publicEquivalent left right := ⟨rfl,rfl,rfl⟩
  have directionDiff : left.direction0 ≠ right.direction0 := by
    cases hd : sourceInput.direction0 <;>
      simp [left, right, Inputs.ofSource, flipFirstDirection, hd, bit, zero_ne_one, Ne.symm zero_ne_one]
  refine ⟨directionDiff, lw, rw, ls, rs, la, ra, leftRun, rightRun, ?_⟩
  exact (native_observer_equal commit binding host budget ctx hash agreement left right left.root left.campaign entries
    invariant same left.root left.campaign zero right.root right.campaign zero lw rw ls rs la ra leftRun rightRun).2

/-- A changed scope cannot reuse the successful-execution privacy obligation. -/
def allOutcomesPolicy : Verification.NativePrivacy.Policy := {policy with scope := .allOutcomes}

theorem wrong_scope_rejected : ¬ NativePrivacyObligation allOutcomesPolicy := by
  intro claim
  have impossible := congrArg Verification.NativePrivacy.Policy.scope claim.1
  contradiction

/-- Exact byte/build binding is a future proof argument. This theorem exposes
both pending conclusions instead of silently claiming artifact authentication. -/
theorem exact_artifact_composition {byteType buildType : Type} (sourceIdentity : String)
    (planBytes callBytes : byteType) (planTree callTree : Lean.Json) (build : buildType)
    (parse : byteType → Except String Lean.Json)
    (authenticates : buildType → String → byteType → byteType → Prop)
    (bindingCertificate : ExactArtifactBinding byteType buildType sourceIdentity planBytes callBytes planTree callTree build parse authenticates)
    (planCertificate : Verification.NativeStateJson.decode planTree = .ok symbolicPlan)
    (callCertificate : Verification.NativeRelationJson.decode callTree = .ok callProgram) :
    parse planBytes = .ok planTree ∧ parse callBytes = .ok callTree ∧
    authenticates build sourceIdentity planBytes callBytes ∧ DecodedPrivacyObligation planTree callTree :=
  ⟨bindingCertificate.planParsed, bindingCertificate.callParsed, bindingCertificate.authenticatedBuild,
    decoded_obligation planTree callTree planCertificate callCertificate⟩

#print axioms privacy
#print axioms native_observer_equal
#print axioms bound_native_privacy
#print axioms decoded_bound_privacy
#print axioms source_privacy_from_native
#print axioms decoded_privacy
#print axioms different_private_fixture_pair
#print axioms symmetric_eligible_native_pair
#print axioms exact_artifact_composition
#print axioms wrong_scope_rejected
end Noctium.PrivateClaimNativePrivacy
