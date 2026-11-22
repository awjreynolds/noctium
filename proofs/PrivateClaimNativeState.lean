import proofs.PrivateClaimLowering
import proofs.PrivateClaimVerification
import Noctium.Verification.NativeStateJson

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Noctium.PrivateClaimNativeState
open PrivateClaimProofs PrivateClaimLowering Verification.NativeRelation
open Verification.NativeState
private def ref := Operand.reference
private def imm (value : Nat) := Operand.immediate (scalar value)

/-- Independently specified actual ledger-call graph. Its emitted JSON tree is
bound separately through the strict NativeRelationJson decoder. -/
def callProgram : Program := {
  outputArity := 0
  communicationsCommitment := Bool.true
  instructions := [
    .input .«public» "%input_root",
    .input .«public» "%input_campaign",
    .input .«public» "%input_suppliedNullifier",
    .input .«private» "%input_secret",
    .input .«private» "%input_sibling0",
    .input .«private» "%input_sibling1",
    .input .«private» "%input_direction0",
    .boolean (ref "%input_direction0"),
    .input .«private» "%input_direction1",
    .boolean (ref "%input_direction1"),
    .hash [imm 1, ref "%input_secret", ref "%input_campaign"] "%v0",
    .select (ref "%input_direction0") (ref "%input_sibling0") (ref "%v0") "%v1",
    .select (ref "%input_direction0") (ref "%v0") (ref "%input_sibling0") "%v2",
    .hash [imm 2, ref "%v1", ref "%v2"] "%v3",
    .select (ref "%input_direction1") (ref "%input_sibling1") (ref "%v3") "%v4",
    .select (ref "%input_direction1") (ref "%v3") (ref "%input_sibling1") "%v5",
    .hash [imm 2, ref "%v4", ref "%v5"] "%v6",
    .testEq (ref "%v6") (ref "%input_root") "%v7",
    .assert (ref "%v7"),
    .hash [imm 3, ref "%input_secret", ref "%input_campaign"] "%v8",
    .testEq (ref "%v8") (ref "%input_suppliedNullifier") "%v9",
    .assert (ref "%v9"),
    .input .«public» "%input_storedRoot",
    .input .«public» "%input_storedCampaign",
    .input .«public» "%input__noctium_absence_5",
    .boolean (ref "%input__noctium_absence_5"),
    .testEq (ref "%input_storedRoot") (ref "%input_root") "%v10",
    .assert (ref "%v10"),
    .testEq (ref "%input_storedCampaign") (ref "%input_campaign") "%v11",
    .assert (ref "%v11"),
    .testEq (ref "%input__noctium_absence_5") (imm 0) "%v12",
    .assert (ref "%v12"),
    .impact (imm 1) [imm 16, imm 1, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, ref "%input_root"],
    .impact (imm 1) [imm 12, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, ref "%input_root"],
    .impact (imm 1) [imm 16, imm 1, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, ref "%input_campaign"],
    .impact (imm 1) [imm 12, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, ref "%input_campaign"],
    .impact (imm 1) [imm 16, imm 1, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, ref "%input_suppliedNullifier"],
    .impact (imm 1) [imm 12, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, ref "%input_suppliedNullifier"],
    .impact (imm 1) [imm 48],
    .impact (imm 1) [imm 80, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, imm 0],
    .impact (imm 1) [imm 12, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, ref "%input_storedRoot"],
    .impact (imm 1) [imm 48],
    .impact (imm 1) [imm 80, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, imm 1],
    .impact (imm 1) [imm 12, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, ref "%input_storedCampaign"],
    .impact (imm 1) [imm 48],
    .impact (imm 1) [imm 80, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, imm 2],
    .impact (imm 1) [imm 16, imm 1, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, ref "%input_suppliedNullifier"],
    .impact (imm 1) [imm 24],
    .impact (imm 1) [imm 12, imm 1, imm 1, imm 0],
    .impact (imm 1) [imm 112, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, imm 2],
    .impact (imm 1) [imm 16, imm 1, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, ref "%input_suppliedNullifier"],
    .select (imm 1) (imm 1) (imm 0) "%v13",
    .impact (imm 1) [imm 17, imm 1, imm 1, imm 52435875175126190479447740508185965837690552500527637822603658699938581184511, ref "%v13"],
    .impact (imm 1) [imm 146],
    .output []]
}

def operations (w : Assignment) : List Op := [
  .push (field (w "%input_root")) Bool.false, .popeq (field (w "%input_root")),
  .push (field (w "%input_campaign")) Bool.false, .popeq (field (w "%input_campaign")),
  .push (field (w "%input_suppliedNullifier")) Bool.false, .popeq (field (w "%input_suppliedNullifier")),
  .dup, .index 0 Bool.false, .popeq (field (w "%input_storedRoot")),
  .dup, .index 1 Bool.false, .popeq (field (w "%input_storedCampaign")),
  .dup, .index 2 Bool.false, .push (field (w "%input_suppliedNullifier")) Bool.false,
  .member, .popeq (boolean Bool.false), .index 2 Bool.true,
  .push (field (w "%input_suppliedNullifier")) Bool.false,
  .push (field (w "%v13")) Bool.true, .insert 2]

def sourceValues (entries : List (Scalar × _root_.Bool)) : List (Nat × _root_.Bool) :=
  entries.map fun p => (p.1.val, p.2)
def encodedEntries (entries : List (Scalar × _root_.Bool)) : List (Scalar × Scalar) :=
  entries.map fun p => (p.1, bit p.2)
def mark (key : Scalar) (entries : List (Scalar × _root_.Bool)) : List (Scalar × _root_.Bool) :=
  (key, Bool.true) :: entries.filter (fun p => p.1 != key)

def callStreams (input : Inputs) (storedRoot storedCampaign presence : Scalar) : InputStreams := {
  publicValues := [input.root, input.campaign, input.nullifier, storedRoot, storedCampaign, presence]
  privateValues := input.streams.privateValues
}

/-- Native execution relation. The machine starts from encoded state, never a
source evaluator result. Ordered reads must equal public input scalars. -/
structure Execution (w : Assignment) (root campaign : Scalar)
    (entries : List (Scalar × _root_.Bool)) (publicGroups : List (List Scalar)) (after : Machine) : Prop where
  trace : Trace (operations w) (initial root campaign (encodedEntries entries)) after
  transcript : groups (operations w) = publicGroups
  publicReads : after.reads.map Cell.value = callProgram.inputValues .«public» w

/-- Complete field vectors, opcode grouping, all-active structure and storage
flags agree with the independent VM instruction encoding. -/
theorem groups_encoding (w : Assignment) : callProgram.groups w = groups (operations w) := by
  rfl

theorem scalar_projection (hash : Hash) (input : Inputs) (sr sc presence : Scalar)
    (w : Assignment) (publicGroups : List (List Scalar))
    (sat : CircuitSatisfies hash callProgram (callStreams input sr sc presence) w publicGroups) :
    CircuitSatisfies hash program input.streams w (program.groups w) := by
  constructor
  · intro instruction membership
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst instruction
    all_goals first | trivial | exact sat.instructions _ (by decide +kernel)
  · have hp := sat.publicInputs
    change [w "%input_root", w "%input_campaign", w "%input_suppliedNullifier",
      w "%input_storedRoot", w "%input_storedCampaign", w "%input__noctium_absence_5"] =
      [input.root, input.campaign, input.nullifier, sr, sc, presence] at hp
    have head := congrArg (List.take 3) hp
    exact head
  · exact sat.privateInputs
  · rfl

 theorem call_bindings (hash : Hash) (input : Inputs) (sr sc presence : Scalar)
    (w : Assignment) (publicGroups : List (List Scalar))
    (sat : CircuitSatisfies hash callProgram (callStreams input sr sc presence) w publicGroups) :
    InputBindings input w ∧ w "%v13" = one := by
  refine ⟨stream_bindings hash input w _ _ (scalar_projection hash input sr sc presence w publicGroups sat).withObservedReturns, ?_⟩
  have selected := (sat.instructions (.select (imm 1) (imm 1) (imm 0) "%v13") (by simp [callProgram])).2
  simpa only [Instruction.Holds, Operand.read, imm, show scalar 1 = one by decide, ite_true] using selected

/-- In the qualified claim the 21 operations execute with no jumps or skipped
groups. The read result includes three echo reads, two cells, then membership. -/
def plan (root campaign nullifier storedRoot storedCampaign writeValue : Scalar) : List Op := [
  .push (field root) Bool.false, .popeq (field root),
  .push (field campaign) Bool.false, .popeq (field campaign),
  .push (field nullifier) Bool.false, .popeq (field nullifier),
  .dup, .index 0 Bool.false, .popeq (field storedRoot),
  .dup, .index 1 Bool.false, .popeq (field storedCampaign),
  .dup, .index 2 Bool.false, .push (field nullifier) Bool.false, .member,
  .popeq (boolean Bool.false), .index 2 Bool.true, .push (field nullifier) Bool.false,
  .push (field writeValue) Bool.true, .insert 2]

def planResult (root campaign nullifier actualRoot actualCampaign writeValue : Scalar)
    (entries : List (Scalar × Scalar)) : Machine :=
  {stack := [.array [field actualRoot, field actualCampaign]
      ((nullifier, writeValue) :: entries.filter (fun p => p.1 != nullifier))]
   reads := [field root, field campaign, field nullifier, field actualRoot, field actualCampaign, boolean Bool.false]}

def result (root campaign nullifier writeValue : Scalar) (entries : List (Scalar × Scalar)) : Machine :=
  planResult root campaign nullifier root campaign writeValue entries

theorem execute_plan (root campaign nullifier storedRoot storedCampaign writeValue actualRoot actualCampaign : Scalar)
    (entries : List (Scalar × Scalar)) :
    run (plan root campaign nullifier storedRoot storedCampaign writeValue) (initial actualRoot actualCampaign entries) =
      if actualRoot = storedRoot ∧ actualCampaign = storedCampaign ∧ entries.any (fun p => p.1 == nullifier) = Bool.false
      then some (planResult root campaign nullifier actualRoot actualCampaign writeValue entries) else none := by
  by_cases hr : actualRoot = storedRoot
  · subst storedRoot
    by_cases hc : actualCampaign = storedCampaign
    · subst storedCampaign
      cases hm : entries.any (fun p => p.1 == nullifier) <;>
        simp only [plan, initial, run_push, run_popeq, run_dup, run_index_zero, run_index_one,
          run_index_two, run_member, run_insert_two, field_inj, hm, boolean_ne, run_nil,
          ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false, and_self, and_true, true_and,
          List.nil_append, List.cons_append, planResult]
    · simp [plan, initial, run_push, run_popeq, run_dup, run_index_zero, run_index_one, hc]
  · simp [plan, initial, run_push, run_popeq, run_dup, run_index_zero, hr]

theorem absence_encoding (key : Scalar) (entries : List (Scalar × _root_.Bool)) :
    (encodedEntries entries).any (fun p => p.1 == key) = Bool.false ↔
    (typedEntries (sourceValues entries)).lookup (.native key.val) = none := by
  induction entries with
  | nil => simp [encodedEntries, sourceValues, typedEntries]
  | cons p rest ih =>
    rcases p with ⟨k, b⟩
    by_cases eq : k = key
    · subst k
      simp [encodedEntries, sourceValues, typedEntries, List.lookup]
    · have neq : k.val ≠ key.val := fun h => eq (Fin.ext h)
      change ((_ == key) || (encodedEntries rest).any (fun p => p.1 == key)) = Bool.false ↔
        (match key.val == k.val with
        | Bool.true => some (.bool b)
        | Bool.false => (typedEntries (sourceValues rest)).lookup (.native key.val)) = none
      have hk : (k == key) = Bool.false := by simp [eq]
      have hn : (key.val == k.val) = Bool.false := by exact beq_eq_false_iff_ne.mpr (Ne.symm neq)
      simpa only [hk, Bool.false_or, hn] using ih

theorem mark_encoding (key : Scalar) (entries : List (Scalar × _root_.Bool)) :
    sourceValues (mark key entries) = recordValues key.val (sourceValues entries) := by
  induction entries with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨k, b⟩
    by_cases eq : k = key
    · subst k
      simpa [mark, sourceValues, recordValues] using ih
    · have neq : k.val ≠ key.val := fun h => eq (Fin.ext h)
      simpa [mark, sourceValues, recordValues, eq, neq] using congrArg (fun xs => (key.val, Bool.true) :: (k.val, b) :: xs.tail) ih

theorem encoded_mark (key : Scalar) (entries : List (Scalar × _root_.Bool)) :
    encodedEntries (mark key entries) =
      (key, one) :: (encodedEntries entries).filter (fun p => p.1 != key) := by
  induction entries with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨k,b⟩
    by_cases eq : k = key
    · subst k; simpa [encodedEntries, mark] using ih
    · simpa [encodedEntries, mark, eq, bit] using congrArg (fun xs => (key, one) :: (k, bit b) :: xs.tail) ih

theorem call_guards (hash : Hash) (input : Inputs) (sr sc presence : Scalar)
    (w : Assignment) (publicGroups : List (List Scalar))
    (sat : CircuitSatisfies hash callProgram (callStreams input sr sc presence) w publicGroups) :
    w "%input_storedRoot" = w "%input_root" ∧
    w "%input_storedCampaign" = w "%input_campaign" ∧
    w "%input__noctium_absence_5" = zero := by
  refine ⟨?_, ?_, ?_⟩
  · exact test_eq_assert_sound _ _ _
      (sat.instructions (.testEq (ref "%input_storedRoot") (ref "%input_root") "%v10") (by simp [callProgram]))
      (sat.instructions (.assert (ref "%v10")) (by simp [callProgram]))
  · exact test_eq_assert_sound _ _ _
      (sat.instructions (.testEq (ref "%input_storedCampaign") (ref "%input_campaign") "%v11") (by simp [callProgram]))
      (sat.instructions (.assert (ref "%v11")) (by simp [callProgram]))
  · exact test_eq_assert_sound _ _ _
      (sat.instructions (.testEq (ref "%input__noctium_absence_5") (imm 0) "%v12") (by simp [callProgram]))
      (sat.instructions (.assert (ref "%v12")) (by simp [callProgram]))

/-- Universal native VM preservation. No source success, honest read provider,
or state preservation assumption occurs among the premises. -/
theorem native_execution_sound (hash : Hash) (input : Inputs) (sr sc presence : Scalar)
    (w : Assignment) (publicGroups : List (List Scalar))
    (sat : CircuitSatisfies hash callProgram (callStreams input sr sc presence) w publicGroups)
    (root campaign : Scalar) (entries : List (Scalar × _root_.Bool)) (after : Machine)
    (execution : Execution w root campaign entries publicGroups after) :
    root = input.root ∧ campaign = input.campaign ∧
    (typedEntries (sourceValues entries)).lookup (.native input.nullifier.val) = none ∧
    after = result input.root input.campaign input.nullifier one (encodedEntries entries) := by
  obtain ⟨bindings, writeValue⟩ := call_bindings hash input sr sc presence w publicGroups sat
  have guards := call_guards hash input sr sc presence w publicGroups sat
  have ops : operations w = plan input.root input.campaign input.nullifier
      (w "%input_storedRoot") (w "%input_storedCampaign") one := by
    simp only [operations, plan, bindings.root, bindings.campaign, bindings.nullifier, writeValue]
  have executed := (trace_iff_run _ _ _).mp execution.trace
  rw [ops, execute_plan] at executed
  have checks : root = w "%input_storedRoot" ∧ campaign = w "%input_storedCampaign" ∧
      (encodedEntries entries).any (fun p => p.1 == input.nullifier) = Bool.false := by
    by_cases allowed : root = w "%input_storedRoot" ∧ campaign = w "%input_storedCampaign" ∧
        (encodedEntries entries).any (fun p => p.1 == input.nullifier) = Bool.false
    · exact allowed
    · rw [if_neg allowed] at executed
      contradiction
  rw [if_pos checks] at executed
  have rootEq := checks.1.trans (guards.1.trans bindings.root)
  have campaignEq := checks.2.1.trans (guards.2.1.trans bindings.campaign)
  refine ⟨rootEq, campaignEq, (absence_encoding _ _).mp checks.2.2, ?_⟩
  simpa only [rootEq, campaignEq, result] using (Option.some.inj executed).symm

/-- Composition to the imported actual source entrypoint, with its exact
successor. HashAgreement exposes the scalar/hash implementation boundary. -/
theorem source_native_preservation (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (sr sc presence : Scalar) (w : Assignment) (publicGroups : List (List Scalar))
    (sat : CircuitSatisfies hash callProgram (callStreams input sr sc presence) w publicGroups)
    (root campaign : Scalar) (entries : List (Scalar × _root_.Bool)) (after : Machine)
    (execution : Execution w root campaign entries publicGroups after) :
    claimEntry.run ctx (inputEnvironment input.source) (state root.val campaign.val (sourceValues entries)) =
      .ok ([("nullifier", .native input.nullifier.val)],
        state input.root.val input.campaign.val (sourceValues (mark input.nullifier entries))) ∧
    after.stack = (initial input.root input.campaign (encodedEntries (mark input.nullifier entries))).stack := by
  obtain ⟨rootEq, campaignEq, unspentProof, afterEq⟩ :=
    native_execution_sound hash input sr sc presence w publicGroups sat root campaign entries after execution
  have source := (native_constraints_sound ctx hash agreement input w _
    (scalar_projection hash input sr sc presence w publicGroups sat)).1
  subst root campaign
  have canonical := source_canonical ctx input agreement.modulus
  constructor
  · rw [mark_encoding, ← recorded_is_canonical_state]
    exact accepted_claim_transition ctx _ input.root.val input.campaign.val input.nullifier.val
      (sourceValues entries) source (by rfl) (by rfl) canonical.root canonical.campaign canonical.nullifier unspentProof
  · rw [afterEq, encoded_mark]
    rfl

/-- Native replay fails at the membership read before the insertion. This holds
for any replacement writeValue scalar and every prior map. -/
theorem native_replay_rejected (root campaign key writeValue : Scalar)
    (entries : List (Scalar × _root_.Bool)) :
    run (plan root campaign key root campaign writeValue)
      (initial root campaign (encodedEntries (mark key entries))) = none := by
  rw [execute_plan]
  simp [encodedEntries, mark]

theorem native_frame (root campaign key writeValue : Scalar) (entries : List (Scalar × Scalar)) :
    (result root campaign key writeValue entries).stack.head? =
      some (.array [field root, field campaign] ((key,writeValue) :: entries.filter (fun p => p.1 != key))) := by rfl

theorem invariant_preserved (ctx : EvalContext) (input : Inputs)
    (entries : List (Scalar × _root_.Bool))
    (modulus : ctx.modulus = Field.modulus)
    (before : StateInvariant ctx input.root.val input.campaign.val (sourceValues entries)) :
    StateInvariant ctx input.root.val input.campaign.val (sourceValues (mark input.nullifier entries)) := by
  rw [mark_encoding]
  exact recorded_state_preserves_invariant ctx _ _ _ _
    (by simpa only [modulus] using input.nullifier.isLt) before


open Verification.NativeStateJson

def symbolicPlan : List SymbolicOp := [
  .push (ref "%input_root") Bool.false, .popeq (ref "%input_root") .field,
  .push (ref "%input_campaign") Bool.false, .popeq (ref "%input_campaign") .field,
  .push (ref "%input_suppliedNullifier") Bool.false, .popeq (ref "%input_suppliedNullifier") .field,
  .dup, .index 0 Bool.false, .popeq (ref "%input_storedRoot") .field,
  .dup, .index 1 Bool.false, .popeq (ref "%input_storedCampaign") .field,
  .dup, .index 2 Bool.false, .push (ref "%input_suppliedNullifier") Bool.false,
  .member, .popeq (imm 0) .bit, .index 2 Bool.true,
  .push (ref "%input_suppliedNullifier") Bool.false,
  .push (imm 1) Bool.true, .insert 2]

theorem symbolic_instantiation (w : Assignment) (writeOne : w "%v13" = one) :
    symbolicPlan.map (SymbolicOp.instantiate w) = operations w := by
  simp only [symbolicPlan, List.map_cons, List.map_nil, SymbolicOp.instantiate, Operand.read,
    ref, imm, operations, writeOne]
  rfl

def callWitness (hash : Hash) (input : Inputs) : Assignment := fun name =>
  match name with
  | "%input_storedRoot" => input.root
  | "%input_storedCampaign" => input.campaign
  | "%input__noctium_absence_5" => zero
  | "%v10" | "%v11" | "%v12" | "%v13" => one
  | _ => computedWitness hash input name

theorem call_assignment_complete (hash : Hash) (input : Inputs)
    (direction0 : input.direction0 = zero ∨ input.direction0 = one)
    (direction1 : input.direction1 = zero ∨ input.direction1 = one)
    (root : (compute hash input).root = input.root)
    (nullifier : (compute hash input).nullifier = input.nullifier) :
    CircuitSatisfies hash callProgram (callStreams input input.root input.campaign zero)
      (callWitness hash input) (groups (operations (callWitness hash input))) := by
  have original := computed_assignment_satisfies hash input direction0 direction1 root nullifier
  constructor
  · intro instruction membership
    simp only [callProgram, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst instruction
    all_goals first | trivial | exact original.instructions _ (by decide +kernel) |
      simp [Instruction.Holds, Operand.read, ref, imm, callWitness, computedWitness,
        bit, show scalar 1 = one by decide, show scalar 0 = zero by decide, zero_ne_one, Ne.symm zero_ne_one]
    all_goals first
      | exact original.instructions (.assert (.reference "%v7")) (by decide +kernel)
      | exact original.instructions (.assert (.reference "%v9")) (by decide +kernel)
  · rfl
  · rfl
  · exact groups_encoding _

/-- Every eligible source execution has a native witness and checked VM trace,
including matching public read values, not merely a scalar-circuit witness. -/
theorem eligible_native_complete (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (sourceInput : InputValues) (canonical : CanonicalInputs ctx sourceInput) (leaf node : Nat)
    (hashes : HashTrace ctx sourceInput leaf node) (entries : List (Scalar × _root_.Bool))
    (unused : (typedEntries (sourceValues entries)).lookup (.native sourceInput.nullifier) = none) :
    let input := Inputs.ofSource ctx sourceInput canonical agreement.modulus
    ∃ w after, CircuitSatisfies hash callProgram (callStreams input input.root input.campaign zero)
      w (groups (operations w)) ∧ Execution w input.root input.campaign entries (groups (operations w)) after := by
  dsimp only
  let input := Inputs.ofSource ctx sourceInput canonical agreement.modulus
  have source : claimEntry.circuit.run ctx (inputEnvironment input.source) =
      .ok [("nullifier", .native sourceInput.nullifier)] := by
    rw [source_embedding]
    exact hash_trace_circuit_accepts ctx sourceInput leaf node canonical hashes
  obtain ⟨root, nullifier⟩ := source_acceptance_calculation ctx hash agreement input _ source
  let w := callWitness hash input
  have sat := call_assignment_complete hash input (bit_is_boolean sourceInput.direction0)
    (bit_is_boolean sourceInput.direction1) root nullifier
  refine ⟨w, result input.root input.campaign input.nullifier one (encodedEntries entries), sat, ?_⟩
  have unspentProof : (encodedEntries entries).any (fun p => p.1 == input.nullifier) = Bool.false :=
    (absence_encoding _ _).mpr unused
  have opEq : operations w = plan input.root input.campaign input.nullifier input.root input.campaign one := by rfl
  constructor
  · apply (trace_iff_run _ _ _).mpr
    change run (operations w) (initial input.root input.campaign (encodedEntries entries)) =
      some (result input.root input.campaign input.nullifier one (encodedEntries entries))
    rw [opEq, execute_plan]
    simp only [unspentProof, and_self, ite_true, result, eq_self]
  · rfl
  · rfl

/-- Empty contract input/output commitments are modeled through the pinned
transient-commitment function as an explicit oracle. No hiding claim is made. -/
abbrev EmptyCommunicationCommitment := Scalar → Scalar

structure PublicStatement where
  opcodeGroups : List (List Scalar)
  readValues : List Scalar
  activity : List _root_.Bool
  communicationCommitment : Scalar

/-- The proof statement and the ledger trace share the same ordered groups,
read stream and all-active mask. Budget is a separate admission predicate. -/
structure Accepted (commit : EmptyCommunicationCommitment) (randomness : Scalar)
    (budget : Budget) (hash : Hash) (input : Inputs) (sr sc presence : Scalar)
    (w : Assignment) (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (statement : PublicStatement) (after : Machine) : Prop where
  circuit : CircuitSatisfies hash callProgram (callStreams input sr sc presence) w statement.opcodeGroups
  execution : Execution w root campaign entries statement.opcodeGroups after
  reads : statement.readValues = after.reads.map Cell.value
  activity : statement.activity = List.replicate 21 Bool.true
  communication : statement.communicationCommitment = commit randomness
  admitted : Admitted budget (operations w) (encodedEntries entries)

theorem public_transcript_preserved (commit : EmptyCommunicationCommitment) (randomness : Scalar)
    (budget : Budget) (hash : Hash) (input : Inputs) (sr sc presence : Scalar)
    (w : Assignment) (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (statement : PublicStatement) (after : Machine)
    (accepted : Accepted commit randomness budget hash input sr sc presence w root campaign entries statement after) :
    statement.opcodeGroups = groups (operations w) ∧
    statement.readValues = [input.root, input.campaign, input.nullifier, input.root, input.campaign, zero] ∧
    statement.activity = List.replicate 21 Bool.true ∧
    statement.communicationCommitment = commit randomness := by
  have sound := native_execution_sound hash input sr sc presence w statement.opcodeGroups accepted.circuit
    root campaign entries after accepted.execution
  refine ⟨accepted.execution.transcript.symm, ?_, accepted.activity, accepted.communication⟩
  rw [accepted.reads, sound.2.2.2]
  rfl

theorem entries_frame (key other value : Scalar) (entries : List (Scalar × Scalar)) (different : other ≠ key) :
    ((key,value) :: entries.filter (fun p => p.1 != key)).lookup other = entries.lookup other := by
  have neq : (other == key) = Bool.false := beq_eq_false_iff_ne.mpr different
  simp only [List.lookup_cons, neq]
  induction entries with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨k,v⟩
    by_cases eq : k = key
    · subst k
      simpa [List.lookup_cons, neq] using ih
    · by_cases same : other = k
      · subst k; simp [eq, List.lookup_cons]
      · have ne : (other == k) = Bool.false := beq_eq_false_iff_ne.mpr same
        simpa [eq, List.lookup_cons, ne] using ih

theorem actual_schema_order : PrivateClaim.state.map (fun d => (d.name, d.kind)) =
    [("acceptedRoot", .cell .native), ("campaignId", .cell .native), ("spent", .map .native .bool)] := by rfl

theorem actual_effect_order : claimEntry.effects = [
    .readCell "acceptedRoot" "storedRoot" .native,
    .require (.eq (.ref "storedRoot" : Expr .native) (.ref "root")),
    .readCell "campaignId" "storedCampaign" .native,
    .require (.eq (.ref "storedCampaign" : Expr .native) (.ref "campaign")),
    .requireAbsent "spent" .native (.ref "nullifier"),
    .writeMap "spent" .native .bool (.ref "nullifier") (.bool Bool.true)] := by rfl

/-- Decoded artifact execution leaves both the SSA witness and the VM trace
arbitrary. It does not postulate a trusted transcript-read provider. -/
def DecodedExecution (planJson callJson : Lean.Json) (hash : Hash) (streams : InputStreams)
    (w : Assignment) (root campaign : Scalar) (entries : List (Scalar × _root_.Bool))
    (publicGroups : List (List Scalar)) (after : Machine) : Prop :=
  ∃ target symbols, Verification.NativeRelationJson.decode callJson = .ok target ∧
    Verification.NativeStateJson.decode planJson = .ok symbols ∧
    CircuitSatisfies hash target streams w publicGroups ∧
    Trace (symbols.map (SymbolicOp.instantiate w)) (initial root campaign (encodedEntries entries)) after ∧
    groups (symbols.map (SymbolicOp.instantiate w)) = publicGroups ∧
    after.reads.map Cell.value = target.inputValues .«public» w

theorem decoded_execution_sound (planJson callJson : Lean.Json)
    (planCertificate : Verification.NativeStateJson.decode planJson = .ok symbolicPlan)
    (callCertificate : Verification.NativeRelationJson.decode callJson = .ok callProgram)
    (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (input : Inputs) (sr sc presence : Scalar) (w : Assignment) (root campaign : Scalar)
    (entries : List (Scalar × _root_.Bool)) (publicGroups : List (List Scalar)) (after : Machine)
    (execution : DecodedExecution planJson callJson hash (callStreams input sr sc presence)
      w root campaign entries publicGroups after) :
    claimEntry.run ctx (inputEnvironment input.source) (state root.val campaign.val (sourceValues entries)) =
      .ok ([("nullifier", .native input.nullifier.val)],
        state input.root.val input.campaign.val (sourceValues (mark input.nullifier entries))) ∧
    after.stack = (initial input.root input.campaign (encodedEntries (mark input.nullifier entries))).stack := by
  obtain ⟨target, symbols, callDecoded, planDecoded, sat, trace, transcript, publicReads⟩ := execution
  have targetEq := Except.ok.inj (callDecoded.symm.trans callCertificate)
  have symbolsEq := Except.ok.inj (planDecoded.symm.trans planCertificate)
  subst target symbols
  have instantiate := symbolic_instantiation w (call_bindings hash input sr sc presence w publicGroups sat).2
  rw [instantiate] at trace transcript
  exact source_native_preservation ctx hash agreement input sr sc presence w publicGroups sat root campaign
    entries after ⟨trace, transcript, publicReads⟩

theorem decoded_execution_complete (planJson callJson : Lean.Json)
    (planCertificate : Verification.NativeStateJson.decode planJson = .ok symbolicPlan)
    (callCertificate : Verification.NativeRelationJson.decode callJson = .ok callProgram)
    (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (sourceInput : InputValues) (canonical : CanonicalInputs ctx sourceInput) (leaf node : Nat)
    (hashes : HashTrace ctx sourceInput leaf node) (entries : List (Scalar × _root_.Bool))
    (unused : (typedEntries (sourceValues entries)).lookup (.native sourceInput.nullifier) = none) :
    let input := Inputs.ofSource ctx sourceInput canonical agreement.modulus
    ∃ w after, DecodedExecution planJson callJson hash (callStreams input input.root input.campaign zero)
      w input.root input.campaign entries (groups (operations w)) after := by
  dsimp only
  obtain ⟨w, after, sat, execution⟩ := eligible_native_complete ctx hash agreement sourceInput canonical leaf node hashes entries unused
  let input := Inputs.ofSource ctx sourceInput canonical agreement.modulus
  have instantiate := symbolic_instantiation w
    (call_bindings hash input input.root input.campaign zero w _ sat).2
  refine ⟨w, after, callProgram, symbolicPlan, callCertificate, planCertificate, sat, ?_, ?_, execution.publicReads⟩
  · rw [instantiate]; exact execution.trace
  · rw [instantiate]

/-- Resource admission is explicit rather than a theorem about arbitrary
ledger gas parameters. The native implementation must qualify this bound. -/
theorem eligible_admitted_complete (ctx : EvalContext) (hash : Hash) (agreement : HashAgreement ctx hash)
    (sourceInput : InputValues) (canonical : CanonicalInputs ctx sourceInput) (leaf node : Nat)
    (hashes : HashTrace ctx sourceInput leaf node) (entries : List (Scalar × _root_.Bool))
    (unused : (typedEntries (sourceValues entries)).lookup (.native sourceInput.nullifier) = none)
    (budget : Budget) (operationsBudget : 21 ≤ budget.operations)
    (entriesBudget : entries.length + 1 ≤ budget.entries)
    (commit : EmptyCommunicationCommitment) (randomness : Scalar) :
    let input := Inputs.ofSource ctx sourceInput canonical agreement.modulus
    ∃ w after statement, Accepted commit randomness budget hash input input.root input.campaign zero
      w input.root input.campaign entries statement after := by
  dsimp only
  obtain ⟨w, after, sat, execution⟩ := eligible_native_complete ctx hash agreement sourceInput canonical leaf node hashes entries unused
  refine ⟨w, after, ⟨groups (operations w), after.reads.map Cell.value, List.replicate 21 Bool.true, commit randomness⟩,
    sat, execution, rfl, rfl, rfl, ?_⟩
  constructor
  · exact operationsBudget
  · simpa only [encodedEntries, List.length_map] using entriesBudget

#print axioms native_execution_sound
#print axioms source_native_preservation
#print axioms eligible_native_complete
#print axioms native_replay_rejected
#print axioms invariant_preserved
#print axioms public_transcript_preserved
end Noctium.PrivateClaimNativeState
