import Noctium.Verification.ScalarSourceReadWitness
import Noctium.Verification.GenericStateConverseRead
import Noctium.Verification.GenericStateConverseWrite
import Noctium.Verification.GenericStateConverseRequire
import Noctium.Verification.GuardedRequireSemantics
import Noctium.Verification.ScalarCellEffectEvaluation

namespace Noctium.Verification.GenericStateConverseSource

open Backend NativeState GenericStateEncoding
open GenericStateEffectValidation GenericStateCheckedReadTrace
open ScalarGuardedPlanAdmission (ScalarEffect)
open ScalarSourceReadTape (CanonicalReadAt sourceReadValuesCanonical)
open ScalarCellWitnessReadSeed (seedReadValues)

def ReadDestinationAgrees (effect : Effect) (after : SourceEffects.Frame)
    (candidate : EvalEnv) : Prop :=
  match effect with
  | .readCell _ destination _ | .readMap _ destination _ _ _ =>
    candidate.lookup destination = after.1.lookup destination
  | _ => True

/-- A read candidate reconstructed from the head record agrees with the
value that the actual source step installed. -/
theorem source_head_candidate_agreement (effect : Effect) (after : SourceEffects.Frame)
    (head : List (Impact.Read × NativeRelation.Scalar)) (candidate : EvalEnv)
    (recorded : ScalarSourceReadTape.SourceReadHeadValue effect after head)
    (candidates : ScalarCellEffectEvaluation.ReadCandidates candidate head) :
    ReadDestinationAgrees effect after candidate := by
  have matchRecord (destination : String) (ty : Ty) (value : ty.Denote)
      (lookup : after.1.lookup destination = some (Value.pack ty value))
      (canonical : ScalarNormalization.Canonical ty value)
      (headShape : head = [({name := destination, ty}, NativeRelation.scalar (number ty value))]) :
      candidate.lookup destination = after.1.lookup destination := by
    obtain ⟨support, found⟩ := candidates
      ({name := destination, ty}, NativeRelation.scalar (number ty value)) (by simp [headShape])
    change candidate.lookup destination = some (Value.pack ty
      (GenericStateInputValues.sourceValue support (NativeRelation.scalar (number ty value)))) at found
    have sameNumber : number ty value = ScalarNormalization.number support value := by
      cases support <;> rfl
    rw [sameNumber, ScalarWitnessConstruction.round_trip_scalar_read support value canonical] at found
    exact found.trans lookup.symm
  cases effect <;> try trivial
  case readCell _ destination ty =>
    obtain ⟨value, lookup, canonical, _, headShape⟩ := recorded
    exact matchRecord destination ty value lookup canonical headShape
  case readMap _ destination _ ty _ =>
    obtain ⟨value, lookup, canonical, _, headShape⟩ := recorded
    exact matchRecord destination ty value lookup canonical headShape

private theorem require_frame (ctx : EvalContext) (guard : Option (Expr .bool))
    (required : Expr .bool) (before after : SourceEffects.Frame)
    (success : GuardedSourceEffects.step ctx guard (.require required) before = .ok after) :
    after = before := by
  rcases before with ⟨env, current⟩
  cases guard with
  | none =>
    rw [GuardedSourceEffects.step_unguarded] at success
    exact (GenericStateConverseRequire.source_require_true ctx env current required after success).2
  | some condition =>
    cases evaluated : condition.eval ctx env with
    | error message =>
      rw [GuardedSourceEffects.step_guard_error ctx condition (.require required) (env, current)
        message (.require condition required) evaluated] at success
      cases success
    | ok selected =>
      change runEffectsWithGuardsAndEnv ctx [.require required] [some condition]
        env current = .ok after at success
      rw [GuardedRequireSemantics.run_guarded_require ctx env current condition required
        selected evaluated] at success
      cases selected with
      | false => exact (Except.ok.inj success).symm
      | true =>
        exact (GenericStateConverseRequire.source_require_true ctx env current required after success).2

private theorem step_read_and_encoding (ctx : EvalContext) (state : List StateDecl)
    (guard : Option (Expr .bool)) (effect : Effect) (before after : SourceEffects.Frame)
    (slots : List Slot) {types next : TypeEnv}
    (validated : EffectValidation state types effect next)
    (admitted : ScalarEffect state effect) (scope : GuardedScalarReadEffect guard effect)
    (encoded : encodeState state before.2 = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (slotBound : state.length < Field.modulus) (modulus : ctx.modulus = Field.modulus)
    (success : GuardedSourceEffects.step ctx guard effect before = .ok after) :
    CanonicalReadAt effect after ∧ ∃ nextSlots, encodeState state after.2 = some nextSlots := by
  cases validated with
  | @readCell name destination ty declared _ =>
    cases admitted with
    | cell _ cell _ =>
      cases cell with
      | readCell _ _ _ supported _ =>
        obtain ⟨declaration, found, kind⟩ := declared
        have named := beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) found)
        obtain ⟨value, lookup, canonical, unchanged⟩ :=
          GenericStateConverseRead.guarded_scalarCell_read_canonical ctx before.1 state before.2
            slots name destination ty guard after supported declaration found named kind encoded
            modulus success
        exact ⟨⟨value, lookup, canonical⟩, slots, by simpa only [unchanged] using encoded⟩
  | @readMap name destination keyTy valueTy key declared _ _ =>
    cases admitted with
    | cell _ cell _ => cases cell
    | readMap _ _ _ _ _ _ supported keyAdmitted =>
      obtain ⟨declaration, found, kind⟩ := declared
      have named := beq_iff_eq.mp (List.find?_some (p := fun item : StateDecl => item.name == name) found)
      obtain ⟨value, lookup, canonical, unchanged⟩ :=
        GenericStateConverseRead.guarded_scalarMap_read_canonical ctx before.1 state before.2
          slots name destination keyTy valueTy key keyAdmitted guard after supported declaration
          found named kind encoded modulus success
      exact ⟨⟨value, lookup, canonical⟩, slots, by simpa only [unchanged] using encoded⟩
  | @writeCell name ty value declared _ =>
    cases admitted with
    | cell _ _ operand =>
      obtain ⟨declaration, found, kind⟩ := declared
      exact ⟨trivial, GenericStateConverseWrite.guarded_source_writeCell_encoded ctx state before.1
        before.2 after name ty value guard slots encoded declaration found kind distinct slotBound
        operand modulus success⟩
  | @writeMap name keyTy valueTy key value declared _ _ =>
    cases admitted with
    | cell _ cell _ => cases cell
    | writeMap _ _ _ _ _ _ _ keyAdmitted valueAdmitted =>
      obtain ⟨declaration, found, kind⟩ := declared
      exact ⟨trivial, GenericStateConverseWrite.guarded_source_writeMap_encoded ctx state before.1
        before.2 after name keyTy valueTy key value guard slots encoded declaration found kind distinct
        slotBound keyAdmitted valueAdmitted modulus success⟩
  | @require required _ =>
    have same := require_frame ctx guard required before after success
    subst after
    exact ⟨trivial, slots, encoded⟩
  | @requireAbsent name keyTy key valueTy _ _ =>
    cases scope with
    | unguarded _ =>
      cases admitted with
      | cell _ cell _ => cases cell
      | requireAbsent _ _ _ _ keyAdmitted =>
        rw [GuardedSourceEffects.step_unguarded] at success
        obtain ⟨_, _, _, _, _, _, same⟩ :=
          GenericStateSourceTrace.requireAbsent_step_key ctx before.1 before.2 name keyTy key
            keyAdmitted after modulus success
        rw [same]
        exact ⟨trivial, slots, encoded⟩

private theorem canonical_fold (ctx : EvalContext) (state : List StateDecl) (entry : Entrypoint)
    {types finalTypes : TypeEnv} {items : List (Effect × Nat)}
    (validated : GuardValidatedEffects state entry types items finalTypes)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (slotBound : state.length < Field.modulus) (modulus : ctx.modulus = Field.modulus) :
    ∀ (before after : SourceEffects.Frame) (slots : List Slot),
      (∀ item ∈ items, ScalarEffect state item.1) →
      GuardedScalarReadEffects entry.effectGuards items →
      encodeState state before.2 = some slots →
      GuardedSourceEffects.fold ctx entry.effectGuards items before = .ok after →
      sourceReadValuesCanonical ctx entry.effectGuards items before := by
  induction validated with
  | nil => intro before after slots admitted scope encoded folded; trivial
  | @cons _ _ _ item rest head _ _ ih =>
    intro before after slots admitted scope encoded folded
    rw [GuardedSourceEffects.fold_cons] at folded
    cases step : GuardedSourceEffects.step ctx (entry.effectGuards[item.2]?.getD none)
        item.1 before with
    | error message => simp [step, Except.bind] at folded
    | ok middle =>
      have remaining : GuardedSourceEffects.fold ctx entry.effectGuards rest middle = .ok after := by
        simpa only [step, Except.bind] using folded
      obtain ⟨canonical, nextSlots, nextEncoded⟩ := step_read_and_encoding ctx state
        (entry.effectGuards[item.2]?.getD none) item.1 before middle slots head
        (admitted item (by simp)) (scope item (by simp)) encoded distinct slotBound modulus step
      rw [sourceReadValuesCanonical, step]
      exact ⟨canonical, ih middle after nextSlots
        (fun found present => admitted found (List.mem_cons_of_mem _ present))
        (fun found present => scope found (List.mem_cons_of_mem _ present)) nextEncoded remaining⟩

/-- Accepted scalar effects preserve encoded state and bind canonical read
values at every reached frame of a successful source call. -/
theorem accepted_entrypoint_reads_canonical (ctx : EvalContext) (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (values result : EvalEnv)
    (initial next : LedgerState) (slots : List Slot)
    (lowered : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (effects : ∀ effect ∈ entry.effects, ScalarEffect state effect)
    (admitted : AdmittedState state initial slots) (modulus : ctx.modulus = Field.modulus)
    (success : entry.run ctx values initial = .ok (result, next)) :
    ∀ outputs, entry.circuit.run ctx values = .ok outputs →
      sourceReadValuesCanonical ctx entry.effectGuards entry.effects.zipIdx
        (outputs ++ values,
          {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}) := by
  intro outputs source
  obtain ⟨actual, finalEnv, _, circuit, folded, _, _⟩ :=
    ScalarSourceReadWitness.accepted_entrypoint_source_fold state entry plan ctx values result
      initial next lowered effects success
  have same := Except.ok.inj (circuit.symm.trans source)
  subst outputs
  let ep := Passes.pruneEntrypoint entry
  have scalarEffects := ScalarGuardedActivityAdmission.scalar_state_effects_of_admitted
    state ep.effects effects
  obtain ⟨_, validated, _⟩ := lower_validated_guarded_effects_and_returns state ep plan lowered scalarEffects
  have scope := ScalarGuardedActivityAdmission.lower_guarded_scalar_read_scope state ep plan lowered effects
  have encoded := admitted.encoded
  exact canonical_fold ctx state ep validated admitted.distinctDeclarations admitted.slotBound
    modulus _ (finalEnv, next) slots
    (fun item present => effects item.1 (List.fst_mem_of_mem_zipIdx present)) scope encoded folded

/-- Derive the witness read seed from a successful source call on an admitted
initial ledger, with the exact accepted read order and original input lanes. -/
theorem source_assignment_of_entry_run (ctx : EvalContext) (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (values result : EvalEnv)
    (initial next : LedgerState) (slots : List Slot) (inputs : NativeRelation.Assignment)
    (lowered : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (effects : ∀ effect ∈ entry.effects, ScalarEffect state effect)
    (admitted : AdmittedState state initial slots) (modulus : ctx.modulus = Field.modulus)
    (success : entry.run ctx values initial = .ok (result, next)) :
    let cutoff := Impact.publicInputReadCount entry.circuit.inputs
    let reads := plan.reads.drop cutoff
    ∃ outputs finalEnv returned records readValues,
      entry.circuit.run ctx values = .ok outputs ∧
      entry.evalReturns ctx finalEnv = .ok returned ∧ result = outputs ++ returned ∧
      ScalarSourceReadTape.sourceReadInputs ctx entry.effectGuards entry.effects.zipIdx cutoff
        (outputs ++ values,
          {initial with unshieldedInputs := [], unshieldedOutputs := [], unshieldedSpendClaims := []}) =
        .ok (records, (finalEnv, next)) ∧
      reads.map readMetadata = (records.map Prod.fst).map readMetadata ∧
      (∀ input ∈ entry.circuit.inputs,
        seedReadValues inputs records ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
      GenericStateInputValues.decodeReads reads (seedReadValues inputs records) = .ok readValues ∧
      readValues.map Prod.fst = records.map (fun record => record.1.name) := by
  exact ScalarSourceReadWitness.accepted_entrypoint_source_read_witness state entry plan ctx
    inputs values result initial next lowered effects success
    (accepted_entrypoint_reads_canonical ctx state entry plan values result initial next slots
      lowered effects admitted modulus success)

end Noctium.Verification.GenericStateConverseSource
