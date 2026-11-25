import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.ScalarNormalizationSoundness

namespace Noctium.Verification.ScalarLedgerReturnObservation

open Backend Backend.Native NativeRelation ScalarNormalization
open GenericStateCircuitParts

private theorem bind_ok {α β : Type} {first : Except String α}
    {next : α → Except String β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem evalOutput_value (ctx : EvalContext) (values : EvalEnv)
    (output : Output) (pair : String × Value)
    (accepted : evalOutput ctx values output = .ok pair) :
    ∃ value, output.value.eval ctx values = .ok value ∧
      pair = (output.name, Value.pack output.ty value) := by
  unfold evalOutput at accepted
  cases evaluated : output.value.eval ctx values with
  | error message => simp [evaluated, Bind.bind, Except.bind] at accepted
  | ok value =>
    simp only [Bind.bind, Except.bind, evaluated, Pure.pure, Except.pure] at accepted
    exact ⟨value, rfl, (Except.ok.inj accepted).symm⟩

private theorem normalized_return_observations (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (witness : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv)
    (aliasAgreement : AliasAgreement hash witness aliases values)
    (outputs : List Output) (normalized : List Normalized) (returned : EvalEnv)
    (admitted : ∀ output ∈ outputs, ScalarExpression output.value)
    (supported : ∀ output ∈ outputs, Nonempty (ScalarType output.ty))
    (normal : outputs.mapM (fun output => normalize aliases output.value) = .ok normalized)
    (source : outputs.mapM (evalOutput ctx values) = .ok returned) :
    normalized.map (fun item => interpret hash witness item.term) =
      returned.map (fun binding => some (scalar (valueNumber binding.2))) := by
  induction outputs generalizing normalized returned with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at normal source
    subst normalized
    subst returned
    rfl
  | cons output outputs ih =>
    simp only [List.mapM_cons, bind_ok] at normal source
    obtain ⟨head, headNormal, tail, tailNormal, normalShape⟩ := normal
    obtain ⟨pair, pairEval, tailPairs, tailEval, sourceShape⟩ := source
    cases normalShape
    cases sourceShape
    obtain ⟨value, evaluated, pairShape⟩ :=
      evalOutput_value ctx values output pair pairEval
    obtain ⟨scalarType⟩ := supported output (by simp)
    have expressionAdmission := admitted output (by simp)
    obtain ⟨normalizedOutput, normalizedEval, represents⟩ := normalize_success
      ctx hash implementation witness aliases values aliasAgreement output.value
      expressionAdmission value evaluated
    have normalizedSame : head = normalizedOutput :=
      Except.ok.inj (headNormal.symm.trans normalizedEval)
    have headObservation :
        interpret hash witness head.term = some (scalar (valueNumber pair.2)) := by
      rw [normalizedSame, represents.2.2, pairShape, valueNumber_pack_scalar]
      rw [sourceScalar_number scalarType value]
    have tailAdmission : ∀ item ∈ outputs, ScalarExpression item.value := by
      intro item member
      exact admitted item (List.mem_cons_of_mem _ member)
    have tailSupported : ∀ item ∈ outputs, Nonempty (ScalarType item.ty) := by
      intro item member
      exact supported item (List.mem_cons_of_mem _ member)
    have tailResult := ih tail tailPairs tailAdmission tailSupported tailNormal tailEval
    simp only [List.map_cons, headObservation, tailResult]

/-- The accepted expected return terms observe the same scalar values and
preserve the source return order. -/
theorem expected_returns_observe_source (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan) (expected : Expected) (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (witness : Assignment)
    (sourceFrame : OutputFrame) (values returned : EvalEnv)
    (lowered : Impact.lower state entry = .ok plan)
    (accepted : Native.expectedEntrypoint state entry = .ok expected)
    (frameAccepted : normalizeOutputs (entrypointSeedAliases entry plan)
      entry.circuit.outputs = .ok sourceFrame)
    (sourceAliases : AliasAgreement hash witness sourceFrame.1 values)
    (scalarReads : ∀ read ∈
      (plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)).flatMap
        Impact.Read.scalarReads, scalarAliasReadType read.ty)
    (scalarReturns : ∀ output ∈ entry.returns,
      ∃ _scalarType : ScalarType output.ty, ScalarExpression output.value)
    (source : entry.returns.mapM (evalOutput ctx values) = .ok returned) :
    expected.returns.map (interpret hash witness) =
      returned.map (fun binding => some (scalar (valueNumber binding.2))) := by
  obtain ⟨outputFrame, normalized, outputFrameAccepted, normal, exactReturns, _, _⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_scalar_returns state entry expected plan
      lowered accepted scalarReads
      (fun output member => ⟨(scalarReturns output member).choose⟩)
  have frameEq : outputFrame = sourceFrame :=
    Except.ok.inj (outputFrameAccepted.symm.trans frameAccepted)
  subst outputFrame
  have normalizedValues := normalized_return_observations ctx hash implementation witness
    sourceFrame.1 values sourceAliases entry.returns normalized returned
    (fun output member => (scalarReturns output member).choose_spec)
    (fun output member => ⟨(scalarReturns output member).choose⟩) normal source
  rw [exactReturns]
  simpa only [List.map_map, Function.comp_def] using normalizedValues

end Noctium.Verification.ScalarLedgerReturnObservation
