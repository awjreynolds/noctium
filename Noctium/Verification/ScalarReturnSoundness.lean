import Noctium.Verification.GenericStatePrefixEnvironment
import Noctium.Verification.ScalarCircuit

namespace Noctium.Verification.ScalarReturnSoundness

open Backend.Native NativeRelation ScalarNormalization

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem evalReturns_cons_scalar (ctx : EvalContext) (entry : Entrypoint)
    (env : EvalEnv) (output : Output) (rest : List Output) (tail : EvalEnv)
    (value : output.ty.Denote) (scalarType : ScalarType output.ty)
    (canonical : Canonical output.ty value) (modulus : ctx.modulus = Field.modulus)
    (evaluated : output.value.eval ctx env = .ok value)
    (remaining : Entrypoint.evalReturns ctx {entry with returns := rest} env = .ok tail) :
    Entrypoint.evalReturns ctx {entry with returns := output :: rest} env =
      .ok ((output.name, Value.pack output.ty value) :: tail) := by
  unfold Entrypoint.evalReturns at remaining ⊢
  dsimp only at remaining ⊢
  rw [List.mapM_cons, evaluated]
  simp [canonical_eq, modulus, Bind.bind, Except.bind, Pure.pure, Except.pure] at remaining
  cases output with
  | mk name ty expression span =>
    cases scalarType <;>
      simp [Canonical, sourceNumber?] at canonical <;>
      simp [canonical_eq, modulus, canonical, remaining, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Evaluate the ordered, checked scalar return terms in the final source
environment and recover their exact ABI field observations. -/
theorem normalized_scalar_return_values (ctx : EvalContext) (entry : Entrypoint)
    (hash : Hash) (implementation : HashAgreement ctx hash) (witness : Assignment)
    (aliases : AliasEnvironment) (finalEnv complete : EvalEnv) (finalTypes : TypeEnv)
    (typed : TypedEnvironment hash witness aliases complete finalTypes)
    (agreement : GenericStatePrefixEnvironment.AgreesOnTypes finalTypes finalEnv complete)
    (outputs : List Output) (normalized : List Normalized)
    (supported : ∀ output ∈ outputs, Nonempty (ScalarType output.ty))
    (admitted : ∀ output ∈ outputs, ScalarExpression output.value)
    (valid : ∀ output ∈ outputs,
      output.value.validate Capabilities.scalarFragment finalTypes = .ok ())
    (normal : outputs.mapM (fun output => normalize aliases output.value) = .ok normalized)
    (bounds : ∀ requirement ∈ normalized.flatMap (·.bounds),
      ∃ value, interpret hash witness requirement.1 = some value ∧ value.val ≤ requirement.2)
    (assertions : ∀ term ∈ normalized.flatMap (·.assertions),
      interpret hash witness term = some one) :
    ∃ returned,
      Entrypoint.evalReturns ctx {entry with returns := outputs} finalEnv = .ok returned ∧
      normalized.map (fun value => interpret hash witness value.term) =
        returned.map (fun binding => some (scalar (valueNumber binding.2))) := by
  induction outputs generalizing normalized with
  | nil =>
    cases normal
    exact ⟨[], rfl, rfl⟩
  | cons output rest ih =>
    simp only [List.mapM_cons, bind_ok] at normal
    obtain ⟨head, headChecked, tail, tailChecked, exactNormals⟩ := normal
    cases exactNormals
    have obligations : Requirements hash witness head :=
      ⟨fun requirement member => bounds requirement (by simp [member]),
       fun term member => assertions term (by simp [member])⟩
    obtain ⟨scalarType⟩ := supported output (by simp)
    have checked := valid output (by simp)
    obtain ⟨value, evaluated, represented⟩ := normalize_sound ctx hash implementation witness
      finalTypes aliases complete typed output.value (admitted output (by simp))
      head checked headChecked obligations
    have sourceEvaluation : output.value.eval ctx finalEnv = .ok value :=
      (GenericStatePrefixEnvironment.eval_scoped finalTypes finalEnv complete agreement
        ctx Capabilities.scalarFragment output.value checked).trans evaluated
    obtain ⟨tailValues, tailEvaluation, tailMeaning⟩ := ih tail
      (fun item member => supported item (List.mem_cons_of_mem _ member))
      (fun item member => admitted item (List.mem_cons_of_mem _ member))
      (fun item member => valid item (List.mem_cons_of_mem _ member)) tailChecked
      (fun requirement member => bounds requirement (by simp [member]))
      (fun term member => assertions term (by simp [member]))
    refine ⟨(output.name, Value.pack output.ty value) :: tailValues,
      evalReturns_cons_scalar ctx entry finalEnv output rest tailValues value scalarType
        represented.1 implementation.modulus sourceEvaluation tailEvaluation, ?_⟩
    simp only [List.map_cons, represented.2.2, sourceScalar_number scalarType value,
      valueNumber_pack_scalar output.ty value scalarType, tailMeaning]

end Noctium.Verification.ScalarReturnSoundness
