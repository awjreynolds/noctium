import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.GenericStateAliases
import Noctium.Verification.ScalarCircuit
import Noctium.Verification.ScalarNormalizationSoundness

namespace Noctium.Verification.GenericStateOutputCompleteness
open Backend.Native NativeRelation ScalarNormalization GenericStateCircuitParts

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem normalizeOutput_ok (aliases : AliasEnvironment) (output : Output)
    (normalized : Normalized)
    (accepted : normalizeOutput aliases output = .ok normalized) :
    normalize aliases output.value = .ok normalized := by
  unfold normalizeOutput at accepted
  cases checked : normalize aliases output.value with
  | error message => simp [checked, Except.mapError] at accepted
  | ok found =>
    simp [checked, Except.mapError] at accepted
    subst normalized
    rfl

private theorem outputEval_ok (ctx : EvalContext) (values : EvalEnv)
    (output : Output) (pair : String × Value)
    (accepted : evalOutput ctx values output = .ok pair) :
    ∃ value, output.value.eval ctx values = .ok value ∧
      pair = (output.name, Value.pack output.ty value) := by
  unfold evalOutput at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨value, evaluated, produced⟩
  cases produced
  exact ⟨value, evaluated, rfl⟩

/-- Successful evaluation of scalar-admitted outputs establishes the
requirements of the production output fold. The normalized alias stack
prepends outputs, so its value environment is `results.reverse ++
accumulatedBindings`. The results stay in source order. -/
theorem outputFold_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (originalValues accumulatedBindings : EvalEnv)
    (outputs : List Output)
    (admitted : ∀ output ∈ outputs, ScalarExpression output.value)
    (frame final : OutputFrame)
    (results : List (String × Value))
    (originalAgreement : AliasAgreement hash inputs frame.1 originalValues)
    (bindingAgreement : AliasAgreement hash inputs frame.1 accumulatedBindings)
    (unused : ∀ output ∈ outputs, originalValues.lookup output.name = none)
    (source : outputs.mapM (evalOutput ctx originalValues) = .ok results)
    (accepted : outputFold frame outputs = .ok final)
    (beforeBounds : ∀ requirement ∈ frame.2.1,
      ∃ value, interpret hash inputs requirement.1 = some value ∧
        value.val ≤ requirement.2)
    (beforeAssertions : ∀ term ∈ frame.2.2,
      interpret hash inputs term = some one) :
    (∀ requirement ∈ final.2.1,
      ∃ value, interpret hash inputs requirement.1 = some value ∧
        value.val ≤ requirement.2) ∧
    (∀ term ∈ final.2.2, interpret hash inputs term = some one) ∧
    AliasAgreement hash inputs final.1 originalValues ∧
    AliasAgreement hash inputs final.1 (results.reverse ++ accumulatedBindings) := by
  induction outputs generalizing frame final results accumulatedBindings with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at source
    subst results
    simp [outputFold] at accepted
    cases accepted
    simp only [List.reverse_nil, List.nil_append]
    exact ⟨beforeBounds, beforeAssertions, originalAgreement, bindingAgreement⟩
  | cons output rest ih =>
    rw [outputFold_cons] at accepted
    change (appendOutput output frame >>= fun next => outputFold next rest) =
      .ok final at accepted
    simp only [bind_ok] at accepted
    obtain ⟨middle, first, later⟩ := accepted
    unfold appendOutput at first
    change (normalizeOutput frame.1 output >>= fun result =>
      Except.ok ((output.name, result.term) :: frame.1,
        frame.2.1 ++ result.bounds, frame.2.2 ++ result.assertions)) =
      .ok middle at first
    simp only [bind_ok] at first
    obtain ⟨normalized, normalAccepted, appended⟩ := first
    let nextFrame : OutputFrame :=
      ((output.name, normalized.term) :: frame.1,
        frame.2.1 ++ normalized.bounds, frame.2.2 ++ normalized.assertions)
    have nextEq : nextFrame = middle := (Except.ok.inj appended)
    rw [← nextEq] at later
    have normal : normalize frame.1 output.value = .ok normalized :=
      normalizeOutput_ok frame.1 output normalized normalAccepted
    rw [List.mapM_cons] at source
    change (evalOutput ctx originalValues output >>= fun pair =>
      (rest.mapM (evalOutput ctx originalValues) >>= fun tail =>
        Except.ok (pair :: tail))) = .ok results at source
    simp only [bind_ok] at source
    obtain ⟨pair, pairAccepted, tailResults, tailAccepted, resultShape⟩ := source
    cases resultShape
    obtain ⟨value, evaluated, pairShape⟩ :=
      outputEval_ok ctx originalValues output pair pairAccepted
    subst pair
    have represented := normalize_success ctx hash implementation inputs
      frame.1 originalValues originalAgreement output.value
      (admitted output (by simp)) value evaluated
    obtain ⟨normalizedSource, normalizedEval, represented⟩ := represented
    rw [normal] at normalizedEval
    cases normalizedEval
    obtain ⟨canonical, requirements, meaning⟩ := represented
    have middleBounds : ∀ requirement ∈ nextFrame.2.1,
        ∃ value, interpret hash inputs requirement.1 = some value ∧
          value.val ≤ requirement.2 := by
      intro requirement member
      simp [nextFrame] at member
      rcases member with prior | generated
      · exact beforeBounds requirement prior
      · exact requirements.1 requirement generated
    have middleAssertions : ∀ term ∈ nextFrame.2.2,
        interpret hash inputs term = some one := by
      intro term member
      simp [nextFrame] at member
      rcases member with prior | generated
      · exact beforeAssertions term prior
      · exact requirements.2 term generated
    have nextOriginal : AliasAgreement hash inputs nextFrame.1 originalValues := by
      simpa [nextFrame] using GenericStateAliases.aliasAgreement_cons_unused hash inputs
        frame.1 originalValues output.name normalized.term originalAgreement
        (unused output (by simp))
    have nextBindings : AliasAgreement hash inputs nextFrame.1
        ((output.name, Value.pack output.ty value) :: accumulatedBindings) := by
      simpa [nextFrame] using ScalarNormalization.aliasAgreement_cons hash inputs frame.1
        accumulatedBindings output.name output.ty value normalized.term
        bindingAgreement canonical meaning
    obtain ⟨bounds, assertions, original, bindings⟩ :=
      ih ((output.name, Value.pack output.ty value) :: accumulatedBindings)
        (fun item member => admitted item (by simp [member]))
        nextFrame final tailResults
        nextOriginal nextBindings
        (fun item member => unused item (by simp [member]))
        tailAccepted later middleBounds middleAssertions
    refine ⟨bounds, assertions, original, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using bindings

/-- The wrapper starts with no generated requirements and uses the same
initial alias agreement for original inputs and the empty binding stack. -/
theorem normalizeOutputs_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv)
    (outputs : List Output)
    (admitted : ∀ output ∈ outputs, ScalarExpression output.value)
    (final : OutputFrame)
    (results : List (String × Value))
    (agreement : AliasAgreement hash inputs aliases values)
    (unused : ∀ output ∈ outputs, values.lookup output.name = none)
    (source : outputs.mapM (evalOutput ctx values) = .ok results)
    (accepted : normalizeOutputs aliases outputs = .ok final) :
    (∀ requirement ∈ final.2.1,
      ∃ value, interpret hash inputs requirement.1 = some value ∧
        value.val ≤ requirement.2) ∧
    (∀ term ∈ final.2.2, interpret hash inputs term = some one) ∧
    AliasAgreement hash inputs final.1 values ∧
    AliasAgreement hash inputs final.1 (results.reverse ++ values) := by
  exact outputFold_complete ctx hash implementation inputs values values outputs
    admitted (aliases, [], []) final results agreement agreement unused source
    (by simpa [normalizeOutputs] using accepted)
    (by simp) (by simp)

end Noctium.Verification.GenericStateOutputCompleteness
