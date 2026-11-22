import Noctium.Verification.ScalarCircuit
import Noctium.Verification.ScalarValidation
import Noctium.Verification.ScalarCircuitLowering
import Noctium.Verification.ScalarExpressionLowering

namespace Noctium.Verification.ScalarTranslation
open Backend Native NativeRelation ScalarNormalization

private theorem schema_source (witness : Assignment) (visibility : Visibility) (inputs : List Input) :
    ScalarValidation.schemaValues witness visibility
      ((inputs.map (fun input => ({identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty} : InputRequirement))).map ScalarValidation.inputSchema) =
      (inputs.filter (·.visibility == visibility)).map (fun input => witness ("%input_" ++ input.name)) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    simp only [List.map_cons, ScalarValidation.inputSchema, ScalarValidation.schemaValues,
      List.filterMap_cons, List.filter_cons]
    split <;> simp_all [ScalarValidation.schemaValues]

/-- The existing scalar lowering and mandatory validator preserve successful
source execution for arbitrary satisfying internal assignments. The final
Impact group, rather than standalone Output, binds nonempty source returns. -/
theorem lowerCircuit_sound (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit) (values : EvalEnv)
    (json : Lean.Json) (relation : Program) (streams : InputStreams)
    (witness : Assignment) (publicGroups : List (List Scalar))
    (admitted : CanonicalInputs circuit values witness)
    (lowered : Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ result, circuit.run ctx values = .ok result ∧
      result.map Prod.fst = circuit.outputs.map (·.name) ∧
      relation.returns witness = result.map (fun pair => scalar (valueNumber pair.2)) ∧
      streams.publicValues = (circuit.inputs.filter (·.visibility == .«public»)).map
        (fun input => witness ("%input_" ++ input.name)) ∧
      streams.privateValues = (circuit.inputs.filter (·.visibility == .«private»)).map
        (fun input => witness ("%input_" ++ input.name)) ∧
      publicGroups = (circuit.inputs.filter (·.visibility == .«public»)).map
        (fun input => [witness ("%input_" ++ input.name)]) ++
          (if result.isEmpty then [] else [result.map (fun pair => scalar (valueNumber pair.2))]) ∧
      (result ≠ [] → relation.returns witness = publicGroups.getLastD []) ∧
      (∀ input ∈ circuit.inputs, (witness ("%input_" ++ input.name)).val ≤ sourceMaximum input.ty) := by
  obtain ⟨expected, expectedAccepted, nativeAccepted⟩ := Zkir.lowerCircuit_validated circuit json lowered
  have validated := ScalarValidation.validate_sound (inputs := witness) (by intro requirement member; rfl)
    nativeAccepted decoded satisfies
  have prunedInputs : CanonicalInputs (Passes.pruneCircuit circuit) values witness :=
    ⟨admitted.unique, admitted.declared, admitted.complete, admitted.binding⟩
  obtain ⟨result, source, names, returns, groups⟩ := expectedCircuit_sound ctx hash implementation witness
    (Passes.pruneCircuit circuit) values expected prunedInputs expectedAccepted
    validated.requirements.bounds validated.requirements.assertions
  have hostReturns : relation.returns witness = result.map (fun pair => scalar (valueNumber pair.2)) :=
    validated.returns.trans returns.symm
  have publicBinding : publicGroups = (circuit.inputs.filter (·.visibility == .«public»)).map
      (fun input => [witness ("%input_" ++ input.name)]) ++
        (if result.isEmpty then [] else [result.map (fun pair => scalar (valueNumber pair.2))]) :=
    validated.groups.trans groups
  obtain ⟨_, _, _, _, _, _, _, _, _, inputShape, _, _⟩ :=
    expectedCircuit_parts (Passes.pruneCircuit circuit) expected expectedAccepted
  refine ⟨result, ?_, names, hostReturns, ?_, ?_, publicBinding, ?_, ?_⟩
  · simpa only [Passes.pruneCircuit_run] using source
  · rw [validated.publicInputs, inputShape, schema_source]
    rfl
  · rw [validated.privateInputs, inputShape, schema_source]
    rfl
  · intro nonempty
    rw [hostReturns, publicBinding]
    have notEmpty : result.isEmpty = false := by cases result <;> simp_all
    rw [notEmpty]
    simp only [Bool.false_eq_true, ↓reduceIte, List.getLastD_concat]
  · intro input member
    apply validated.requirements.inputBounds
      {identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}
    rw [inputShape]
    exact List.mem_map.mpr ⟨input, member, rfl⟩

/-- The native witness is constructed from the real lowering computation before
validator soundness identifies its observations. Expression completeness is an
internal composition parameter discharged by the public theorem below. -/
private theorem lowerCircuit_complete_with_expressions (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (complete : ∀ ty (expression : Expr ty), ScalarLowering.ExprComplete expression)
    (circuit : Circuit) (values result : EvalEnv) (inputs : Assignment)
    (json : Lean.Json) (relation : Program)
    (admitted : CanonicalInputs circuit values inputs)
    (lowered : Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (success : circuit.run ctx values = .ok result) :
    ∃ witness, (∀ name, witness ("%input_" ++ name) = inputs ("%input_" ++ name)) ∧
      Satisfies hash relation
        {publicValues := (circuit.inputs.filter (·.visibility == .«public»)).map
          (fun input => inputs ("%input_" ++ input.name)),
         privateValues := (circuit.inputs.filter (·.visibility == .«private»)).map
          (fun input => inputs ("%input_" ++ input.name))}
        witness
        ((circuit.inputs.filter (·.visibility == .«public»)).map
          (fun input => [inputs ("%input_" ++ input.name)]) ++
          (if result.isEmpty then [] else [result.map (fun pair => scalar (valueNumber pair.2))]))
        (result.map (fun pair => scalar (valueNumber pair.2))) := by
  obtain ⟨witness, frame, instructions⟩ := ScalarCircuitLowering.lowerCircuit_witness_with_expressions
    ctx hash implementation complete circuit values result inputs json relation admitted lowered decoded success
  change ∀ name, witness ("%input_" ++ name) = inputs ("%input_" ++ name) at frame
  have witnessInputs : CanonicalInputs circuit values witness :=
    ⟨admitted.unique, admitted.declared, admitted.complete,
      fun input member value lookup => (frame input.name).trans (admitted.binding input member value lookup)⟩
  let streams : InputStreams :=
    {publicValues := relation.inputValues .«public» witness, privateValues := relation.inputValues .«private» witness}
  have selfSat : CircuitSatisfies hash relation streams witness (relation.groups witness) :=
    ⟨instructions, rfl, rfl, rfl⟩
  obtain ⟨observed, observedRun, names, returns, publicInputs, privateInputs, groups, finalGroup, ranges⟩ :=
    lowerCircuit_sound ctx hash implementation circuit values json relation streams witness (relation.groups witness)
      witnessInputs lowered decoded selfSat
  have same : observed = result := Except.ok.inj (observedRun.symm.trans success)
  subst observed
  refine ⟨witness, frame, instructions, ?_, ?_, ?_, returns⟩
  · simpa only [streams, frame] using publicInputs
  · simpa only [streams, frame] using privateInputs
  · simpa only [frame] using groups

/-- Successful source execution extends to a satisfying witness for the actual
admitted emitted program. Decoder acceptance is a syntactic admission premise.
All public groups and returns are fixed by the original source execution. -/
theorem lowerCircuit_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (circuit : Circuit) (values result : EvalEnv) (inputs : Assignment)
    (json : Lean.Json) (relation : Program)
    (admitted : CanonicalInputs circuit values inputs)
    (lowered : Zkir.lowerCircuit circuit = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (success : circuit.run ctx values = .ok result) :
    ∃ witness, (∀ name, witness ("%input_" ++ name) = inputs ("%input_" ++ name)) ∧
      Satisfies hash relation
        {publicValues := (circuit.inputs.filter (·.visibility == .«public»)).map
          (fun input => inputs ("%input_" ++ input.name)),
         privateValues := (circuit.inputs.filter (·.visibility == .«private»)).map
          (fun input => inputs ("%input_" ++ input.name))}
        witness
        ((circuit.inputs.filter (·.visibility == .«public»)).map
          (fun input => [inputs ("%input_" ++ input.name)]) ++
          (if result.isEmpty then [] else [result.map (fun pair => scalar (valueNumber pair.2))]))
        (result.map (fun pair => scalar (valueNumber pair.2))) := by
  exact lowerCircuit_complete_with_expressions ctx hash implementation
    (fun _ expression => ScalarExpressionLowering.lowerExpr_complete expression)
    circuit values result inputs json relation admitted lowered decoded success

end Noctium.Verification.ScalarTranslation
