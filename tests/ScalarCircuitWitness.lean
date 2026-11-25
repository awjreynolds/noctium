import Noctium.Compiler
import Noctium.Verification.ScalarCircuitWitness
import Noctium.Verification.ScalarExpressionAssert
import Noctium.Verification.ScalarExpressionCopy
import Noctium.Verification.ScalarExpressionEquality
import Noctium.Verification.ScalarExpressionNativeTree
import Noctium.Verification.ScalarExpressionUIntAdd

open Lean Noctium Noctium.Backend Noctium.Verification
open NativeRelation NativeRelationJson ScalarNormalization ScalarLowering ScalarWitnessConstruction
open ScalarTranslationSoundness (defaultLoweredRows)
open ScalarValidationOpcodeProfile (checkedScalarOpcodeProfile)

section Source
open scoped Noctium

noctium_circuit scalarCircuitWitnessExample where
  public enabled : Bool
  private amount : UIntRange 201
  private left : Native
  private right : Native
  assert eq(enabled, copyValue(true))
  output total : Native := disclose(copyValue(add(add(0, left), right)))
  output amountPlus : UIntRange 202 := disclose(assertThen(enabled, add(amount, uint(1))))
end

end Source

private def runExample (enabled : _root_.Bool) :=
  scalarCircuitWitnessExample.run
    {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "fixture has no hash"}
    [("enabled", .bool enabled), ("amount", .uint 200 200),
     ("left", .native 17), ("right", .native 25)]

#guard match runExample Bool.true with
  | .ok values => values.map Prod.snd == [.native 42, .uint 201 201]
  | .error _ => Bool.false

#guard !(runExample Bool.false).isOk

#guard match Zkir.lowerCircuit scalarCircuitWitnessExample with
  | .ok json =>
    match NativeRelationJson.decode json with
    | .ok program =>
      checkedScalarOpcodeProfile
        (defaultLoweredRows scalarCircuitWitnessExample).toList.zipIdx program.instructions
    | .error _ => Bool.false
  | .error _ => Bool.false

#guard !(decodeInstruction (Json.mkObj [
  ("op", toJson ("copy" : String)),
  ("val", toJson ("0x01" : String)),
  ("output", toJson ("0x02" : String))])).isOk

private theorem exampleAdmission : ScalarCircuitAdmission scalarCircuitWitnessExample := by
  constructor
  · intro condition present
    simp only [scalarCircuitWitnessExample, List.mem_singleton] at present
    subst condition
    exact .eq _ _ .bool (.ref "enabled" .bool) (.copyValue _ (.bool Bool.true))
  · intro returned present
    simp only [scalarCircuitWitnessExample, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨.native, .disclose _ _ (.copyValue _
        (nativeArithmeticTree_complete (.add (.add (.literal 0) (.ref "left")) (.ref "right"))).1)⟩
    · exact ⟨.uint 201, .disclose _ _ (.assertE _ _ (.ref "enabled" .bool)
        (.uadd _ _ (.ref "amount" (.uint 200)) (.uint 1 1)))⟩

private theorem exampleConditions : ∀ condition ∈ scalarCircuitWitnessExample.constraints,
    ExprComplete condition := by
  intro condition present
  simp only [scalarCircuitWitnessExample, List.mem_singleton] at present
  subst condition
  exact complete_scalar_eq _ _ .bool (.ref "enabled" .bool) (.copyValue _ (.bool Bool.true))
    (complete_ref .bool .bool "enabled")
    (complete_copyValue _ (.bool Bool.true) (complete_bool Bool.true))

private theorem exampleReturns : ∀ returned ∈ scalarCircuitWitnessExample.outputs,
    ExprComplete returned.value := by
  intro returned present
  simp only [scalarCircuitWitnessExample, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · have arithmetic := nativeArithmeticTree_complete
      (.add (.add (.literal 0) (.ref "left")) (.ref "right"))
    exact complete_disclose _ _ (complete_copyValue _ arithmetic.1 arithmetic.2)
  · have amount : ScalarExpression (.ref (ty := .uint 200) "amount") :=
      .ref "amount" (.uint 200)
    have literalSupported : ScalarExpression (.uint 1 1) := .uint 1 1
    have sum := complete_uadd _ _ amount literalSupported
      (complete_ref (.uint 200) (.uint 200) "amount") (complete_uint 1 1)
    exact complete_disclose _ _ (exprComplete_assertE _ _ (.ref "enabled" .bool)
      (.uadd _ _ amount literalSupported) (complete_ref .bool .bool "enabled") sum)

/-- Every successful run of this mixed scalar source circuit has an assignment
for the checked emitted relation, including both observed return fields. -/
theorem scalarCircuitWitnessExample_complete (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (values result : EvalEnv)
    (inputs : NativeRelation.Assignment) (json : Json) (relation : Program)
    (admitted : CanonicalInputs scalarCircuitWitnessExample values inputs)
    (lowered : Zkir.lowerCircuit scalarCircuitWitnessExample = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (profile : checkedScalarOpcodeProfile
      (defaultLoweredRows scalarCircuitWitnessExample).toList.zipIdx relation.instructions = Bool.true)
    (success : scalarCircuitWitnessExample.run ctx values = .ok result) :
    ∃ assignment, InputFrame inputs assignment ∧
      Satisfies hash relation
        {publicValues := [inputs "%input_enabled"],
         privateValues := [inputs "%input_amount", inputs "%input_left", inputs "%input_right"]}
        assignment
        ([[inputs "%input_enabled"]] ++
          (if result.isEmpty then [] else [result.map (fun pair => scalar (valueNumber pair.2))]))
        (result.map (fun pair => scalar (valueNumber pair.2))) := by
  simpa [scalarCircuitWitnessExample] using
    lowerCircuit_complete ctx hash implementation scalarCircuitWitnessExample values result
      inputs json relation admitted exampleAdmission exampleConditions exampleReturns
      lowered decoded profile success
