import Noctium.Verification.ScalarWitnessAliases
import Noctium.Verification.ScalarAllocationOutputFrame

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarWitness ScalarNormalization
open ScalarLowering ScalarInstructionEncoding

/-- A successful circuit validation and execution establish that every listed
constraint is well-typed and evaluates to true. -/
theorem constraints_members (ctx : EvalContext) (circuit : Circuit) (values : EvalEnv)
    (valid : validateConstraints Capabilities.crypto
      (circuit.inputs.map (fun input => (input.name, input.ty))) circuit.span
      circuit.constraints = .ok ())
    (success : runConstraints ctx values circuit.constraints = .ok ()) :
    ∀ condition ∈ circuit.constraints,
      condition.validate Capabilities.crypto
        (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok () ∧
      condition.eval ctx values = .ok true := by
  generalize circuit.constraints = conditions at *
  induction conditions with
  | nil => simp
  | cons condition rest ih =>
    cases checked : condition.validate Capabilities.crypto
        (circuit.inputs.map (fun input => (input.name, input.ty))) with
    | error message => simp [validateConstraints, checked] at valid
    | ok checkedUnit =>
      cases checkedUnit
      simp only [validateConstraints, checked] at valid
      cases evaluated : condition.eval ctx values with
      | error message => simp [runConstraints, evaluated] at success
      | ok value =>
        cases value with
        | false => simp [runConstraints, evaluated] at success
        | true =>
          simp only [runConstraints, evaluated] at success
          intro found member
          rcases List.mem_cons.mp member with same | member
          · subst found
            exact ⟨checked, evaluated⟩
          · exact ih valid success found member

/-- A true source constraint lowers to an asserted ZKIR operand that reads as
one. The proof uses the exact expression lowering and the current input and
alias invariants. -/
theorem completes_condition (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit)
    (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (condition : Expr .bool) (complete : ExprComplete condition)
    (valid : condition.validate Capabilities.crypto
      (circuit.inputs.map (fun input => (input.name, input.ty))) = .ok ())
    (success : condition.eval ctx values = .ok true) :
    Completes hash inputs
      (do
        let text ← Zkir.lowerExpr condition
        Zkir.emit "assert" [("cond", toJson text)]) := by
  intro witness state meaning inputFrame aliases budget
  change ((Zkir.emit "assert"
    [("cond", toJson ((Zkir.lowerExpr condition).run state).1)]).run
      ((Zkir.lowerExpr condition).run state).2).2.next ≤
        Native.maxInstructions * Native.maxVectorLength at budget
  have exprBudget : ((Zkir.lowerExpr condition).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans
      (Zkir.emit_preservesOutputCapacityFrame "assert"
        [("cond", toJson ((Zkir.lowerExpr condition).run state).1)]
        ((Zkir.lowerExpr condition).run state).2).next budget
  let types : TypeEnv := circuit.inputs.map (fun input => (input.name, input.ty))
  obtain ⟨result⟩ := complete ctx hash implementation inputs witness state
    (circuitAliases circuit) values types true valid success
    (admitted.typedEnvironment circuit values inputs hash).aliases
    (current_aliases hash inputs witness circuit values state admitted identifiers
      inputFrame aliases) meaning exprBudget
  have readOne : ∃ operand,
      decodeOperand (toJson result.text) = .ok operand ∧
      operand.read result.finalWitness = one := by
    obtain ⟨operand, parsed, read⟩ := result.operandMeaning
    have valueMeaning : interpret hash inputs result.normalized.term = some one := by
      simpa [sourceScalar?, sourceNumber?, scalar_one] using result.represents.2.2
    exact ⟨operand, parsed, Option.some.inj (read.symm.trans valueMeaning)⟩
  have actualState :
      ((do
        let text ← Zkir.lowerExpr condition
        Zkir.emit "assert" [("cond", toJson text)]).run state).2 =
      ((Zkir.emit "assert" [("cond", toJson result.text)]).run result.finalState).2 := by
    change ((Zkir.emit "assert"
      [("cond", toJson ((Zkir.lowerExpr condition).run state).1)]).run
        ((Zkir.lowerExpr condition).run state).2).2 = _
    rw [result.run]
  refine ⟨{witness := result.finalWitness, meaning := ?_, aliases := ?_, frame := result.frame}⟩
  · rw [actualState]
    exact emit_assert hash result.finalWitness result.finalState result.stateMeaning
      result.text result.textScope readOne
  · rw [actualState]
    exact result.aliasesPreserved

/-- The actual `Zkir.lowerConstraints` loop constructs a witness satisfying
each asserted condition when source validation, source execution, and scalar
expression admission all succeed. -/
theorem completes_circuit_constraints (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (circuit : Circuit)
    (values : EvalEnv) (inputs : NativeRelation.Assignment)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    (scalarAdmission : ScalarCircuitAdmission circuit)
    (complete : ∀ condition ∈ circuit.constraints, ExprComplete condition)
    (valid : validateConstraints Capabilities.crypto
      (circuit.inputs.map (fun input => (input.name, input.ty))) circuit.span
      circuit.constraints = .ok ())
    (success : runConstraints ctx values circuit.constraints = .ok ()) :
    Completes hash inputs (Zkir.lowerConstraints circuit.constraints) := by
  let conditionBody : Expr .bool → StateM Zkir.LowerState Unit := fun condition => do
    let text ← Zkir.lowerExpr condition
    Zkir.emit "assert" [("cond", toJson text)]
  have frames : ∀ condition ∈ circuit.constraints,
      Zkir.PreservesOutputCapacityFrame (conditionBody condition) := by
    intro condition member
    unfold conditionBody
    apply Zkir.bind_preservesOutputCapacityFrame _ _
      (ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
        condition (scalarAdmission.constraints condition member))
    intro text
    exact Zkir.emit_preservesOutputCapacityFrame "assert" [("cond", toJson text)]
  have members := constraints_members ctx circuit values valid success
  have construction : ∀ condition ∈ circuit.constraints,
      Completes hash inputs (conditionBody condition) := by
    intro condition member
    exact completes_condition ctx hash implementation circuit values inputs admitted
      identifiers condition (complete condition member) (members condition member).1
      (members condition member).2
  have loopComplete := completes_forIn hash inputs circuit.constraints PUnit.unit
    conditionBody frames construction
  have loopFrame : Zkir.PreservesOutputCapacityFrame
      (forIn circuit.constraints PUnit.unit
        (fun condition _ => do conditionBody condition; pure (.yield PUnit.unit))) := by
    apply Zkir.forIn_preservesOutputCapacityFrame_of_mem
    intro condition member accumulator
    exact Zkir.bind_preservesOutputCapacityFrame _ _ (frames condition member)
      (fun _ => Zkir.pure_preservesOutputCapacityFrame _)
  have completeAll := completes_bind hash inputs _ _ loopFrame
    (fun _ => Zkir.pure_preservesOutputCapacityFrame _)
    loopComplete (fun _ => completes_pure hash inputs ())
  simpa [conditionBody, Zkir.lowerConstraints, bind_assoc] using completeAll

end Noctium.Verification.ScalarWitnessConstruction
