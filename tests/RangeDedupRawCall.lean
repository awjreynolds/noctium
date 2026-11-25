import Noctium.Compiler
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarValidationOpcodeProfile

open Lean Noctium Noctium.Backend Noctium.Verification
open NativeRelationJson ScalarValidationOpcodeProfile
open scoped Noctium

noctium_circuit rangeDedupRawCall where
  private amount : Native
  output first : UIntRange 200 := disclose(cast(UIntRange 200, amount))
  output second : UIntRange 200 := disclose(cast(UIntRange 200, amount))
end

noctium_contract RangeDedupRawCall where
  entry convert uses rangeDedupRawCall arguments [amount] where
    return firstResult : UIntRange 200 := first
    return secondResult : UIntRange 200 := second
  end
end

private def convertEntry : Entrypoint :=
  match RangeDedupRawCall.entrypoints.find? (·.name == "convert") with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

private def decodeCallArtifact (rewrites : Zkir.Rewrites) :
    Except String
      (Json × ScalarCall × List Json × List Noctium.Verification.NativeRelation.Instruction) := do
  let artifact ← (Zkir.lowerEntrypoint RangeDedupRawCall.state convertEntry rewrites)
    |>.mapError (·.message)
  let call ← decodeScalarCall artifact
  let rows ← arrayField artifact "instructions"
  let instructions ← rows.toList.mapM decodeInstruction
  ensure
    (checkedScalarOpcodeProfile rows.toList.zipIdx instructions)
    "emitted native call does not pass the checked scalar opcode profile"
  ensure (instructions == call.body.instructions)
    "decoded call body differs from its emitted instruction rows"
  pure (artifact, call, rows.toList, instructions)
where
  ensure (condition : _root_.Bool) (message : String) : Except String Unit :=
    if condition then .ok () else .error message

private def rawCallRewriteChecks : Except String _root_.Bool := do
  let (_, rangeCall, rangeRows, rangeInstructions) ←
    decodeCallArtifact .rangeAndAssertions
  let (_, comparisonCall, comparisonRows, comparisonInstructions) ←
    decodeCallArtifact .includingComparisons
  let expectedArguments := ["%input_amount"]
  let isCopy := fun row =>
    match stringField row "op" with
    | .ok opcode => opcode == "copy"
    | .error _ => _root_.Bool.false
  let comparisonCopyCount := comparisonRows.countP isCopy
  let rangeCopyCount := rangeRows.countP isCopy
  ensure (rangeCall.arguments == expectedArguments)
    "range-only call header lost its declared raw caller argument"
  ensure (comparisonCall.arguments == expectedArguments)
    "comparison rewrite changed the declared raw caller argument"
  ensure (rangeCall.arguments == comparisonCall.arguments)
    "rewrite modes emitted different ordered caller arguments"
  ensure (decide (comparisonCopyCount > rangeCopyCount))
    "comparison rewrite did not replace a repeated range check with Copy"
  ensure (rangeInstructions != comparisonInstructions)
    "comparison rewrite left the accepted call body unchanged"
  pure _root_.Bool.true

#guard rawCallRewriteChecks.toOption == some _root_.Bool.true
