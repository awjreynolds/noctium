import Noctium.Verification.NativeTypedBoolRelation
import Noctium.Verification.ScalarValidationTypedBool

namespace Noctium.Verification.ScalarValidationTypedBoolCircuit

open Backend.Native Noctium.Verification.NativeRelation
open Noctium.Verification.NativeTypedBoolRelation
open Noctium.Verification.ScalarValidationTypedBool

/-- Compose the existing accepted NativeProducer handoff with satisfaction of
the decoded ZKIR Bool slice. The producer premise is the result of
`accepted_bool_and_encode_meaning`; source parsing is not repeated here. -/
theorem accepted_producer_and_decoded_bool_satisfaction
    {witness : Assignment} {json : Lean.Json}
    {slice : AndOutput} (leftValue rightValue : Bool)
    (producer : ∃ output : String, ∃ fact : Fact,
      output = slice.outputName ∧
      interpretTypedBoolNative? fact.term = some (bit (leftValue && rightValue)))
    (decoded : DecodedRootSatisfies json slice witness)
    (leftValueMatches : slice.leftValue = leftValue)
    (rightValueMatches : slice.rightValue = rightValue) :
    ∃ output : String, ∃ fact : Fact,
      output = slice.outputName ∧
      interpretTypedBoolNative? fact.term = some (bit (leftValue && rightValue)) ∧
      witness output = bit (leftValue && rightValue) := by
  obtain ⟨output, fact, outputSame, producerMeaning⟩ := producer
  have outputMeaning := root_output_of_satisfies json witness slice decoded
  rw [leftValueMatches, rightValueMatches] at outputMeaning
  rw [← outputSame] at outputMeaning
  exact ⟨output, fact, outputSame, producerMeaning, outputMeaning⟩

end Noctium.Verification.ScalarValidationTypedBoolCircuit
