import Noctium.Verification.GenericStateOutputCompleteness

namespace Noctium.Verification.GenericStateOutputCompletenessFixture

open Noctium Noctium.Backend.Native Noctium.Verification.NativeRelation
  Noctium.Verification.ScalarNormalization Noctium.Verification.GenericStateCircuitParts
  Noctium.Verification.GenericStateOutputCompleteness

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .ok 0
}

private def hash : Hash := fun _ => zero
private def inputs : Assignment := fun _ => zero
private def values : EvalEnv := []

private theorem hashAgreement : HashAgreement context hash := by
  constructor
  · rfl
  · intro domain left right
    rfl

private def boundedSum : Output := {
  name := "sum"
  ty := .uint 6
  value := .uadd (.uint 3 2) (.uint 3 1)
}

private def scalarOutput : Output := {
  name := "raw"
  ty := .native
  value := .native 7
}

private def outputs : List Output := [boundedSum, scalarOutput]

private def normalizedSum : Term := .binary "add" (.constant 2) (.constant 1)

private def expectedFrame : OutputFrame :=
  ([ ("raw", .constant 7), ("sum", normalizedSum) ],
    [ (.constant 2, 3), (.constant 1, 3), (normalizedSum, 6) ], [])

private def sourceResults : List (String × Value) :=
  [("sum", .uint 6 3), ("raw", .native 7)]

private theorem outputs_admitted :
    ∀ output ∈ outputs, ScalarExpression output.value := by
  intro output member
  simp only [outputs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with first | second
  · subst output
    exact ScalarExpression.uadd (.uint 3 2) (.uint 3 1)
      (ScalarExpression.uint 3 2) (ScalarExpression.uint 3 1)
  · subst output
    change ScalarExpression (.native 7)
    exact ScalarExpression.native 7

private theorem initialAgreement : AliasAgreement hash inputs [] values := by
  intro name ty raw value found typed
  change (none : Option Value) = some raw at found
  cases found

private theorem outputs_unused : ∀ output ∈ outputs, values.lookup output.name = none := by
  intro output member
  simp [values]

private theorem sourceAccepted : outputs.mapM (evalOutput context values) = .ok sourceResults := by
  with_unfolding_all rfl

private theorem foldAccepted : normalizeOutputs [] outputs = .ok expectedFrame := by
  with_unfolding_all rfl

theorem successful_source_and_normalizer_paths_are_complete :
    outputs.mapM (evalOutput context values) = .ok sourceResults ∧
    normalizeOutputs [] outputs = .ok expectedFrame ∧
    (∀ requirement ∈ expectedFrame.2.1,
      ∃ value, interpret hash inputs requirement.1 = some value ∧
        value.val ≤ requirement.2) ∧
    (∀ term ∈ expectedFrame.2.2, interpret hash inputs term = some one) ∧
    AliasAgreement hash inputs expectedFrame.1 values ∧
    AliasAgreement hash inputs expectedFrame.1 (sourceResults.reverse ++ values) := by
  have complete := normalizeOutputs_complete context hash hashAgreement inputs [] values
    outputs outputs_admitted expectedFrame sourceResults initialAgreement outputs_unused
    sourceAccepted foldAccepted
  exact ⟨sourceAccepted, foldAccepted, complete.1, complete.2.1,
    complete.2.2.1, complete.2.2.2⟩

theorem normalized_alias_order_matches_reversed_source_order :
    expectedFrame.1.map Prod.fst = sourceResults.reverse.map Prod.fst := by
  rfl

private def bytesOutput : Output := {
  name := "bytes"
  ty := .bytes 1
  value := .bytesLiteral 1 [9]
}

theorem bytes_source_stays_outside_scalar_interpretation :
    evalOutput context values bytesOutput = .ok ("bytes", .bytes 1 [9]) ∧
    normalizeOutputs [] [bytesOutput] =
      .ok ([ ("bytes", .bytes [.constant 9]) ], [], []) ∧
    interpret hash inputs (.bytes [.constant 9]) = none ∧
    ¬ ScalarExpression bytesOutput.value := by
  constructor
  · with_unfolding_all rfl
  · constructor
    · with_unfolding_all rfl
    · constructor
      · change ScalarTermMeaning.interpret? hash inputs
          (.bytes [.constant 9]) = none
        simp
      · intro admitted
        cases admitted

end Noctium.Verification.GenericStateOutputCompletenessFixture
