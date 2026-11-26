import Noctium.Verification.ScalarValidation

namespace ScalarValidationTests

open Lean Noctium Noctium.Backend.Native
open Noctium.Verification NativeRelation ScalarNormalization ScalarValidation

private def accepted (result : Except String α) : Bool :=
  match result with | .ok _ => true | .error _ => false

private theorem observedGroups {groups expected : List (List Scalar)}
    (observed : groups.map (List.map some) = expected.map (List.map some)) : groups = expected := by
  have recovered := congrArg (List.map (List.filterMap id)) observed
  simpa only [List.map_map, Function.comp_def, List.filterMap_map, id, List.filterMap_some,
    List.map_id'] using recovered

private def flagExpected : Expected := {
  mode := .relation
  inputs := [{identifier := "%flag", visibility := .private, ty := .bool}]
  groups := [[.input "%flag"]]
  returns := [.input "%flag"]
  assertions := [.input "%flag"]
  bounds := []
}

private def flagRelation : Program := {
  instructions := [.input .private "%flag", .boolean (.reference "%flag"),
    .assert (.reference "%flag"), .impact (.immediate one) [.reference "%flag"],
    .output [.reference "%flag"]]
  outputArity := 1
  communicationsCommitment := false
}

private def flagJson : Json := NativeRelationJson.encode flagRelation

#guard accepted (validate flagExpected flagJson)
#guard accepted (NativeRelationJson.decode flagJson)
#guard !accepted (validate flagExpected (NativeRelationJson.encode
  {flagRelation with instructions := [.input .private "%flag", .assert (.reference "%flag"),
    .impact (.immediate one) [.reference "%flag"], .output [.reference "%flag"]]}))
#guard !accepted (validate flagExpected (NativeRelationJson.encode
  {flagRelation with instructions := [.input .private "%flag", .boolean (.reference "%flag"),
    .assert (.reference "%flag"), .output [.reference "%flag"]]}))

/-- A private Boolean input obtains its range from the native constraint.
Native Assert alone contributes only nonzero, so the producer's range gate matters. -/
example (hash : Hash) (inputs witness : Assignment) (streams : InputStreams)
    (groups : List (List Scalar)) (returns : List Scalar)
    (agreement : InputAgreement flagExpected inputs witness)
    (checked : validate flagExpected flagJson = .ok ())
    (decoded : NativeRelationJson.decode flagJson = .ok flagRelation)
    (satisfies : Satisfies hash flagRelation streams witness groups returns) :
    inputs "%flag" = one ∧ groups = [[inputs "%flag"]] ∧ returns = [inputs "%flag"] := by
  obtain ⟨sound, returned⟩ := validate_observed_returns agreement checked decoded satisfies
  have assertion := sound.assertions (.input "%flag") (by simp [flagExpected])
  have returnedValues := congrArg (List.filterMap id) returned
  have flagValue : inputs "%flag" = one :=
    Option.some.inj (by simpa only [ScalarTermMeaning.interpret_input] using assertion)
  exact ⟨flagValue, observedGroups (by simpa [flagExpected, interpret] using sound.impact),
    by simpa [flagExpected, interpret, List.filterMap_map, Function.comp_def] using returnedValues⟩

private def rangeExpected : Expected := {
  mode := .relation
  inputs := [{identifier := "%value", visibility := .private, ty := .uint 200}]
  groups := [[.input "%value"]]
  returns := [.input "%value"]
  assertions := []
  bounds := [(.input "%value", 200)]
}

private def rangeRelation : Program := {
  instructions := [.input .private "%value", .bits (.reference "%value") 8,
    .lessThan (.reference "%value") (.immediate (scalar 201)) 8 "%bounded",
    .assert (.reference "%bounded"), .impact (.immediate one) [.reference "%value"],
    .output [.reference "%value"]]
  outputArity := 1
  communicationsCommitment := false
}

private def rangeJson : Json := NativeRelationJson.encode rangeRelation

#guard accepted (validate rangeExpected rangeJson)
#guard accepted (NativeRelationJson.decode rangeJson)
#guard !accepted (validate rangeExpected (NativeRelationJson.encode
  {rangeRelation with instructions := [.input .private "%value",
    .lessThan (.reference "%value") (.immediate (scalar 201)) 8 "%bounded",
    .assert (.reference "%bounded"), .impact (.immediate one) [.reference "%value"],
    .output [.reference "%value"]]}))
#guard !accepted (validate rangeExpected (NativeRelationJson.encode
  {rangeRelation with instructions := [.input .private "%value", .bits (.reference "%value") 8,
    .lessThan (.reference "%value") (.immediate (scalar 202)) 8 "%bounded",
    .assert (.reference "%bounded"), .impact (.immediate one) [.reference "%value"],
    .output [.reference "%value"]]}))

/-- The LessThan native model is conditional. The actual producer fold proves
both operand ranges before using its output to establish this tighter bound. -/
example (hash : Hash) (inputs witness : Assignment) (streams : InputStreams)
    (groups : List (List Scalar))
    (agreement : InputAgreement rangeExpected inputs witness)
    (checked : validate rangeExpected rangeJson = .ok ())
    (decoded : NativeRelationJson.decode rangeJson = .ok rangeRelation)
    (satisfies : CircuitSatisfies hash rangeRelation streams witness groups) :
    (inputs "%value").val ≤ 200 ∧ groups = [[inputs "%value"]] := by
  have sound := validate_sound agreement checked decoded satisfies
  obtain ⟨value, valueMeaning, bound⟩ :=
    sound.bounds (.input "%value", 200) (by simp [rangeExpected])
  have exactValue : inputs "%value" = value :=
    Option.some.inj (by simpa only [ScalarTermMeaning.interpret_input] using valueMeaning)
  exact ⟨exactValue.symm ▸ bound,
    observedGroups (by simpa [rangeExpected, interpret] using sound.impact)⟩

#print axioms Noctium.Verification.ScalarValidation.validate_sound
#print axioms Noctium.Verification.ScalarValidation.validate_observed_returns

end ScalarValidationTests
