import Noctium.Verification.ScalarWitnessCircuitInputs

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarWitness ScalarNormalization
open ScalarLowering ScalarInstructionEncoding

private def scalarEntrypointInputRead (input : Input) (raw : Bool) :
    StateM Zkir.LowerState Unit :=
  if raw then pure () else
    Zkir.emit (if input.visibility == .«public» then "public_input" else "private_input")
      [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
        ("output", toJson ("%input_" ++ input.name))]

private def scalarEntrypointInputOperation (input : Input) (raw : Bool) :
    StateM Zkir.LowerState Unit :=
  scalarEntrypointInputRead input raw >>= fun _ =>
    Zkir.constrainType input.ty ("%input_" ++ input.name)

private theorem lowerByteInput_scalar_eq (input : Input) (scalarType : ScalarType input.ty)
    (raw : Bool) :
    Zkir.lowerByteInput input raw = scalarEntrypointInputOperation input raw := by
  cases input with
  | mk name ty visibility span =>
    cases scalarType with
    | native =>
      cases raw <;>
        simp [scalarEntrypointInputOperation, scalarEntrypointInputRead,
          Zkir.lowerByteInput, Zkir.constrainType, Input.nativeIdentifiers]
      all_goals rfl
    | bool =>
      cases raw <;>
        simp [scalarEntrypointInputOperation, scalarEntrypointInputRead,
          Zkir.lowerByteInput, Zkir.constrainType, Input.nativeIdentifiers]
      all_goals rfl
    | uint maximum =>
      cases raw <;>
        simp [scalarEntrypointInputOperation, scalarEntrypointInputRead,
          Zkir.lowerByteInput, Zkir.constrainType, Input.nativeIdentifiers]
      all_goals rfl

private theorem scalarEntrypointInputRead_preservesOutputCapacityFrame
    (input : Input) (raw : Bool) :
    Zkir.PreservesOutputCapacityFrame (scalarEntrypointInputRead input raw) := by
  cases raw with
  | false =>
    simpa [scalarEntrypointInputRead] using
      Zkir.emit_preservesOutputCapacityFrame
        (if input.visibility == .«public» then "public_input" else "private_input")
        [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
          ("output", toJson ("%input_" ++ input.name))]
  | true =>
    simp [scalarEntrypointInputRead, Zkir.pure_preservesOutputCapacityFrame]

private theorem completes_scalar_entrypoint_input (hash : Hash)
    (inputs : NativeRelation.Assignment)
    (input : Input) (raw : Bool) (value : input.ty.Denote)
    (scalarType : ScalarType input.ty)
    (canonical : Canonical input.ty value)
    (binding : inputs ("%input_" ++ input.name) = scalar (number scalarType value))
    (valid : validIdentifier ("%input_" ++ input.name) = true)
    {aliasRequirement : List (String × String) → Prop} :
    Completes hash inputs (Zkir.lowerByteInput input raw) aliasRequirement := by
  have readComplete : Completes hash inputs (scalarEntrypointInputRead input raw)
      aliasRequirement := by
    cases raw with
    | false =>
      simpa [scalarEntrypointInputRead] using
        (completes_emit_input hash inputs input valid :
          Completes hash inputs
            (Zkir.emit (if input.visibility == .«public» then "public_input" else "private_input")
              [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
                ("output", toJson ("%input_" ++ input.name))]) aliasRequirement)
    | true =>
      simpa [scalarEntrypointInputRead] using
        (completes_pure hash inputs () : Completes hash inputs (pure ()) aliasRequirement)
  have readFrame : Zkir.PreservesOutputCapacityFrame (scalarEntrypointInputRead input raw) :=
    scalarEntrypointInputRead_preservesOutputCapacityFrame input raw
  have typeComplete : Completes hash inputs
      (Zkir.constrainType input.ty ("%input_" ++ input.name)) aliasRequirement :=
    completes_scalar_constraint hash inputs input.name value scalarType canonical binding valid
  have semantic : Completes hash inputs (scalarEntrypointInputOperation input raw)
      aliasRequirement := by
    unfold scalarEntrypointInputOperation
    exact completes_bind hash inputs (scalarEntrypointInputRead input raw)
      (fun _ => Zkir.constrainType input.ty ("%input_" ++ input.name)) readFrame
      (fun _ => Zkir.constrainType_preservesOutputCapacityFrame _ _) readComplete
      (fun _ => typeComplete)
  rw [lowerByteInput_scalar_eq input scalarType raw]
  exact semantic

/-- Every admitted scalar entrypoint input lowers to a satisfying witness
prefix. The call header supplies the raw scalar inputs, which retain their
source type constraints in the body. -/
theorem completes_entrypoint_inputs (hash : Hash)
    (inputs : NativeRelation.Assignment) (entry : Entrypoint) (values : EvalEnv)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (identifiers : ∀ input ∈ entry.circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true)
    {aliasRequirement : List (String × String) → Prop} :
    Completes hash inputs (Zkir.lowerEntrypointInputs entry) aliasRequirement := by
  let body : Input → StateM Zkir.LowerState Unit := fun input =>
    Zkir.lowerByteInput input (entry.callInputs.contains input.name)
  have frames : ∀ input ∈ entry.circuit.inputs,
      Zkir.PreservesOutputCapacityFrame
        (body input) := by
    intro input member
    exact Zkir.lowerByteInput_preservesOutputCapacityFrame input
      (entry.callInputs.contains input.name)
  have construction : ∀ input ∈ entry.circuit.inputs,
      Completes hash inputs (body input) aliasRequirement := by
    intro input member
    obtain ⟨value, lookup, canonical⟩ := admitted.complete input member
    let scalarType := scalarTypeOfCanonicalInput canonical
    have binding : inputs ("%input_" ++ input.name) = scalar (number scalarType value) :=
      admitted.binding input member value lookup canonical
    simpa only [body] using
      completes_scalar_entrypoint_input hash inputs input
        (entry.callInputs.contains input.name) value scalarType canonical binding
        (identifiers input member)
  unfold Zkir.lowerEntrypointInputs
  apply completes_forIn hash inputs entry.circuit.inputs () body frames construction

end Noctium.Verification.ScalarWitnessConstruction
