import Noctium.Verification.ScalarWitnessAssembly
import Noctium.Verification.ScalarRangeLowering

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarWitness ScalarNormalization
open ScalarLowering ScalarInstructionEncoding

private def scalarTypeOfCanonicalInput {ty : Ty} {value : ty.Denote}
    (canonical : Canonical ty value) : ScalarType ty := by
  cases ty with
  | native => exact .native
  | bool => exact .bool
  | uint maximum => exact .uint maximum
  | bytes _ => simp [Canonical, sourceNumber?] at canonical
  | opaqueBytes => simp [Canonical, sourceNumber?] at canonical
  | opaqueString => simp [Canonical, sourceNumber?] at canonical
  | jubjubScalar => simp [Canonical, sourceNumber?] at canonical
  | jubjubPoint => simp [Canonical, sourceNumber?] at canonical
  | foreign kind => simp [Canonical, sourceNumber?] at canonical

private theorem fresh_binary_scope (next : Nat) (left right : Operand)
    (leftScope : ∀ name ∈ operandIdentifiers left, InScope next name)
    (rightScope : ∀ name ∈ operandIdentifiers right, InScope next name) :
    ∀ name ∈ operandIdentifiers left ++ operandIdentifiers right ++ [freshName next],
      InScope (next + 1) name := by
  intro name member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (member | member) | rfl
  · exact InScope.mono (by omega) (leftScope name member)
  · exact InScope.mono (by omega) (rightScope name member)
  · exact Or.inr ⟨next, by omega, rfl⟩

private theorem state_from_suffix (hash : Hash)
    (witness afterWitness : NativeRelation.Assignment)
    (before after : Zkir.LowerState) (prior suffix : List Instruction)
    (meaning : LowerStateMeaning hash witness before)
    (priorDecoded : before.instructions.toList.mapM decodeInstruction = .ok prior)
    (afterDecoded : after.instructions.toList.mapM decodeInstruction = .ok (prior ++ suffix))
    (holds : ∀ instructions, after.instructions.toList.mapM decodeInstruction = .ok instructions →
      ∀ instruction ∈ instructions, instruction.Holds hash afterWitness)
    (next : before.next ≤ after.next) (aliasesSame : after.aliases = before.aliases)
    (cacheSame : after.expressions = before.expressions)
    (scope : ∀ instruction ∈ suffix, ∀ name ∈ instructionIdentifiers instruction,
      InScope after.next name) :
    LowerStateMeaning hash afterWitness after := by
  constructor
  · exact ⟨prior ++ suffix, afterDecoded⟩
  · exact holds
  · intro instructions checked instruction member name nameMember
    have equal : instructions = prior ++ suffix := Except.ok.inj (checked.symm.trans afterDecoded)
    subst instructions
    rcases List.mem_append.mp member with old | new
    · exact InScope.mono next (meaning.scope prior priorDecoded instruction old name nameMember)
    · exact scope instruction new name nameMember
  · intro name text member
    rw [aliasesSame] at member
    exact TextScope.mono next (meaning.aliases name text member)
  · intro key output member
    rw [cacheSame] at member
    obtain ⟨old, oldDecoded, instruction, instructionMember, correspondence⟩ :=
      meaning.cacheTrace key output member
    have equal : old = prior := Except.ok.inj (oldDecoded.symm.trans priorDecoded)
    subst old
    exact ⟨prior ++ suffix, afterDecoded, instruction,
      List.mem_append_left _ instructionMember, correspondence⟩

private theorem completes_constrain_unsigned (hash : Hash)
    (inputs : NativeRelation.Assignment) (maximum : Nat) (name : String) (value : Nat)
    (canonical : value < Field.modulus ∧ maximum ≤ ScalarPolicy.maxUint ∧ value ≤ maximum)
    (binding : inputs ("%input_" ++ name) = scalar value)
    (valid : validIdentifier ("%input_" ++ name) = true) :
    Completes hash inputs (Zkir.constrainUnsigned maximum ("%input_" ++ name)) := by
  intro witness state meaning inputFrame aliases budget
  let text := "%input_" ++ name
  let operand : Operand := .reference text
  have operandDecoded : decodeOperand (toJson text) = .ok operand :=
    (OperandEncoding.reference text valid).decode
  have operandMeaning : OperandMeaning hash inputs witness text (.input text) := by
    refine ⟨operand, operandDecoded, ?_⟩
    simp only [Operand.read, interpret_input]
    rw [← inputFrame name]
  have textScope : TextScope state.next text := by
    exact ⟨operand, operandDecoded, by
      intro identifier member
      change identifier ∈ [text] at member
      have equal := List.mem_singleton.mp member
      subst identifier
      exact Or.inl ⟨name, rfl⟩⟩
  obtain ⟨prior, priorDecoded⟩ := meaning.decoded
  obtain ⟨scopedOperand, scopedDecoded, names⟩ := textScope
  have sameOperand : scopedOperand = operand := Except.ok.inj (scopedDecoded.symm.trans operandDecoded)
  subst scopedOperand
  have next := (Zkir.constrainUnsigned_preservesOutputCapacityFrame maximum text state).next
  have startBudget : state.next ≤ Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans next budget
  have independent : OperandIndependent s!"%v{state.next}" operand :=
    Operand.independent_of_scope state.next operand names
  have priorIndependent : ∀ instruction ∈ prior,
      InstructionIndependent s!"%v{state.next}" instruction := by
    intro instruction member
    exact Instruction.independent_of_scope state.next instruction
      (meaning.scope prior priorDecoded instruction member)
  have range : (operand.read witness).val ≤ maximum := by
    change (witness text).val ≤ maximum
    rw [inputFrame name, binding]
    change value % Field.modulus ≤ maximum
    rw [Nat.mod_eq_of_lt canonical.1]
    exact canonical.2.2
  obtain ⟨afterWitness, instructions, decoded, nativeHolds, stable, frame, extension⟩ :=
    ScalarRangeLowering.constrainUnsigned_complete hash witness state maximum text operand prior
      operandDecoded priorDecoded (meaning.holds prior priorDecoded) range canonical.2.1
      startBudget independent priorIndependent
  let after := ((Zkir.constrainUnsigned maximum text).run state).2
  have frameOld : ∀ name, InScope state.next name → afterWitness name = witness name := by
    intro name inScope
    apply frame
    intro equal
    rw [equal] at inScope
    exact fresh_not_inScope state.next inScope
  have allHolds : ∀ found, after.instructions.toList.mapM decodeInstruction = .ok found →
      ∀ instruction ∈ found, instruction.Holds hash afterWitness := by
    intro found checked instruction member
    have equal : found = instructions := Except.ok.inj (checked.symm.trans decoded)
    subst found
    exact nativeHolds instruction member
  have aliasesSame : after.aliases = state.aliases := by
    change ((Zkir.constrainUnsigned maximum text).run state).2.aliases = state.aliases
    by_cases isZero : maximum = 0
    · subst maximum
      rw [ScalarRangeLowering.zero_run]
    · by_cases power : maximum + 1 = 2 ^ (maximum.log2 + 1)
      · rw [ScalarRangeLowering.power_run state maximum text isZero power]
      · rw [ScalarRangeLowering.nonpower_run state maximum text isZero power]
  have cacheSame : after.expressions = state.expressions := by
    change ((Zkir.constrainUnsigned maximum text).run state).2.expressions = state.expressions
    by_cases isZero : maximum = 0
    · subst maximum
      rw [ScalarRangeLowering.zero_run]
    · by_cases power : maximum + 1 = 2 ^ (maximum.log2 + 1)
      · rw [ScalarRangeLowering.power_run state maximum text isZero power]
      · rw [ScalarRangeLowering.nonpower_run state maximum text isZero power]
  have finalMeaning : LowerStateMeaning hash afterWitness after := by
    by_cases isZero : maximum = 0
    · subst maximum
      apply state_from_suffix hash witness afterWitness state after prior
        [.equal operand (.immediate zero)] meaning priorDecoded
        (ScalarRangeLowering.zero_decode state text operand prior operandDecoded priorDecoded)
        allHolds next aliasesSame cacheSame
      intro instruction member name nameMember
      have equal := List.mem_singleton.mp member
      subst instruction
      have oldName : name ∈ operandIdentifiers operand := by
        simpa only [instructionIdentifiers, operandIdentifiers, List.append_nil] using nameMember
      exact InScope.mono next (names name oldName)
    · by_cases power : maximum + 1 = 2 ^ (maximum.log2 + 1)
      · apply state_from_suffix hash witness afterWitness state after prior
          [.bits operand (maximum.log2 + 1)] meaning priorDecoded
          (ScalarRangeLowering.power_decode state maximum text operand prior isZero power
            canonical.2.1 operandDecoded priorDecoded)
          allHolds next aliasesSame cacheSame
        intro instruction member name nameMember
        have equal := List.mem_singleton.mp member
        subst instruction
        exact InScope.mono next (names name nameMember)
      · apply state_from_suffix hash witness afterWitness state after prior
          [.bits operand (maximum.log2 + 1),
            .lessThan operand (.immediate (scalar (maximum + 1))) (maximum.log2 + 1)
              s!"%v{state.next}", .assert (.reference s!"%v{state.next}")]
          meaning priorDecoded
          (ScalarRangeLowering.nonpower_decode state maximum text operand prior isZero power
            canonical.2.1 startBudget operandDecoded priorDecoded)
          allHolds next aliasesSame cacheSame
        have nextEq : after.next = state.next + 1 := by
          change ((Zkir.constrainUnsigned maximum text).run state).2.next = state.next + 1
          rw [ScalarRangeLowering.nonpower_run state maximum text isZero power]
        intro instruction member name nameMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact InScope.mono next (names name nameMember)
        · rw [nextEq]
          exact fresh_binary_scope state.next operand (.immediate (scalar (maximum + 1)))
            names (by intro identifier absent; simp [operandIdentifiers] at absent) name nameMember
        · have equal : name = s!"%v{state.next}" := by
            simpa only [instructionIdentifiers, operandIdentifiers, List.mem_singleton] using nameMember
          subst name
          rw [nextEq]
          exact Or.inr ⟨state.next, by omega, rfl⟩
  refine ⟨{witness := afterWitness, meaning := finalMeaning, aliases := aliasesSame, frame := ?_}⟩
  intro name inScope
  exact frameOld name inScope

private theorem completes_scalar_constraint (hash : Hash)
    (inputs : NativeRelation.Assignment) (name : String) (value : ty.Denote)
    (scalarType : ScalarType ty)
    (canonical : Canonical ty value)
    (binding : inputs ("%input_" ++ name) = scalar (number scalarType value))
    (valid : validIdentifier ("%input_" ++ name) = true) :
    Completes hash inputs (Zkir.constrainType ty ("%input_" ++ name)) := by
  let text := "%input_" ++ name
  cases scalarType with
  | native => exact completes_pure hash inputs ()
  | bool =>
    intro witness state meaning inputFrame aliases budget
    let operand : Operand := .reference text
    have operandDecoded : decodeOperand (toJson text) = .ok operand :=
      (OperandEncoding.reference text valid).decode
    have boolean : operand.read witness = zero ∨ operand.read witness = one := by
      change witness text = zero ∨ witness text = one
      rw [inputFrame name, binding]
      cases value <;> simp [number, scalar_zero, scalar_one]
    have newMeaning : LowerStateMeaning hash witness
        ((Zkir.constrainType .bool text).run state).2 := by
      change LowerStateMeaning hash witness {state with instructions := state.instructions.push _}
      exact LowerStateMeaning.append hash witness state meaning _ _
        (ScalarInstructionEncoding.decode_boolean_instruction operandDecoded) boolean
        (by
          intro identifier member
          have equal : identifier = text := by
            change identifier ∈ [text] at member
            exact List.mem_singleton.mp member
          subst identifier
          exact Or.inl ⟨name, rfl⟩)
    exact ⟨PrefixExtension.mk witness newMeaning rfl (by intro identifier _; rfl)⟩
  | uint maximum =>
    have canonicalParts : value < Field.modulus ∧
        maximum ≤ ScalarPolicy.maxUint ∧ value ≤ maximum := by
      simpa [Canonical, sourceNumber?] using canonical
    have bounded : Completes hash inputs (Zkir.constrainUnsigned maximum text) :=
      completes_constrain_unsigned hash inputs maximum name value canonicalParts
        (by simpa only [number] using binding) valid
    simpa only [Zkir.constrainType] using bounded

private def scalarInputOperation (input : Input) : StateM Zkir.LowerState Unit := do
  let output := "%input_" ++ input.name
  Zkir.emit (if input.visibility == .«public» then "public_input" else "private_input")
    [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)), ("output", toJson output)]
  Zkir.constrainType input.ty output
  if input.visibility == .«public» then Zkir.bindPublic [output]

private theorem lowerCircuitInput_scalar_eq (input : Input) (scalarType : ScalarType input.ty) :
    Zkir.lowerCircuitInput input = scalarInputOperation input := by
  cases input with
  | mk name ty visibility span =>
    cases scalarType with
    | native =>
      cases visibility <;>
        simp [scalarInputOperation, Zkir.lowerCircuitInput, Zkir.lowerByteInput,
          Zkir.constrainType, Input.nativeIdentifiers, Zkir.bindPublic]
      all_goals rfl
    | bool =>
      cases visibility <;>
        simp [scalarInputOperation, Zkir.lowerCircuitInput, Zkir.lowerByteInput,
          Zkir.constrainType, Input.nativeIdentifiers, Zkir.bindPublic]
      all_goals rfl
    | uint maximum =>
      cases visibility <;>
        simp [scalarInputOperation, Zkir.lowerCircuitInput, Zkir.lowerByteInput,
          Zkir.constrainType, Input.nativeIdentifiers, Zkir.bindPublic]
      all_goals rfl

private theorem completes_scalar_input (hash : Hash)
    (inputs : NativeRelation.Assignment)
    (input : Input) (value : input.ty.Denote) (scalarType : ScalarType input.ty)
    (canonical : Canonical input.ty value)
    (binding : inputs ("%input_" ++ input.name) = scalar (number scalarType value))
    (valid : validIdentifier ("%input_" ++ input.name) = true) :
    Completes hash inputs (Zkir.lowerCircuitInput input) := by
  have inputComplete := completes_emit_input hash inputs input valid
  have typeComplete : Completes hash inputs
      (Zkir.constrainType input.ty ("%input_" ++ input.name)) :=
    completes_scalar_constraint hash inputs input.name value scalarType
      canonical binding valid
  have publicComplete : Completes hash inputs
      (if input.visibility == .«public» then
        Zkir.bindPublic ["%input_" ++ input.name] else pure ()) := by
    by_cases isPublic : input.visibility == .«public»
    · have visibleComplete : Completes hash inputs (Zkir.bindPublic ["%input_" ++ input.name]) := by
        intro witness state meaning inputFrame aliases budget
        have parsed : decodeOperand (toJson ("%input_" ++ input.name)) =
            .ok (.reference ("%input_" ++ input.name)) :=
          (OperandEncoding.reference _ valid).decode
        have scope : TextScope state.next ("%input_" ++ input.name) := by
          refine ⟨.reference _, parsed, ?_⟩
          intro name member
          simp only [operandIdentifiers, List.mem_singleton] at member
          subst name
          exact Or.inl ⟨input.name, rfl⟩
        have meaning' := emit_impact hash witness state meaning
          ["%input_" ++ input.name] (by
            intro text member
            have equal : text = "%input_" ++ input.name := List.mem_singleton.mp member
            subst text
            exact scope)
        exact ⟨PrefixExtension.mk witness meaning' rfl (by intro name _; rfl)⟩
      simpa [isPublic] using visibleComplete
    · simpa [isPublic] using (completes_pure hash inputs ())
  have semantic : Completes hash inputs (scalarInputOperation input) := by
    unfold scalarInputOperation
    apply completes_bind hash inputs _ _
      (Zkir.emit_preservesOutputCapacityFrame _ _)
    · intro _
      exact Zkir.bind_preservesOutputCapacityFrame _ _
        (Zkir.constrainType_preservesOutputCapacityFrame _ _)
        (fun _ => by
          split
          · simpa only [Zkir.bindPublic] using
              Zkir.emit_preservesOutputCapacityFrame "impact"
                [("guard", toJson ("0x01" : String)), ("inputs", toJson ["%input_" ++ input.name])]
          · exact Zkir.pure_preservesOutputCapacityFrame ())
    · exact inputComplete
    · intro _
      apply completes_bind hash inputs _ _
        (Zkir.constrainType_preservesOutputCapacityFrame _ _)
      · intro _
        split
        · simpa only [Zkir.bindPublic] using
            Zkir.emit_preservesOutputCapacityFrame "impact"
              [("guard", toJson ("0x01" : String)), ("inputs", toJson ["%input_" ++ input.name])]
        · exact Zkir.pure_preservesOutputCapacityFrame ()
      · exact typeComplete
      · intro _
        exact publicComplete
  rw [lowerCircuitInput_scalar_eq input scalarType]
  exact semantic

/-- Every admitted scalar circuit input lowers to a satisfying witness prefix.
UInt bounds use the current unsigned ZKIR lowering, including its fresh
comparison witness when the bound is not a power of two. -/
theorem completes_circuit_inputs (hash : Hash) (inputs : NativeRelation.Assignment)
    (circuit : Circuit) (values : EvalEnv)
    (admitted : CanonicalInputs circuit values inputs)
    (identifiers : ∀ input ∈ circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true) :
    Completes hash inputs (Zkir.lowerCircuitInputs circuit.inputs) := by
  let body : Input → StateM Zkir.LowerState Unit := Zkir.lowerCircuitInput
  have frames : ∀ input ∈ circuit.inputs, Zkir.PreservesOutputCapacityFrame (body input) := by
    intro input _
    exact Zkir.lowerCircuitInput_preservesOutputCapacityFrame input
  have construction : ∀ input ∈ circuit.inputs, Completes hash inputs (body input) := by
    intro input member
    obtain ⟨value, lookup, canonical⟩ := admitted.complete input member
    let scalarType := scalarTypeOfCanonicalInput canonical
    have binding : inputs ("%input_" ++ input.name) = scalar (number scalarType value) :=
      admitted.binding input member value lookup canonical
    simpa only [body] using
      completes_scalar_input hash inputs input value scalarType canonical binding
        (identifiers input member)
  let loop : StateM Zkir.LowerState Unit :=
    forIn circuit.inputs () (fun input _ => do
      body input
      pure (.yield ()))
  have loopComplete : Completes hash inputs loop := by
    simpa only [loop] using completes_forIn hash inputs circuit.inputs () body frames construction
  have loopFrame : Zkir.PreservesOutputCapacityFrame loop := by
    apply Zkir.forIn_preservesOutputCapacityFrame_of_mem
    intro input member accumulator
    exact Zkir.bind_preservesOutputCapacityFrame _ _ (frames input member)
      (fun _ => Zkir.pure_preservesOutputCapacityFrame _)
  have fullComplete : Completes hash inputs (loop >>= fun _ => pure ()) :=
    completes_bind hash inputs loop (fun _ => pure ()) loopFrame
      (fun _ => Zkir.pure_preservesOutputCapacityFrame ()) loopComplete
      (fun _ => completes_pure hash inputs ())
  simpa only [Zkir.lowerCircuitInputs, body, loop, bind_assoc, pure_bind] using fullComplete

end Noctium.Verification.ScalarWitnessConstruction
