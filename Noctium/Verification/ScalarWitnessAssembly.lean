import Noctium.Verification.ScalarStateExtensions
import Noctium.Verification.ScalarInstructionEncoding
import Noctium.Verification.ScalarCircuit

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarWitness ScalarNormalization
open ScalarLowering ScalarInstructionEncoding

/-- A declared input is a scoped field, while its declared source type is
constrained by the following actual constrainType computation. -/
theorem emit_input (hash : Hash) (witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (meaning : LowerStateMeaning hash witness state)
    (input : Input) (valid : validIdentifier ("%input_" ++ input.name) = true) :
    LowerStateMeaning hash witness
      ((Zkir.emit (if input.visibility == .«public» then "public_input" else "private_input")
        [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
          ("output", toJson ("%input_" ++ input.name))]).run state).2 := by
  change LowerStateMeaning hash witness {state with instructions := state.instructions.push _}
  apply meaning.append
  · exact ScalarInstructionEncoding.decode_input _ _ valid
  · trivial
  · intro name member
    simp only [instructionIdentifiers, List.mem_singleton] at member
    subst name
    exact Or.inl ⟨input.name, rfl⟩

theorem scoped_operands (next : Nat) (texts : List String)
    (scopes : ∀ text ∈ texts, TextScope next text) :
    ∃ operands, decodeOperands (toJson texts) = .ok operands ∧
      ∀ name ∈ operands.flatMap operandIdentifiers, InScope next name := by
  have listResult : ∃ operands, texts.mapM (fun text => decodeOperand (toJson text)) = .ok operands ∧
      ∀ name ∈ operands.flatMap operandIdentifiers, InScope next name := by
    induction texts with
    | nil => exact ⟨[], rfl, by simp⟩
    | cons text texts ih =>
      obtain ⟨operand, parsed, scope⟩ := scopes text (by simp)
      obtain ⟨operands, tailParsed, tailScope⟩ := ih
        (by intro value member; exact scopes value (by simp [member]))
      refine ⟨operand :: operands, ?_, ?_⟩
      · simp only [List.mapM_cons, parsed, tailParsed, Bind.bind, Except.bind]
        rfl
      · intro name member
        simp only [List.flatMap_cons, List.mem_append] at member
        exact member.elim (scope name) (tailScope name)
  obtain ⟨operands, parsed, scope⟩ := listResult
  refine ⟨operands, ?_, scope⟩
  unfold decodeOperands
  change ((texts.toArray.map toJson).toList.mapM decodeOperand) = .ok operands
  simpa only [Array.toList_map, List.toList_toArray, List.mapM_map, Function.comp_def] using parsed

theorem emit_impact (hash : Hash) (witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (meaning : LowerStateMeaning hash witness state)
    (texts : List String) (scopes : ∀ text ∈ texts, TextScope state.next text) :
    LowerStateMeaning hash witness ((Zkir.bindPublic texts).run state).2 := by
  obtain ⟨operands, parsed, scope⟩ := scoped_operands state.next texts scopes
  change LowerStateMeaning hash witness {state with instructions := state.instructions.push _}
  exact LowerStateMeaning.append hash witness state meaning _ _
    (ScalarInstructionEncoding.decode_impact_instruction parsed) rfl
    (by simpa only [instructionIdentifiers, operandIdentifiers, List.nil_append] using scope)

theorem emit_output (hash : Hash) (witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (meaning : LowerStateMeaning hash witness state)
    (texts : List String) (scopes : ∀ text ∈ texts, TextScope state.next text) :
    LowerStateMeaning hash witness ((Zkir.emit "output" [("vals", toJson texts)]).run state).2 := by
  obtain ⟨operands, parsed, scope⟩ := scoped_operands state.next texts scopes
  change LowerStateMeaning hash witness {state with instructions := state.instructions.push _}
  exact LowerStateMeaning.append hash witness state meaning _ _
    (ScalarInstructionEncoding.decode_output_instruction parsed) True.intro scope

theorem emit_assert (hash : Hash) (witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (meaning : LowerStateMeaning hash witness state)
    (text : String) (scope : TextScope state.next text)
    (value : ∃ operand, decodeOperand (toJson text) = .ok operand ∧ operand.read witness = one) :
    LowerStateMeaning hash witness ((Zkir.emit "assert" [("cond", toJson text)]).run state).2 := by
  obtain ⟨operand, parsed, value⟩ := value
  obtain ⟨found, decoded, identifiers⟩ := scope
  rw [parsed] at decoded
  cases decoded
  change LowerStateMeaning hash witness {state with instructions := state.instructions.push _}
  apply LowerStateMeaning.append hash witness state meaning _ _
    (ScalarInstructionEncoding.decode_assert_instruction parsed)
  · change operand.read witness ≠ zero
    rw [value]
    decide
  · exact identifiers

structure PrefixExtension (hash : Hash) (beforeWitness : NativeRelation.Assignment)
    (before after : Zkir.LowerState) where
  witness : NativeRelation.Assignment
  meaning : LowerStateMeaning hash witness after
  aliases : after.aliases = before.aliases
  frame : ∀ name, InScope before.next name → witness name = beforeWitness name

def InputFrame (inputs witness : NativeRelation.Assignment) : Prop :=
  ∀ name, witness ("%input_" ++ name) = inputs ("%input_" ++ name)

/-- Compose witness extensions through stages that preserve lowered aliases.
Standalone circuits start with no aliases. Ledger stages may begin after
output aliases have been installed. -/
def Completes (hash : Hash) (inputs : NativeRelation.Assignment)
    (operation : StateM Zkir.LowerState α)
    (aliasRequirement : List (String × String) → Prop := fun aliases => aliases = []) : Prop :=
  ∀ witness state, LowerStateMeaning hash witness state → InputFrame inputs witness →
    aliasRequirement state.aliases →
    (operation.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength →
    Nonempty (PrefixExtension hash witness state (operation.run state).2)

theorem completes_pure (hash : Hash) (inputs : NativeRelation.Assignment) (value : α)
    {aliasRequirement : List (String × String) → Prop} :
    Completes hash inputs (pure value) aliasRequirement := by
  intro witness state meaning inputFrame aliases budget
  exact ⟨{witness, meaning, aliases := rfl, frame := by intro name _; rfl}⟩

theorem completes_emit_input (hash : Hash) (inputs : NativeRelation.Assignment) (input : Input)
    (valid : validIdentifier ("%input_" ++ input.name) = true)
    {aliasRequirement : List (String × String) → Prop} :
    Completes hash inputs
      (Zkir.emit (if input.visibility == .«public» then "public_input" else "private_input")
        [("guard", Json.null), ("type", toJson ("Scalar<BLS12-381>" : String)),
          ("output", toJson ("%input_" ++ input.name))]) aliasRequirement := by
  intro witness state meaning inputFrame aliases budget
  exact ⟨{witness, meaning := emit_input hash witness state meaning input valid, aliases := rfl, frame := by intro name _; rfl}⟩

theorem completes_bind (hash : Hash) (inputs : NativeRelation.Assignment)
    (first : StateM Zkir.LowerState α) (next : α → StateM Zkir.LowerState β)
    (firstFrame : Zkir.PreservesOutputCapacityFrame first)
    (nextFrame : ∀ value, Zkir.PreservesOutputCapacityFrame (next value))
    {aliasRequirement : List (String × String) → Prop}
    (firstComplete : Completes hash inputs first aliasRequirement)
    (nextComplete : ∀ value, Completes hash inputs (next value) aliasRequirement) :
    Completes hash inputs (first >>= next) aliasRequirement := by
  intro witness state meaning inputFrame aliases budget
  have runBudget : ((next (first.run state).1).run (first.run state).2).2.next ≤
      Native.maxInstructions * Native.maxVectorLength := budget
  have middleBudget : (first.run state).2.next ≤ Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans (nextFrame _ _).next runBudget
  obtain ⟨left⟩ := firstComplete witness state meaning inputFrame aliases middleBudget
  have nextInput : InputFrame inputs left.witness := fun name =>
    (left.frame _ (Or.inl ⟨name, rfl⟩)).trans (inputFrame name)
  have nextAliases : aliasRequirement (first.run state).2.aliases := by
    rw [left.aliases]
    exact aliases
  obtain ⟨right⟩ := nextComplete _ left.witness _ left.meaning nextInput nextAliases runBudget
  refine ⟨{witness := right.witness, meaning := right.meaning, aliases := right.aliases.trans left.aliases, frame := ?_}⟩
  intro name scope
  exact (right.frame name (InScope.mono (firstFrame state).next scope)).trans
    (left.frame name scope)

theorem completes_forIn (hash : Hash) (inputs : NativeRelation.Assignment) (items : List α)
    (initial : β) (body : α → StateM Zkir.LowerState Unit)
    (frames : ∀ item ∈ items, Zkir.PreservesOutputCapacityFrame (body item))
    {aliasRequirement : List (String × String) → Prop}
    (complete : ∀ item ∈ items, Completes hash inputs (body item) aliasRequirement) :
    Completes hash inputs
      (forIn items initial (fun item _ => do body item; pure (.yield initial))) aliasRequirement := by
  induction items with
  | nil => exact completes_pure hash inputs initial
  | cons item items ih =>
    rw [List.forIn_cons]
    simp only [bind_assoc, pure_bind]
    change Completes hash inputs
      (body item >>= fun _ => forIn items initial (fun item _ => do body item; pure (.yield initial)))
      aliasRequirement
    apply completes_bind hash inputs _ _ (frames item (by simp))
    · intro value
      exact Zkir.forIn_preservesOutputCapacityFrame_of_mem items initial _
        (by
          intro item member accumulator
          exact Zkir.bind_preservesOutputCapacityFrame _ _
            (frames item (List.mem_cons_of_mem _ member))
            (fun _ => Zkir.pure_preservesOutputCapacityFrame _))
    · exact complete item (by simp)
    · intro value
      apply ih
      · intro item member
        exact frames item (List.mem_cons_of_mem _ member)
      · intro item member
        exact complete item (List.mem_cons_of_mem _ member)

end Noctium.Verification.ScalarWitnessConstruction
