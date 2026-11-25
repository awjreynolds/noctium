import Noctium.Backend.Zkir

namespace Noctium.Verification.ScalarAllocation
open Backend

/-- The backend output-slot allocation frame used by witness composition. -/
abbrev Frame := Zkir.OutputCapacityFrame

theorem Frame.refl (state : Zkir.LowerState) : Frame state state :=
  Zkir.OutputCapacityFrame.refl state

theorem Frame.trans {before middle after : Zkir.LowerState}
    (first : Frame before middle) (second : Frame middle after) : Frame before after :=
  Zkir.OutputCapacityFrame.trans first second

/-- Lowering keeps fresh SSA allocation within the emitted definition slots. -/
abbrev PreservesFrame (operation : StateM Zkir.LowerState α) : Prop :=
  Zkir.PreservesOutputCapacityFrame operation

theorem pure_preserves (value : α) : PreservesFrame (pure value) :=
  Zkir.pure_preservesOutputCapacityFrame value

theorem bind_preserves (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β)
    (firstFrame : PreservesFrame first)
    (nextFrame : ∀ value, PreservesFrame (next value)) :
    PreservesFrame (first >>= next) :=
  Zkir.bind_preservesOutputCapacityFrame first next firstFrame nextFrame

theorem get_preserves : PreservesFrame (get : StateM Zkir.LowerState Zkir.LowerState) := by
  intro state
  exact Zkir.OutputCapacityFrame.refl state

theorem modify_preserves (update : Zkir.LowerState → Zkir.LowerState)
    (preserves : ∀ state, Frame state (update state)) :
    PreservesFrame (modify update) :=
  preserves

theorem emit_preserves (opcode : String) (fields : List (String × Lean.Json)) :
    PreservesFrame (Zkir.emit opcode fields) :=
  Zkir.emit_preservesOutputCapacityFrame opcode fields

/-- The generic binary emitter allocates one definition for ordinary opcodes.
The premise excludes the three opcodes whose output list has a separate ABI. -/
theorem binary_preserves (opcode left right : String)
    (ordinary : opcode ≠ "encode" ∧ opcode ≠ "bytes_into_natives" ∧
      opcode ≠ "into_coordinates") :
    PreservesFrame (Zkir.binary opcode left right) :=
  Zkir.ordinaryBinary_preservesOutputCapacityFrame opcode left right ordinary

/-- The generic unary emitter has the same single-output opcode restriction. -/
theorem unary_preserves (opcode operand : String)
    (ordinary : opcode ≠ "encode" ∧ opcode ≠ "bytes_into_natives" ∧
      opcode ≠ "into_coordinates") :
    PreservesFrame (Zkir.unary opcode operand) :=
  Zkir.ordinaryUnary_preservesOutputCapacityFrame opcode operand ordinary

theorem constrainUnsigned_preserves (maximum : Nat) (value : String) :
    PreservesFrame (Zkir.constrainUnsigned maximum value) :=
  Zkir.constrainUnsigned_preservesOutputCapacityFrame maximum value

theorem constrainType_preserves (ty : Ty) (value : String) :
    PreservesFrame (Zkir.constrainType ty value) :=
  Zkir.constrainType_preservesOutputCapacityFrame ty value

theorem bindPublic_preserves (values : List String) :
    PreservesFrame (Zkir.bindPublic values) :=
  Zkir.emit_preservesOutputCapacityFrame _ _

theorem aliases_preserves (aliases : List (String × String)) :
    PreservesFrame (modify fun state => {state with aliases := aliases}) := by
  apply Zkir.modify_preservesOutputCapacityFrame
  · intro state
    rfl
  · intro state
    rfl

theorem lowerExpr_preserves (expression : Expr ty) :
    PreservesFrame (Zkir.lowerExpr expression) :=
  Zkir.lowerExpr_preservesOutputCapacityFrame expression

theorem lowerExpr_next (expression : Expr ty) (state : Zkir.LowerState) :
    state.next ≤ ((Zkir.lowerExpr expression).run state).2.next :=
  (lowerExpr_preserves expression state).next

theorem forIn_preserves (items : List α) (initial : β)
    (body : α → β → StateM Zkir.LowerState (ForInStep β))
    (preserves : ∀ item accumulator, PreservesFrame (body item accumulator)) :
    PreservesFrame (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact pure_preserves _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply bind_preserves _ _ (preserves item initial)
    intro step
    cases step with
    | done result => exact pure_preserves _
    | yield result => exact ih result

theorem lowerBody_preserves (circuit : Circuit) :
    PreservesFrame (Zkir.lowerBody circuit) :=
  Zkir.lowerBody_outputCapacityFrame circuit

theorem lowerBody_next (circuit : Circuit) (state : Zkir.LowerState) :
    state.next ≤ ((Zkir.lowerBody circuit).run state).2.next :=
  (lowerBody_preserves circuit state).next

/-- Every generated SSA name has a corresponding emitted output definition. -/
theorem lowerBody_allocated (circuit : Circuit) :
    ((Zkir.lowerBody circuit).run {}).2.next ≤
      ((Zkir.lowerBody circuit).run {}).2.outputDefinitions := by
  have frame := lowerBody_preserves circuit {}
  exact frame.next_le_outputDefinitions (by simp [Zkir.LowerState.outputDefinitions])

theorem Frame.budget {before after : Zkir.LowerState} (frame : Frame before after)
    (limit : Nat) (bound : after.next ≤ limit) : before.next ≤ limit :=
  Nat.le_trans frame.next bound

/-- The state between two actual lowering computations is bounded by their
actual final state when the remaining computation preserves allocation order. -/
theorem bind_middle_frame (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState)
    (remaining : ∀ value, PreservesFrame (next value)) :
    Frame (first.run state).2 ((first >>= next).run state).2 := by
  change Frame (first.run state).2 ((next (first.run state).1).run (first.run state).2).2
  exact remaining _ _

theorem bind_middle_budget (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState)
    (remaining : ∀ value, PreservesFrame (next value)) (limit : Nat)
    (bound : ((first >>= next).run state).2.next ≤ limit) :
    (first.run state).2.next ≤ limit :=
  (bind_middle_frame first next state remaining).budget limit bound

end Noctium.Verification.ScalarAllocation
