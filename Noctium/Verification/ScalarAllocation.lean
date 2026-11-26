import Noctium.Backend.Zkir

namespace Noctium.Verification.ScalarAllocation
open Backend

/-- The backend output-slot allocation frame used by witness composition. -/
abbrev Frame := Zkir.OutputCapacityFrame

/-- Lowering keeps fresh SSA allocation within the output definitions emitted
by its native instructions. -/
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

theorem modify_preserves (update : Zkir.LowerState → Zkir.LowerState)
    (preserves : ∀ state, Frame state (update state)) :
    PreservesFrame (modify update) :=
  preserves

theorem emit_preserves (opcode : String) (fields : List (String × Lean.Json)) :
    PreservesFrame (Zkir.emit opcode fields) :=
  Zkir.emit_preservesOutputCapacityFrame opcode fields

theorem constrainType_preserves (ty : Ty) (value : String) :
    PreservesFrame (Zkir.constrainType ty value) :=
  Zkir.constrainType_preservesOutputCapacityFrame ty value

theorem bindPublic_preserves (values : List String) :
    PreservesFrame (Zkir.bindPublic values) :=
  Zkir.emit_preservesOutputCapacityFrame _ _

theorem lowerExpr_preserves (expression : Expr ty) :
    PreservesFrame (Zkir.lowerExpr expression) :=
  Zkir.lowerExpr_preservesOutputCapacityFrame expression

theorem forIn_preserves (items : List α) (initial : β)
    (body : α → β → StateM Zkir.LowerState (ForInStep β))
    (preserves : ∀ item accumulator, PreservesFrame (body item accumulator)) :
    PreservesFrame (forIn items initial body) := by
  apply Zkir.forIn_preservesOutputCapacityFrame_of_mem
  intro item member accumulator
  exact preserves item accumulator

/-- Bound an intermediate state by the final state when the remaining
computation preserves output capacity. -/
theorem bind_middle_budget (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState)
    (remaining : ∀ value, PreservesFrame (next value)) (limit : Nat)
    (bound : ((first >>= next).run state).2.next ≤ limit) :
    (first.run state).2.next ≤ limit := by
  have frame : Frame (first.run state).2 ((first >>= next).run state).2 := by
    change Frame (first.run state).2
      ((next (first.run state).1).run (first.run state).2).2
    exact remaining _ _
  exact Nat.le_trans frame.next bound

end Noctium.Verification.ScalarAllocation
