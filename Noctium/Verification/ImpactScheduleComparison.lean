import Noctium.Verification.ImpactExpressionComparison
import Noctium.Verification.ImpactPlanAgreement
import Noctium.Verification.ImpactTranscriptSchedule

namespace Noctium.Verification.ImpactScheduleComparison

open Lean
open Noctium.Verification.ImpactWireDecoder
open Noctium.Verification.ImpactExpressionEvaluation
open Noctium.Verification.ImpactExpressionComparison (evaluate_eq_of_matches)
open Noctium.Verification.ImpactOperationAgreement
open Noctium.Verification.ImpactScheduledAgreement
open Noctium.Verification.ImpactTranscriptSchedule
open Noctium.Verification.ImpactTranscriptWidth

private def expressionOptionMatches (budget : Nat) : Option Json → Option Json → _root_.Bool
  | none, none => Bool.true
  | some left, some right => ImpactExpressionComparison.«matches» budget left right
  | _, _ => Bool.false

/-- Compare the supported scalar operation shapes and their operand trees. -/
private def operationMatches (budget : Nat) : Operation → Operation → _root_.Bool
  | .dup, .dup => Bool.true
  | .index leftSlot leftPath leftKey, .index rightSlot rightPath rightKey =>
      leftSlot == rightSlot && leftPath == rightPath &&
        expressionOptionMatches budget leftKey rightKey
  | .push leftStorage leftAlignment leftExpression,
      .push rightStorage rightAlignment rightExpression =>
      leftStorage == rightStorage && leftAlignment == rightAlignment &&
        ImpactExpressionComparison.«matches» budget leftExpression rightExpression
  | .popeq leftAlignment leftExpression, .popeq rightAlignment rightExpression =>
      leftAlignment == rightAlignment &&
        ImpactExpressionComparison.«matches» budget leftExpression rightExpression
  | .member, .member => Bool.true
  | .insert leftDepth, .insert rightDepth => leftDepth == rightDepth
  | _, _ => Bool.false

private def scheduledMatches (budget : Nat) (left right : ScheduledOperation) : _root_.Bool :=
  expressionOptionMatches budget left.guard right.guard &&
    operationMatches budget left.operation right.operation

private def schedulesMatch (budget : Nat) : List ScheduledOperation → List ScheduledOperation → _root_.Bool
  | [], [] => Bool.true
  | left :: leftRest, right :: rightRest =>
      scheduledMatches budget left right && schedulesMatch budget leftRest rightRest
  | _, _ => Bool.false

/-- Accept two plans when both decode as scalar Impact schedules of equal
length and every item matches in order. -/
def «matches» (budget : Nat) (left right : Json) : _root_.Bool :=
  match ImpactWireDecoder.decodePlanOperations left,
      ImpactWireDecoder.decodePlanOperations right with
  | .ok leftItems, .ok rightItems =>
      schedulesMatch budget leftItems rightItems
  | _, _ => Bool.false

private theorem evaluateOperation_eq_of_matches {budget : Nat}
    {left right : Operation}
    (matched : operationMatches budget left right = Bool.true)
    (fuel : Nat) (ctx : EvalContext) (env : EvalEnv) :
    ImpactOperationAgreement.evaluateOperation fuel ctx env left =
      ImpactOperationAgreement.evaluateOperation fuel ctx env right := by
  cases left with
  | dup =>
      cases right <;> simp [operationMatches, ImpactOperationAgreement.evaluateOperation] at matched ⊢
  | index leftSlot leftPath leftKey =>
      cases right with
      | dup => simp [operationMatches] at matched
      | index rightSlot rightPath rightKey =>
          simp only [operationMatches, Bool.and_eq_true, beq_iff_eq] at matched
          obtain ⟨⟨slotEq, pathEq⟩, keyMatch⟩ := matched
          subst rightSlot
          subst rightPath
          cases leftKey with
          | none =>
              cases rightKey <;>
                simp [expressionOptionMatches, ImpactOperationAgreement.evaluateOperation] at keyMatch ⊢
          | some leftRaw =>
              cases rightKey with
              | none => simp [expressionOptionMatches] at keyMatch
              | some rightRaw =>
                  have equal := evaluate_eq_of_matches keyMatch fuel ctx env
                  cases leftPath <;> simp [ImpactOperationAgreement.evaluateOperation,
                    ImpactOperationAgreement.evaluateAligned, equal]
      | _ => simp [operationMatches] at matched
  | push leftStorage leftAlignment leftRaw =>
      cases right with
      | push rightStorage rightAlignment rightRaw =>
          simp only [operationMatches, Bool.and_eq_true, beq_iff_eq] at matched
          obtain ⟨⟨storageEq, alignmentEq⟩, expressionMatch⟩ := matched
          subst rightStorage
          subst rightAlignment
          have equal := evaluate_eq_of_matches expressionMatch fuel ctx env
          simp [ImpactOperationAgreement.evaluateOperation,
            ImpactOperationAgreement.evaluateAligned, equal]
      | _ => simp [operationMatches] at matched
  | popeq leftAlignment leftRaw =>
      cases right with
      | popeq rightAlignment rightRaw =>
          simp only [operationMatches, Bool.and_eq_true, beq_iff_eq] at matched
          obtain ⟨alignmentEq, expressionMatch⟩ := matched
          subst rightAlignment
          have equal := evaluate_eq_of_matches expressionMatch fuel ctx env
          simp [ImpactOperationAgreement.evaluateOperation,
            ImpactOperationAgreement.evaluateAligned, equal]
      | _ => simp [operationMatches] at matched
  | «member» =>
      cases right <;> simp [operationMatches, ImpactOperationAgreement.evaluateOperation] at matched ⊢
  | «insert» leftDepth =>
      cases right with
      | «insert» rightDepth =>
          simp only [operationMatches, beq_iff_eq] at matched
          subst rightDepth
          rfl
      | _ => simp [operationMatches] at matched

private theorem evaluateOperationWidth_eq_of_matches {budget : Nat}
    {left right : Operation}
    (matched : operationMatches budget left right = Bool.true)
    (keyWidth : Nat → Option Nat) :
    operationWidth keyWidth left = operationWidth keyWidth right := by
  cases left with
  | dup => cases right <;> simp [operationMatches, operationWidth] at matched ⊢
  | index leftSlot leftPath leftKey =>
      cases right with
      | index rightSlot rightPath rightKey =>
          simp only [operationMatches, Bool.and_eq_true, beq_iff_eq] at matched
          obtain ⟨⟨slotEq, pathEq⟩, keyMatch⟩ := matched
          subst rightSlot
          subst rightPath
          cases leftKey <;> cases rightKey <;> cases leftPath <;>
            simp [expressionOptionMatches, operationWidth] at keyMatch ⊢
      | _ => simp [operationMatches] at matched
  | push leftStorage leftAlignment leftRaw =>
      cases right with
      | push rightStorage rightAlignment rightRaw =>
          simp only [operationMatches, Bool.and_eq_true, beq_iff_eq] at matched
          obtain ⟨⟨_, alignmentEq⟩, _⟩ := matched
          subst rightAlignment
          rfl
      | _ => simp [operationMatches] at matched
  | popeq leftAlignment leftRaw =>
      cases right with
      | popeq rightAlignment rightRaw =>
          simp only [operationMatches, Bool.and_eq_true, beq_iff_eq] at matched
          obtain ⟨alignmentEq, _⟩ := matched
          subst rightAlignment
          rfl
      | _ => simp [operationMatches] at matched
  | «member» => cases right <;> simp [operationMatches, operationWidth] at matched ⊢
  | «insert» leftDepth =>
      cases right with
      | «insert» rightDepth =>
          simp only [operationMatches, beq_iff_eq] at matched
          subst rightDepth
          rfl
      | _ => simp [operationMatches] at matched

private theorem evaluateActivityGuard_eq_of_matches {budget : Nat}
    {left right : Option Json}
    (matched : expressionOptionMatches budget left right = Bool.true)
    (fuel : Nat) (ctx : EvalContext) (env : EvalEnv) :
    ImpactScheduledAgreement.evaluateActivityGuard fuel ctx env left =
      ImpactScheduledAgreement.evaluateActivityGuard fuel ctx env right := by
  cases left with
  | none =>
      cases right <;> simp [expressionOptionMatches, evaluateActivityGuard] at matched ⊢
  | some leftRaw =>
      cases right with
      | none => simp [expressionOptionMatches] at matched
      | some rightRaw =>
          have equal := evaluate_eq_of_matches matched fuel ctx env
          simp [evaluateActivityGuard, equal]

private theorem evaluateScheduledOperation_eq_of_matches {budget : Nat}
    {left right : ScheduledOperation}
    (matched : scheduledMatches budget left right = Bool.true)
    (fuel : Nat) (ctx : EvalContext) (env : EvalEnv) :
    ImpactScheduledAgreement.evaluateScheduledOperation fuel ctx env left =
      ImpactScheduledAgreement.evaluateScheduledOperation fuel ctx env right := by
  simp only [scheduledMatches, Bool.and_eq_true] at matched
  obtain ⟨guardMatch, operationMatch⟩ := matched
  have guardEq := evaluateActivityGuard_eq_of_matches guardMatch fuel ctx env
  have operationEq := evaluateOperation_eq_of_matches operationMatch fuel ctx env
  unfold ImpactScheduledAgreement.evaluateScheduledOperation
  rw [guardEq, operationEq]

private theorem evaluateGroups_eq_of_matches {budget : Nat}
    {left right : ScheduledOperation}
    (matched : scheduledMatches budget left right = Bool.true)
    (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (keyWidth : Nat → Option Nat) :
    ImpactTranscriptSchedule.evaluateGroups fuel ctx env keyWidth left =
      ImpactTranscriptSchedule.evaluateGroups fuel ctx env keyWidth right := by
  simp only [scheduledMatches, Bool.and_eq_true] at matched
  obtain ⟨guardMatch, operationMatch⟩ := matched
  have guardEq := evaluateActivityGuard_eq_of_matches guardMatch fuel ctx env
  have widthEq := evaluateOperationWidth_eq_of_matches operationMatch keyWidth
  unfold ImpactTranscriptSchedule.evaluateGroups
  rw [guardEq, widthEq]

private theorem mapM_eq_of_schedulesMatch {budget : Nat} {α : Type}
    (left right : List ScheduledOperation)
    (matched : schedulesMatch budget left right = Bool.true)
    (f g : ScheduledOperation → Option α)
    (itemEq : ∀ a b, scheduledMatches budget a b = Bool.true → f a = g b) :
    left.mapM f = right.mapM g := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [schedulesMatch] at matched ⊢
  | cons leftItem leftRest ih =>
      cases right with
      | nil => simp [schedulesMatch] at matched
      | cons rightItem rightRest =>
          simp only [schedulesMatch, Bool.and_eq_true] at matched
          obtain ⟨headMatch, tailMatch⟩ := matched
          rw [List.mapM_cons, List.mapM_cons, itemEq leftItem rightItem headMatch,
            ih rightRest tailMatch]

/-- Matched schedules preserve both modeled program operations and transcript
group metadata, including rejection from either expression evaluator. -/
theorem evaluations_eq_of_matches {budget : Nat} {left right : Json}
    (matched : «matches» budget left right = Bool.true)
    (fuel : Nat) (ctx : EvalContext) (env : EvalEnv)
    (keyWidth : Nat → Option Nat) :
    ImpactPlanAgreement.evaluatePlan fuel ctx env left =
        ImpactPlanAgreement.evaluatePlan fuel ctx env right ∧
      ImpactTranscriptSchedule.evaluateSchedule fuel ctx env keyWidth left =
        ImpactTranscriptSchedule.evaluateSchedule fuel ctx env keyWidth right := by
  cases leftDecoded : ImpactWireDecoder.decodePlanOperations left with
  | error message =>
      simp [«matches», leftDecoded] at matched
  | ok leftItems =>
      cases rightDecoded : ImpactWireDecoder.decodePlanOperations right with
      | error message => simp [«matches», leftDecoded, rightDecoded] at matched
      | ok rightItems =>
          have scheduleMatch : schedulesMatch budget leftItems rightItems = Bool.true := by
            simpa [«matches», leftDecoded, rightDecoded] using matched
          have programItems := mapM_eq_of_schedulesMatch leftItems rightItems scheduleMatch
            (ImpactScheduledAgreement.evaluateScheduledOperation fuel ctx env)
            (ImpactScheduledAgreement.evaluateScheduledOperation fuel ctx env)
            (fun a b h => evaluateScheduledOperation_eq_of_matches h fuel ctx env)
          have groupItems := mapM_eq_of_schedulesMatch leftItems rightItems scheduleMatch
            (ImpactTranscriptSchedule.evaluateGroups fuel ctx env keyWidth)
            (ImpactTranscriptSchedule.evaluateGroups fuel ctx env keyWidth)
            (fun a b h => evaluateGroups_eq_of_matches h fuel ctx env keyWidth)
          constructor
          · simpa [ImpactPlanAgreement.evaluatePlan, leftDecoded, rightDecoded, Except.toOption] using
              congrArg (Option.map List.flatten) programItems
          · simpa [ImpactTranscriptSchedule.evaluateSchedule, leftDecoded, rightDecoded,
            Except.toOption] using
              congrArg (Option.map List.flatten) groupItems

end Noctium.Verification.ImpactScheduleComparison
