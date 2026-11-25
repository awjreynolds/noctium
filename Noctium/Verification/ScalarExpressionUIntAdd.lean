import Noctium.Verification.ScalarNativeWitnessSteps
import Noctium.Verification.ScalarAllocationOutputFrame
import Noctium.Verification.ScalarRangeLowering
import Noctium.Verification.ScalarStateExtensions

namespace Noctium.Verification.ScalarWitnessConstruction

open Lean Backend NativeRelation NativeRelationJson ScalarLowering ScalarNormalization
open ScalarInstructionEncoding ScalarWitness

private theorem fresh_binary_scope (next : Nat) (left right : Operand)
    (leftScope : ∀ name ∈ operandIdentifiers left, InScope next name)
    (rightScope : ∀ name ∈ operandIdentifiers right, InScope next name) :
    ∀ name ∈ operandIdentifiers left ++ operandIdentifiers right ++ [s!"%v{next}"],
      InScope (next + 1) name := by
  intro name member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (member | member) | rfl
  · exact InScope.mono (by omega) (leftScope name member)
  · exact InScope.mono (by omega) (rightScope name member)
  · exact Or.inr ⟨next, by omega, rfl⟩

private theorem state_from_suffix (hash : Hash) (witness afterWitness : NativeRelation.Assignment)
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

private theorem bind_middle_next (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState)
    (preserves : ∀ value, Zkir.PreservesOutputCapacityFrame (next value)) :
    (first.run state).2.next ≤ ((first >>= next).run state).2.next := by
  change (first.run state).2.next ≤
    ((next (first.run state).1).run (first.run state).2).2.next
  exact (preserves (first.run state).1 (first.run state).2).next

/-- Extend an arbitrary satisfying prefix through the emitted UInt range check.
The input operand is an existing scoped reference or immediate, so the only
new witness value is the comparison result emitted for a non-power bound. -/
theorem constrainUnsigned_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (maximum : Nat) (text : String) (term : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (meaning : OperandMeaning hash inputs witness text term) (scope : TextScope state.next text)
    (range : ∃ value, interpret hash inputs term = some value ∧ value.val ≤ maximum)
    (admitted : maximum ≤ ScalarPolicy.maxUint)
    (budget : ((do Zkir.constrainUnsigned maximum text; pure text).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state
      (do Zkir.constrainUnsigned maximum text; pure text) term) := by
  rcases meaning with ⟨operand, operandDecoded, operandMeaning⟩
  obtain ⟨rangeValue, rangeMeaning, rangeBound⟩ := range
  have valueEqual : rangeValue = operand.read witness :=
    Option.some.inj (rangeMeaning.symm.trans operandMeaning)
  have rangeWitness : (operand.read witness).val ≤ maximum := by
    simpa only [valueEqual] using rangeBound
  obtain ⟨prior, priorDecoded⟩ := stateMeaning.decoded
  obtain ⟨scopedOperand, scopedDecoded, names⟩ := scope
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
      (stateMeaning.scope prior priorDecoded instruction member)
  obtain ⟨afterWitness, instructions, decoded, nativeHolds, stable, frame, extension⟩ :=
    ScalarRangeLowering.constrainUnsigned_complete hash witness state maximum text operand prior
      operandDecoded priorDecoded (stateMeaning.holds prior priorDecoded) rangeWitness admitted
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
        [.equal operand (.immediate zero)] stateMeaning priorDecoded
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
          [.bits operand (maximum.log2 + 1)] stateMeaning priorDecoded
          (ScalarRangeLowering.power_decode state maximum text operand prior isZero power
            admitted operandDecoded priorDecoded)
          allHolds next aliasesSame cacheSame
        intro instruction member name nameMember
        have equal := List.mem_singleton.mp member
        subst instruction
        exact InScope.mono next (names name nameMember)
      · apply state_from_suffix hash witness afterWitness state after prior
          [.bits operand (maximum.log2 + 1),
            .lessThan operand (.immediate (scalar (maximum + 1))) (maximum.log2 + 1)
              s!"%v{state.next}", .assert (.reference s!"%v{state.next}")]
          stateMeaning priorDecoded
          (ScalarRangeLowering.nonpower_decode state maximum text operand prior isZero power
            admitted startBudget operandDecoded priorDecoded)
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
  refine ⟨{
    text := text
    finalState := after
    finalWitness := afterWitness
    run := rfl
    operandMeaning := OperandMeaning.of_frame hash inputs witness afterWitness
      state.next text term ⟨operand, operandDecoded, operandMeaning⟩
      ⟨operand, operandDecoded, names⟩ frameOld
    textScope := ⟨operand, operandDecoded,
      fun name member => InScope.mono next (names name member)⟩
    stateMeaning := finalMeaning
    budget := budget
    aliasesPreserved := aliasesSame
    frame := frameOld
  }⟩

private def uintAddTerm {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n))
    (leftTerm rightTerm : Native.Term) : Native.Term :=
  if Native.isLiteralUIntZero left then rightTerm
  else if Native.isLiteralUIntZero right then leftTerm
  else .binary "add" leftTerm rightTerm

private theorem uint_add_step (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) {m n : Nat} (leftSource : Expr (.uint m))
    (rightSource : Expr (.uint n)) (maximum : Nat) (left right : String)
    (leftTerm rightTerm : Native.Term)
    (stateMeaning : LowerStateMeaning hash witness state)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (leftScope : TextScope state.next left) (rightScope : TextScope state.next right)
    (range : ∃ value, interpret hash inputs (uintAddTerm leftSource rightSource leftTerm rightTerm) =
      some value ∧ value.val ≤ maximum)
    (admitted : maximum ≤ ScalarPolicy.maxUint)
    (budget : ((Zkir.nativeUIntAdd maximum (Native.isLiteralUIntZero leftSource)
      (Native.isLiteralUIntZero rightSource) left right).run state).2.next ≤
        Native.maxInstructions * Native.maxVectorLength) :
    Nonempty (NativeStepResult hash inputs witness state
      (Zkir.nativeUIntAdd maximum (Native.isLiteralUIntZero leftSource)
        (Native.isLiteralUIntZero rightSource) left right)
      (uintAddTerm leftSource rightSource leftTerm rightTerm)) := by
  cases leftZero : Native.isLiteralUIntZero leftSource with
  | true =>
    have runEq : Zkir.nativeUIntAdd maximum true (Native.isLiteralUIntZero rightSource)
        left right = (do
          Zkir.constrainUnsigned maximum right
          pure right) := by
      simp [Zkir.nativeUIntAdd, Zkir.nativeAdd]
    have rangeBudget : ((do Zkir.constrainUnsigned maximum right; pure right).run state).2.next ≤
        Native.maxInstructions * Native.maxVectorLength := by
      have bound := budget
      rw [leftZero] at bound
      rw [runEq] at bound
      exact bound
    have rightRange : ∃ value, interpret hash inputs rightTerm = some value ∧ value.val ≤ maximum := by
      simpa [uintAddTerm, leftZero] using range
    obtain ⟨bounded⟩ := constrainUnsigned_step hash inputs witness state maximum right rightTerm
      stateMeaning rightMeaning rightScope rightRange admitted rangeBudget
    have result : NativeStepResult hash inputs witness state
        (Zkir.nativeUIntAdd maximum true (Native.isLiteralUIntZero rightSource) left right) rightTerm := {
      bounded with
      run := by rw [runEq]; exact bounded.run
    }
    exact ⟨by simpa [uintAddTerm, leftZero] using result⟩
  | false =>
    cases rightZero : Native.isLiteralUIntZero rightSource with
    | true =>
      have runEq : Zkir.nativeUIntAdd maximum false true left right = (do
          Zkir.constrainUnsigned maximum left
          pure left) := by
        simp [Zkir.nativeUIntAdd, Zkir.nativeAdd]
      have rangeBudget : ((do Zkir.constrainUnsigned maximum left; pure left).run state).2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
        have bound := budget
        rw [leftZero, rightZero] at bound
        rw [runEq] at bound
        exact bound
      have leftRange : ∃ value, interpret hash inputs leftTerm = some value ∧ value.val ≤ maximum := by
        simpa [uintAddTerm, leftZero, rightZero] using range
      obtain ⟨bounded⟩ := constrainUnsigned_step hash inputs witness state maximum left leftTerm
        stateMeaning leftMeaning leftScope leftRange admitted rangeBudget
      have result : NativeStepResult hash inputs witness state
          (Zkir.nativeUIntAdd maximum false true left right) leftTerm := {
        bounded with
        run := by rw [runEq]; exact bounded.run
      }
      exact ⟨by simpa [uintAddTerm, leftZero, rightZero] using result⟩
    | false =>
      have runEq : Zkir.nativeUIntAdd maximum false false left right = (do
          let output ← Zkir.binary "add" left right
          Zkir.constrainUnsigned maximum output
          pure output) := by
        simp [Zkir.nativeUIntAdd, Zkir.nativeAdd]
      have binaryFrame : Zkir.PreservesOutputCapacityFrame (Zkir.binary "add" left right) :=
        Zkir.ordinaryBinary_preservesOutputCapacityFrame "add" left right ⟨by decide, by decide, by decide⟩
      have suffixFrame (output : String) : Zkir.PreservesOutputCapacityFrame (do
          Zkir.constrainUnsigned maximum output
          pure output) :=
        Zkir.bind_preservesOutputCapacityFrame _ _
          (Zkir.constrainUnsigned_preservesOutputCapacityFrame maximum output)
          (fun _ => Zkir.pure_preservesOutputCapacityFrame output)
      have binaryBudget : ((Zkir.binary "add" left right).run state).2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
        have tailBudget := budget
        rw [leftZero, rightZero] at tailBudget
        rw [runEq] at tailBudget
        exact Nat.le_trans
          (bind_middle_next (Zkir.binary "add" left right)
            (fun output => do Zkir.constrainUnsigned maximum output; pure output) state suffixFrame)
          tailBudget
      obtain ⟨binary⟩ := ScalarWitnessConstruction.binary_add_step hash inputs witness state
        left right leftTerm rightTerm stateMeaning leftMeaning rightMeaning leftScope rightScope binaryBudget
      have rangeBudget : ((do Zkir.constrainUnsigned maximum binary.text; pure binary.text).run
          binary.finalState).2.next ≤ Native.maxInstructions * Native.maxVectorLength := by
        have bound := budget
        rw [leftZero, rightZero] at bound
        rw [runEq, StateT.run_bind, binary.run] at bound
        exact bound
      have binaryRange : ∃ value,
          interpret hash inputs (.binary "add" leftTerm rightTerm) = some value ∧
            value.val ≤ maximum := by
        simpa [uintAddTerm, leftZero, rightZero] using range
      obtain ⟨bounded⟩ := constrainUnsigned_step hash inputs binary.finalWitness binary.finalState
        maximum binary.text (.binary "add" leftTerm rightTerm) binary.stateMeaning
        binary.operandMeaning binary.textScope binaryRange admitted rangeBudget
      have binaryNext : state.next ≤ binary.finalState.next := by
        simpa only [binary.run] using (binaryFrame state).next
      let combined := binary.chain
        (fun text => do Zkir.constrainUnsigned maximum text; pure text) bounded binaryNext
      have result : NativeStepResult hash inputs witness state
          (Zkir.nativeUIntAdd maximum false false left right) (.binary "add" leftTerm rightTerm) := {
        combined with
        run := by rw [runEq]; exact combined.run
      }
      exact ⟨by simpa [uintAddTerm, leftZero, rightZero] using result⟩

/-- UInt addition lowers both source operands, reuses a literal-zero operand
when possible, and proves the emitted output bound from the source result. -/
theorem complete_uadd {m n : Nat} (left : Expr (.uint m)) (right : Expr (.uint n))
    (leftAdmission : ScalarExpression left) (rightAdmission : ScalarExpression right)
    (completeLeft : ExprComplete left) (completeRight : ExprComplete right) :
    ExprComplete (.uadd left right) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  let admission : ScalarExpression (.uadd left right) :=
    .uadd left right leftAdmission rightAdmission
  let tail (a b : String) : StateM Zkir.LowerState String :=
    Zkir.nativeUIntAdd (m + n) (Native.isLiteralUIntZero left)
      (Native.isLiteralUIntZero right) a b
  have lowerRun : Zkir.lowerExpr (.uadd left right) = (do
      let a ← Zkir.lowerExpr left
      let b ← Zkir.lowerExpr right
      tail a b) := by
    simp only [Zkir.lowerExpr, tail]
  have leftFrame := ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
    left leftAdmission
  have rightFrame := ScalarAllocationOutputFrame.lowerExpr_admitted_preservesOutputCapacityFrame
    right rightAdmission
  have tailFrame (a b : String) : Zkir.PreservesOutputCapacityFrame (tail a b) := by
    exact Zkir.nativeUIntAdd_preservesOutputCapacityFrame (m + n)
      (Native.isLiteralUIntZero left) (Native.isLiteralUIntZero right) a b
  have rightSuffixFrame (a : String) : Zkir.PreservesOutputCapacityFrame (do
      let b ← Zkir.lowerExpr right
      tail a b) :=
    Zkir.bind_preservesOutputCapacityFrame _ _ rightFrame (tailFrame a)
  have loweredBudget := budget
  rw [lowerRun] at loweredBudget
  have leftBudget : ((Zkir.lowerExpr left).run state).2.next ≤
      Native.maxInstructions * Native.maxVectorLength :=
    Nat.le_trans (rightSuffixFrame _ _).next loweredBudget
  have validForm : (do
      (Ty.uint (m + n)).validate Capabilities.crypto
      left.validate Capabilities.crypto types
      right.validate Capabilities.crypto types) = .ok () := by
    have nativeArithmetic : Capabilities.crypto.nativeArithmetic = true := rfl
    simpa [Expr.validate, nativeArithmetic] using valid
  rcases ScalarValidationMeaning.bind_ok.mp validForm with
    ⟨_, typeValid, childrenValid⟩
  rcases ScalarValidationMeaning.bind_ok.mp childrenValid with
    ⟨_, leftValid, rightValid⟩
  have typeBound : m + n ≤ ScalarPolicy.maxUint := by
    by_cases bound : m + n ≤ ScalarPolicy.maxUint
    · exact bound
    · simp [Ty.validate, Ty.scalarKind, ScalarPolicy.validate, bound,
        Bind.bind, Except.bind] at typeValid
  cases leftEval : left.eval ctx values with
  | error message => simp [Expr.eval, leftEval, Bind.bind, Except.bind] at success
  | ok leftValue =>
    cases rightEval : right.eval ctx values with
    | error message => simp [Expr.eval, leftEval, rightEval, Bind.bind, Except.bind] at success
    | ok rightValue =>
      obtain ⟨first⟩ := completeLeft ctx hash implementation inputs witness state normalAliases
        values types leftValue leftValid leftEval aliases lowerAliases stateMeaning leftBudget
      have remainingBudget : ((do
          let b ← Zkir.lowerExpr right
          tail first.text b).run first.finalState).2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
        have bound := loweredBudget
        rw [StateT.run_bind, first.run] at bound
        exact bound
      have rightBudget : ((Zkir.lowerExpr right).run first.finalState).2.next ≤
          Native.maxInstructions * Native.maxVectorLength :=
        Nat.le_trans (tailFrame first.text _ _).next remainingBudget
      obtain ⟨second⟩ := completeRight ctx hash implementation inputs first.finalWitness
        first.finalState normalAliases values types rightValue rightValid rightEval aliases
        first.aliasAgreement first.stateMeaning rightBudget
      have firstNext : state.next ≤ first.finalState.next := by
        simpa only [first.run] using (leftFrame state).next
      have secondNext : first.finalState.next ≤ second.finalState.next := by
        simpa only [second.run] using (rightFrame first.finalState).next
      have leftMeaning := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
        first.finalState.next first.text first.normalized.term first.operandMeaning
        first.textScope second.frame
      have leftScope := TextScope.mono secondNext first.textScope
      have tailBudget : (tail first.text second.text).run second.finalState |>.2.next ≤
          Native.maxInstructions * Native.maxVectorLength := by
        rw [StateT.run_bind, second.run] at remainingBudget
        exact remainingBudget
      obtain ⟨normalized, normalization, represents⟩ :=
        normalize_success ctx hash implementation inputs normalAliases values aliases
          (.uadd left right) admission value success
      have termEq : normalized.term = uintAddTerm left right
          first.normalized.term second.normalized.term := by
        have normal := normalization
        simp only [Native.normalize, first.normalization, second.normalization] at normal
        cases normal
        simp only [Native.normalizeUIntAdd, Native.requireSourceType_eq, uintAddTerm]
      have resultMeaning : interpret hash inputs
          (uintAddTerm left right first.normalized.term second.normalized.term) =
          some (scalar value) := by
        rw [← termEq]
        simpa [ScalarNormalization.number] using
          (represents.2.2.trans (sourceScalar_number (ScalarType.uint (m + n)) value))
      have valueBound : value ≤ m + n := represents.1.2.2
      have resultRange : ∃ found,
          interpret hash inputs
            (uintAddTerm left right first.normalized.term second.normalized.term) = some found ∧
          found.val ≤ m + n := by
        refine ⟨scalar value, resultMeaning, ?_⟩
        exact Nat.le_trans (Nat.mod_le value Field.modulus) valueBound
      obtain ⟨native⟩ := uint_add_step hash inputs second.finalWitness second.finalState
        left right (m + n) first.text second.text first.normalized.term second.normalized.term
        second.stateMeaning leftMeaning second.operandMeaning leftScope second.textScope
        resultRange typeBound tailBudget
      let firstNative : NativeStepResult hash inputs witness state
          (Zkir.lowerExpr left) first.normalized.term := {
        text := first.text
        finalState := first.finalState
        finalWitness := first.finalWitness
        run := first.run
        operandMeaning := first.operandMeaning
        textScope := first.textScope
        stateMeaning := first.stateMeaning
        budget := first.budget
        aliasesPreserved := first.aliasesPreserved
        frame := first.frame
      }
      let secondNative : NativeStepResult hash inputs first.finalWitness first.finalState
          (Zkir.lowerExpr right) second.normalized.term := {
        text := second.text
        finalState := second.finalState
        finalWitness := second.finalWitness
        run := second.run
        operandMeaning := second.operandMeaning
        textScope := second.textScope
        stateMeaning := second.stateMeaning
        budget := second.budget
        aliasesPreserved := second.aliasesPreserved
        frame := second.frame
      }
      let pair := firstNative.chain (fun _ => Zkir.lowerExpr right) secondNative firstNext
      let full := pair.chain (fun rightText => tail first.text rightText) native
        (Nat.le_trans firstNext secondNext)
      refine ⟨{
        text := full.text
        finalState := full.finalState
        finalWitness := full.finalWitness
        normalized := normalized
        run := ?_
        normalization := normalization
        represents := represents,
          operandMeaning := by rw [termEq]; exact full.operandMeaning
        textScope := full.textScope
        stateMeaning := full.stateMeaning
        budget := full.budget
        aliasAgreement := ?_
        aliasesPreserved := full.aliasesPreserved
        frame := ?_
      }⟩
      · rw [lowerRun, StateT.run_bind, first.run]
        change ((do
            let b ← Zkir.lowerExpr right
            tail first.text b).run first.finalState) = _
        rw [StateT.run_bind, second.run]
        exact native.run
      · rw [full.aliasesPreserved]
        have agreement := LowerAliasAgreement.of_frame hash inputs second.finalWitness full.finalWitness
          second.finalState.next normalAliases second.finalState.aliases values
          second.aliasAgreement second.stateMeaning.aliases native.frame
        simpa [second.aliasesPreserved, first.aliasesPreserved] using agreement
      · intro name inScope
        change native.finalWitness name = witness name
        rw [native.frame name (InScope.mono secondNext (InScope.mono firstNext inScope)),
          second.frame name (InScope.mono firstNext inScope), first.frame name inScope]

end Noctium.Verification.ScalarWitnessConstruction
