import Noctium.Verification.ScalarLowering

namespace Noctium.Verification.ScalarCache

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering ScalarInstructionEncoding

theorem cached_testEq_meaning (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (left right result : String) (leftTerm rightTerm : Backend.Native.Term)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (hit : state.expressions.lookup ("test_eq", [left, right], none) = some result) :
    OperandMeaning hash inputs witness result (.binary "test_eq" leftTerm rightTerm) := by
  rcases leftMeaning with ⟨leftOperand, leftDecoded, leftValue⟩
  rcases rightMeaning with ⟨rightOperand, rightDecoded, rightValue⟩
  obtain ⟨instructions, decoded, instruction, member, correspondence⟩ :=
    invariant.cacheTrace _ result (ScalarValidationMeaning.lookup_member hit)
  cases instruction <;> simp [CacheCorresponds] at correspondence
  next foundLeft foundRight output =>
    rcases correspondence with ⟨resultEq, a, b, ⟨rfl, rfl⟩, foundLeftDecoded, foundRightDecoded, outputValid⟩
    subst result
    have leftEq : foundLeft = leftOperand := Except.ok.inj (foundLeftDecoded.symm.trans leftDecoded)
    have rightEq : foundRight = rightOperand := Except.ok.inj (foundRightDecoded.symm.trans rightDecoded)
    have holds := invariant.holds instructions decoded (.testEq foundLeft foundRight output) member
    rw [leftEq, rightEq] at holds
    refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
    simp only [Operand.read]
    simp only [interpret_testEq, leftValue, rightValue, Option.bind_some]
    exact congrArg some holds.symm

theorem cached_neg_meaning (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (text result : String) (term : Backend.Native.Term)
    (meaning : OperandMeaning hash inputs witness text term)
    (hit : state.expressions.lookup ("neg", [text], none) = some result) :
    OperandMeaning hash inputs witness result (.unary "neg" term) := by
  rcases meaning with ⟨operand, operandDecoded, operandValue⟩
  obtain ⟨instructions, decoded, instruction, member, correspondence⟩ :=
    invariant.cacheTrace _ result (ScalarValidationMeaning.lookup_member hit)
  cases instruction <;> simp [CacheCorresponds] at correspondence
  next found output =>
    rcases correspondence with ⟨resultEq, foundDecoded, outputValid⟩
    subst result
    have operandEq : found = operand := Except.ok.inj (foundDecoded.symm.trans operandDecoded)
    have holds := invariant.holds instructions decoded (.neg found output) member
    rw [operandEq] at holds
    refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
    simp only [Operand.read]
    simp only [interpret_neg, operandValue, Option.bind_some]
    exact congrArg some holds.symm

theorem cached_not_meaning (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (text result : String) (term : Backend.Native.Term)
    (meaning : OperandMeaning hash inputs witness text term)
    (hit : state.expressions.lookup ("not", [text], none) = some result) :
    OperandMeaning hash inputs witness result (.unary "not" term) := by
  rcases meaning with ⟨operand, operandDecoded, operandValue⟩
  obtain ⟨instructions, decoded, instruction, member, correspondence⟩ :=
    invariant.cacheTrace _ result (ScalarValidationMeaning.lookup_member hit)
  cases instruction <;> simp [CacheCorresponds] at correspondence
  next found output =>
    rcases correspondence with ⟨resultEq, foundDecoded, outputValid⟩
    subst result
    have operandEq : found = operand := Except.ok.inj (foundDecoded.symm.trans operandDecoded)
    have holds := invariant.holds instructions decoded (.not found output) member
    rw [operandEq] at holds
    have isZeroOrOne : Operand.read witness operand = zero ∨
        Operand.read witness operand = one := holds.1
    have resultValue := holds.2
    refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
    simp only [Operand.read]
    rcases isZeroOrOne with isZero | isOne
    · have outputIsOne : witness output = one := by simpa [isZero] using resultValue
      simp [interpret_not, operandValue, isZero, outputIsOne, bit]
    · have outputIsZero : witness output = zero := by
        have isNotZero : Operand.read witness operand ≠ zero := by
          intro equal
          rw [equal] at isOne
          exact zero_ne_one isOne
        simpa [isNotZero] using resultValue
      simp [interpret_not, operandValue, isOne, Ne.symm zero_ne_one,
        outputIsZero, bit]

theorem cached_select_meaning (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (condition yes no result : String) (conditionTerm yesTerm noTerm : Backend.Native.Term)
    (conditionMeaning : OperandMeaning hash inputs witness condition conditionTerm)
    (yesMeaning : OperandMeaning hash inputs witness yes yesTerm)
    (noMeaning : OperandMeaning hash inputs witness no noTerm)
    (hit : state.expressions.lookup ("cond_select", [condition, yes, no], none) = some result) :
    OperandMeaning hash inputs witness result (.select conditionTerm yesTerm noTerm) := by
  rcases conditionMeaning with ⟨conditionOperand, conditionDecoded, conditionValue⟩
  rcases yesMeaning with ⟨yesOperand, yesDecoded, yesValue⟩
  rcases noMeaning with ⟨noOperand, noDecoded, noValue⟩
  obtain ⟨instructions, decoded, instruction, member, correspondence⟩ :=
    invariant.cacheTrace _ result (ScalarValidationMeaning.lookup_member hit)
  cases instruction <;> simp [CacheCorresponds] at correspondence
  next foundCondition foundYes foundNo output =>
    rcases correspondence with ⟨resultEq, c, a, b, ⟨rfl, rfl, rfl⟩, foundConditionDecoded, foundYesDecoded, foundNoDecoded, outputValid⟩
    subst result
    have conditionEq : foundCondition = conditionOperand :=
      Except.ok.inj (foundConditionDecoded.symm.trans conditionDecoded)
    have yesEq : foundYes = yesOperand := Except.ok.inj (foundYesDecoded.symm.trans yesDecoded)
    have noEq : foundNo = noOperand := Except.ok.inj (foundNoDecoded.symm.trans noDecoded)
    have holds := invariant.holds instructions decoded (.select foundCondition foundYes foundNo output) member
    rw [conditionEq, yesEq, noEq] at holds
    have boolean : conditionOperand.read witness = zero ∨
        conditionOperand.read witness = one := holds.1
    have resultValue := holds.2
    refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
    simp only [Operand.read]
    rcases boolean with isZero | isOne
    · have outputValue : witness output = noOperand.read witness := by
        simpa [isZero, zero_ne_one] using resultValue
      simp [interpret_select, conditionValue, yesValue, noValue, isZero,
        zero_ne_one, outputValue]
    · have outputValue : witness output = yesOperand.read witness := by
        simpa [isOne] using resultValue
      simp [interpret_select, conditionValue, yesValue, noValue, isOne,
        outputValue]

theorem cached_hash_meaning (hash : Hash) (inputs witness : NativeRelation.Assignment)
    (state : Zkir.LowerState) (invariant : LowerStateMeaning hash witness state)
    (domain : Nat) (domainText left right result : String)
    (leftTerm rightTerm : Backend.Native.Term)
    (leftMeaning : OperandMeaning hash inputs witness left leftTerm)
    (rightMeaning : OperandMeaning hash inputs witness right rightTerm)
    (domainDecoded : decodeOperand (toJson domainText) = .ok (.immediate (scalar domain)))
    (hit : state.expressions.lookup ("transient_hash", [domainText, left, right], none) = some result) :
    OperandMeaning hash inputs witness result (.hash [.constant domain, leftTerm, rightTerm]) := by
  rcases leftMeaning with ⟨leftOperand, leftDecoded, leftValue⟩
  rcases rightMeaning with ⟨rightOperand, rightDecoded, rightValue⟩
  obtain ⟨instructions, decoded, instruction, member, correspondence⟩ :=
    invariant.cacheTrace _ result (ScalarValidationMeaning.lookup_member hit)
  cases instruction with
  | hash values output =>
    change result = output ∧
      ∃ (foundDomain : Nat) (foundDomainText a b : String) (foundLeft foundRight : Operand),
        ("transient_hash", [domainText, left, right], none) =
          ("transient_hash", [foundDomainText, a, b], none) ∧
        values = [.immediate (scalar foundDomain), foundLeft, foundRight] ∧
        decodeOperand (toJson foundDomainText) = .ok (.immediate (scalar foundDomain)) ∧
        decodeOperand (toJson a) = .ok foundLeft ∧
        decodeOperand (toJson b) = .ok foundRight ∧ validIdentifier output = true at correspondence
    rcases correspondence with ⟨resultEq, foundDomain, foundDomainText, a, b,
      foundLeft, foundRight, keyEq, valuesEq, foundDomainDecoded,
      foundLeftDecoded, foundRightDecoded, outputValid⟩
    subst result
    have textsEq : [domainText, left, right] = [foundDomainText, a, b] :=
      congrArg (fun key : ExpressionKey => key.2.1) keyEq
    rcases List.cons.inj textsEq with ⟨domainTextEq, restEq⟩
    rcases List.cons.inj restEq with ⟨leftTextEq, rightTextEq⟩
    have rightTextEqual : right = b := (List.cons.inj rightTextEq).1
    have decodedDomainAtSource : decodeOperand (toJson domainText) =
        .ok (.immediate (scalar foundDomain)) := by
      rw [domainTextEq]
      exact foundDomainDecoded
    have immediateDomainEq : Operand.immediate (scalar foundDomain) =
        Operand.immediate (scalar domain) :=
      Except.ok.inj (decodedDomainAtSource.symm.trans domainDecoded)
    have scalarDomainEq : scalar foundDomain = scalar domain :=
      Operand.immediate.inj immediateDomainEq
    have foundLeftDecodedAtSource : decodeOperand (toJson left) = .ok foundLeft := by
      rw [leftTextEq]
      exact foundLeftDecoded
    have foundRightDecodedAtSource : decodeOperand (toJson right) = .ok foundRight := by
      rw [rightTextEqual]
      exact foundRightDecoded
    have leftEq : foundLeft = leftOperand :=
      Except.ok.inj (foundLeftDecodedAtSource.symm.trans leftDecoded)
    have rightEq : foundRight = rightOperand :=
      Except.ok.inj (foundRightDecodedAtSource.symm.trans rightDecoded)
    have holds := invariant.holds instructions decoded (.hash values output) member
    rw [valuesEq, leftEq, rightEq] at holds
    refine ⟨.reference output, (OperandEncoding.reference output outputValid).decode, ?_⟩
    simp only [Operand.read]
    have outputMeaning : witness output =
        hash [scalar foundDomain, leftOperand.read witness, rightOperand.read witness] := by
      simpa [Instruction.Holds, Operand.read] using holds
    calc
      interpret hash inputs (.hash [.constant domain, leftTerm, rightTerm]) =
          some (hash [scalar foundDomain, leftOperand.read witness, rightOperand.read witness]) := by
        simp [interpret_hash, leftValue, rightValue, ← scalarDomainEq]
      _ = some (witness output) := congrArg some outputMeaning.symm
  | _ => simp [CacheCorresponds] at correspondence

end Noctium.Verification.ScalarCache
