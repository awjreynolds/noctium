import Noctium.Semantics
import Noctium.Verification.GenericStateExpressionChildren

namespace Noctium.Verification.GenericStateExpressionScope

open Noctium Noctium.Verification.GenericStateExpressionChildren

private def Agreements (ty : Ty) (expression : Expr ty) : Prop :=
  ∀ (caps : Capabilities) (types : TypeEnv) (ctx : EvalContext) (left right : EvalEnv),
    expression.validate caps types = .ok () →
    (∀ name ∈ types.map Prod.fst, left.lookup name = right.lookup name) →
    expression.eval ctx left = expression.eval ctx right

private theorem lookupNameMem (types : TypeEnv) (name : String) (ty : Ty)
    (lookup : types.lookup name = some ty) : name ∈ types.map Prod.fst := by
  obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp lookup
  rw [equal]
  simp

private theorem extendAgreement (types : TypeEnv) (left right : EvalEnv)
    (agreement : ∀ name ∈ types.map Prod.fst, left.lookup name = right.lookup name)
    (name : String) (source : Ty) (raw : Value) :
    ∀ found ∈ ((name, source) :: types).map Prod.fst,
      ((name, raw) :: left).lookup found = ((name, raw) :: right).lookup found := by
  intro found member
  simp only [List.map_cons] at member
  rcases List.mem_cons.mp member with same | inTypes
  · subst found
    simp
  · by_cases same : found = name
    · subst found
      simp
    · have unequal : (found == name) = false := by simp [same]
      simp only [List.lookup_cons, unequal]
      exact agreement found inTypes

private theorem supportsBytes32 (ty : Ty) :
    (((ty == .native) = true ∨ (ty == .jubjubScalar) = true) ∨
      (ty == .jubjubPoint) = true) ↔
      ty = .native ∨ ty = .jubjubScalar ∨ ty = .jubjubPoint := by
  cases ty <;> simp [BEq.beq, instBEqTy.beq]

private theorem supportsFromBytes (ty : Ty) :
    ((ty == .native) = true ∨ (ty == .jubjubScalar) = true) ↔
      ty = .native ∨ ty = .jubjubScalar := by
  cases ty <;> simp [BEq.beq, instBEqTy.beq]

private theorem foldlM_fixedList_congr {α β : Type}
    (leftStep rightStep : β → α → Except String β) (values : List α) (initial : β)
    (same : ∀ value ∈ values, ∀ state, leftStep state value = rightStep state value) :
    List.foldlM leftStep initial values = List.foldlM rightStep initial values := by
  induction values generalizing initial with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldlM_cons]
    rw [same head (by simp) initial]
    cases step : rightStep initial head with
    | error message => rfl
    | ok state =>
      simp only [step, bind, Except.bind]
      apply ih
      intro value member next
      exact same value (by simp [member]) next

private theorem forIn_fixedList_congr {α β : Type}
    (leftStep rightStep : α → β → Except String (ForInStep β)) (values : List α) (initial : β)
    (same : ∀ value ∈ values, ∀ state, leftStep value state = rightStep value state) :
    forIn values initial leftStep = forIn values initial rightStep := by
  induction values generalizing initial with
  | nil => rfl
  | cons head tail ih =>
    rw [List.forIn_cons, List.forIn_cons]
    rw [same head (by simp) initial]
    cases step : rightStep head initial with
    | error message => rfl
    | ok result =>
      cases result with
      | done state => rfl
      | yield state =>
        simp only [step, bind, Except.bind]
        apply ih
        intro value member next
        exact same value (by simp [member]) next

private theorem eval_agreements (ty : Ty) (expression : Expr ty) : Agreements ty expression := by
  apply Expr.rec (motive_1 := Agreements)
    (motive_2 := fun values => ∀ expression ∈ values, Agreements _ expression)
    (motive_3 := fun values => ∀ expression ∈ values, Agreements _ expression)
    (motive_4 := fun values => ∀ expression ∈ values, Agreements expression.1 expression.2)
    (motive_5 := fun expression => Agreements expression.1 expression.2)
  case ref =>
    intro ty name caps types ctx left right valid agreement
    have found : ∃ foundTy, types.lookup name = some foundTy := by
      cases checkedType : ty.validate caps with
      | error message => simp [Expr.validate, checkedType, bind, Except.bind] at valid
      | ok checked =>
        cases lookup : types.lookup name with
        | none => simp [Expr.validate, checkedType, lookup, bind, Except.bind] at valid
        | some foundTy => exact ⟨foundTy, rfl⟩
    obtain ⟨foundTy, lookup⟩ := found
    have member := lookupNameMem types name foundTy lookup
    simp [Expr.eval, agreement name member]
  case letE =>
    intro source ty name value body ihValue ihBody caps types ctx left right valid agreement
    simp only [Expr.validate] at valid
    cases valueValid : value.validate caps types with
    | error message => simp [valueValid, Bind.bind, Except.bind] at valid
    | ok checked =>
      cases checked
      have bodyValid : body.validate caps ((name, source) :: types) = .ok () := by
        simpa [valueValid, Bind.bind, Except.bind] using valid
      have valueEqual := ihValue caps types ctx left right valueValid agreement
      simp only [Expr.eval]
      rw [valueEqual]
      cases evaluated : value.eval ctx right with
      | error message => simp [bind, Except.bind]
      | ok raw =>
        simp only [bind, Except.bind]
        exact ihBody caps ((name, source) :: types) ctx
          ((name, Value.pack source raw) :: left)
          ((name, Value.pack source raw) :: right) bodyValid
          (extendAgreement types left right agreement name source (Value.pack source raw))
  case add =>
    intro a b ihA ihB caps types ctx left right valid agreement
    cases supported : caps.nativeArithmetic
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · cases first : a.validate caps types with
      | error message => simp [Expr.validate, supported, first, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        have second : b.validate caps types = .ok () := by
          simpa [Expr.validate, supported, first, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ihA caps types ctx left right first agreement,
          ihB caps types ctx left right second agreement]
  case mul =>
    intro a b ihA ihB caps types ctx left right valid agreement
    cases supported : caps.nativeArithmetic
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · cases first : a.validate caps types with
      | error message => simp [Expr.validate, supported, first, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        have second : b.validate caps types = .ok () := by
          simpa [Expr.validate, supported, first, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ihA caps types ctx left right first agreement,
          ihB caps types ctx left right second agreement]
  case sub =>
    intro a b ihA ihB caps types ctx left right valid agreement
    cases supported : caps.nativeArithmetic
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · cases first : a.validate caps types with
      | error message => simp [Expr.validate, supported, first, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        have second : b.validate caps types = .ok () := by
          simpa [Expr.validate, supported, first, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ihA caps types ctx left right first agreement,
          ihB caps types ctx left right second agreement]
  case boolAnd =>
    intro a b ihA ihB caps types ctx left right valid agreement
    cases supported : caps.typedBoolean
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · cases first : a.validate caps types with
      | error message => simp [Expr.validate, supported, first, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        have second : b.validate caps types = .ok () := by
          simpa [Expr.validate, supported, first, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ihA caps types ctx left right first agreement,
          ihB caps types ctx left right second agreement]
  case boolOr =>
    intro a b ihA ihB caps types ctx left right valid agreement
    cases supported : caps.typedBoolean
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · cases first : a.validate caps types with
      | error message => simp [Expr.validate, supported, first, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        have second : b.validate caps types = .ok () := by
          simpa [Expr.validate, supported, first, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ihA caps types ctx left right first agreement,
          ihB caps types ctx left right second agreement]
  case boolXor =>
    intro a b ihA ihB caps types ctx left right valid agreement
    cases supported : caps.typedBoolean
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · cases first : a.validate caps types with
      | error message => simp [Expr.validate, supported, first, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        have second : b.validate caps types = .ok () := by
          simpa [Expr.validate, supported, first, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ihA caps types ctx left right first agreement,
          ihB caps types ctx left right second agreement]
  case jubjubAdd =>
    intro a b ihA ihB caps types ctx left right valid agreement
    cases supported : caps.jubjub
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · cases first : a.validate caps types with
      | error message => simp [Expr.validate, supported, first, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        have second : b.validate caps types = .ok () := by
          simpa [Expr.validate, supported, first, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ihA caps types ctx left right first agreement,
          ihB caps types ctx left right second agreement]
  case jubjubNeg =>
    intro a ih caps types ctx left right valid agreement
    cases supported : caps.jubjub
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · have accepted : a.validate caps types = .ok () := by
        simpa [Expr.validate, supported] using valid
      simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case opaqueBytesProjection =>
    intro a ih caps types ctx left right valid agreement
    have accepted : a.validate caps types = .ok () := by
      simpa only [Expr.validate] using valid
    simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case opaqueStringProjection =>
    intro a ih caps types ctx left right valid agreement
    have accepted : a.validate caps types = .ok () := by
      simpa only [Expr.validate] using valid
    simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case copyValue =>
    intro ty a ih caps types ctx left right valid agreement
    have accepted : a.validate caps types = .ok () := by
      simpa only [Expr.validate] using valid
    simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case disclose =>
    intro ty span a ih caps types ctx left right valid agreement
    have accepted : a.validate caps types = .ok () := by
      simpa only [Expr.validate] using valid
    simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case bytesField =>
    intro length a index ih caps types ctx left right valid agreement
    cases accepted : a.validate caps types with
    | error message => simp [Expr.validate, accepted, Bind.bind, Except.bind] at valid
    | ok checked =>
      cases checked
      simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case bytesAt =>
    intro length a index ih caps types ctx left right valid agreement
    cases accepted : a.validate caps types with
    | error message => simp [Expr.validate, accepted, Bind.bind, Except.bind] at valid
    | ok checked =>
      cases checked
      simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case reverseBytes32 =>
    intro a ih caps types ctx left right valid agreement
    cases supported : caps.bytes32Conversions
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · have accepted : a.validate caps types = .ok () := by
        simpa [Expr.validate, supported] using valid
      simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case persistentHash32 =>
    intro a ih caps types ctx left right valid agreement
    cases supported : caps.persistentHash32
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · have accepted : a.validate caps types = .ok () := by
        simpa [Expr.validate, supported] using valid
      simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case persistentHashNative =>
    intro a ih caps types ctx left right valid agreement
    cases supported : caps.persistentHashNative
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · have accepted : a.validate caps types = .ok () := by
        simpa [Expr.validate, supported] using valid
      simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case keccak256Secp256k1Point =>
    intro a ih caps types ctx left right valid agreement
    cases supported : caps.keccak256
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · have accepted : a.validate caps types = .ok () := by
        simpa [Expr.validate, supported] using valid
      simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case jubjubScalarFromNative =>
    intro a ih caps types ctx left right valid agreement
    cases supported : caps.jubjub
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · have accepted : a.validate caps types = .ok () := by
        simpa [Expr.validate, supported] using valid
      simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case jubjubScalarToNative =>
    intro a ih caps types ctx left right valid agreement
    cases supported : caps.jubjub
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · have accepted : a.validate caps types = .ok () := by
        simpa [Expr.validate, supported] using valid
      simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case jubjubMulGenerator =>
    intro a ih caps types ctx left right valid agreement
    cases supported : caps.jubjub
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · have accepted : a.validate caps types = .ok () := by
        simpa [Expr.validate, supported] using valid
      simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case jubjubMul =>
    intro a b ihA ihB caps types ctx left right valid agreement
    cases supported : caps.jubjub
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · cases first : a.validate caps types with
      | error message => simp [Expr.validate, supported, first, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        have second : b.validate caps types = .ok () := by
          simpa [Expr.validate, supported, first, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ihA caps types ctx left right first agreement,
          ihB caps types ctx left right second agreement]
  case jubjubFromCoordinates =>
    intro a b ihA ihB caps types ctx left right valid agreement
    cases supported : caps.jubjub
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw, MonadExceptOf.throw] at valid
    · cases first : a.validate caps types with
      | error message => simp [Expr.validate, supported, first, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        have second : b.validate caps types = .ok () := by
          simpa [Expr.validate, supported, first, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ihA caps types ctx left right first agreement,
          ihB caps types ctx left right second agreement]
  case reverseBytes =>
    intro length value ih caps types ctx left right valid agreement
    cases supported : caps.bytes32Conversions
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · have lengthOk : length ≤ maxByteOperationLength := by
        by_cases bound : length ≤ maxByteOperationLength
        · exact bound
        · simp [Expr.validate, supported, bound, Bind.bind, Except.bind, throw] at valid
      cases child : value.validate caps types with
      | error message => simp [Expr.validate, supported, lengthOk, child, Bind.bind, Except.bind] at valid
      | ok checked =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, lengthOk, child, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case sliceBytes =>
    intro length value start stop ih caps types ctx left right valid agreement
    cases supported : caps.bytes32Conversions
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · have lengthOk : length ≤ maxByteOperationLength := by
        by_cases bound : length ≤ maxByteOperationLength
        · exact bound
        · simp [Expr.validate, supported, bound, Bind.bind, Except.bind, throw] at valid
      have startOk : start ≤ stop := by
        by_cases bound : start ≤ stop
        · exact bound
        · simp [Expr.validate, supported, lengthOk, bound, Bind.bind, Except.bind, throw] at valid
      have stopOk : stop ≤ length := by
        by_cases bound : stop ≤ length
        · exact bound
        · simp [Expr.validate, supported, lengthOk, startOk, bound, Bind.bind, Except.bind, throw] at valid
      cases child : value.validate caps types with
      | error message => simp [Expr.validate, supported, lengthOk, startOk, stopOk, child, Bind.bind, Except.bind] at valid
      | ok checked =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, lengthOk, startOk, stopOk, child, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case concatBytes =>
    intro leftLength rightLength left right ihLeft ihRight caps types ctx leftEnv rightEnv valid agreement
    cases supported : caps.bytes32Conversions
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · have lengthOk : leftLength + rightLength ≤ maxByteOperationLength := by
        by_cases bound : leftLength + rightLength ≤ maxByteOperationLength
        · exact bound
        · simp [Expr.validate, supported, bound, Bind.bind, Except.bind, throw] at valid
      cases first : left.validate caps types with
      | error message => simp [Expr.validate, supported, lengthOk, first, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        cases second : right.validate caps types with
        | error message => simp [Expr.validate, supported, lengthOk, first, second, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          have acceptedLeft : left.validate caps types = .ok () := first
          have acceptedRight : right.validate caps types = .ok () := by
            simpa [Expr.validate, supported, lengthOk, first, Bind.bind, Except.bind] using valid
          simp [Expr.eval, ihLeft caps types ctx leftEnv rightEnv acceptedLeft agreement,
            ihRight caps types ctx leftEnv rightEnv acceptedRight agreement]
  case sha256 =>
    intro length value ih caps types ctx left right valid agreement
    cases supported : caps.persistentHash32
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · have lengthOk : length ≤ maxByteOperationLength := by
        by_cases bound : length ≤ maxByteOperationLength
        · exact bound
        · simp [Expr.validate, supported, bound, Bind.bind, Except.bind, throw] at valid
      cases typeValid : (Ty.bytes length).validate caps with
      | error message => simp [Expr.validate, supported, lengthOk, typeValid, Bind.bind, Except.bind] at valid
      | ok typeChecked =>
        cases child : value.validate caps types with
        | error message => simp [Expr.validate, supported, lengthOk, typeValid, child, Bind.bind, Except.bind] at valid
        | ok checked =>
          have accepted : value.validate caps types = .ok () := child
          simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case sha512 =>
    intro length value ih caps types ctx left right valid agreement
    cases supported : caps.sha512
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · have lengthOk : length ≤ maxByteOperationLength := by
        by_cases bound : length ≤ maxByteOperationLength
        · exact bound
        · simp [Expr.validate, supported, bound, Bind.bind, Except.bind, throw] at valid
      cases child : value.validate caps types with
      | error message => simp [Expr.validate, supported, lengthOk, child, Bind.bind, Except.bind] at valid
      | ok checked =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, lengthOk, child, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case keccak256 =>
    intro length value ih caps types ctx left right valid agreement
    cases supported : caps.keccak256
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · have lengthOk : length ≤ maxByteOperationLength := by
        by_cases bound : length ≤ maxByteOperationLength
        · exact bound
        · simp [Expr.validate, supported, bound, Bind.bind, Except.bind, throw] at valid
      cases child : value.validate caps types with
      | error message => simp [Expr.validate, supported, lengthOk, child, Bind.bind, Except.bind] at valid
      | ok checked =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, lengthOk, child, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case toBytes32 =>
    intro source value ih caps types ctx left right valid agreement
    cases supported : caps.bytes32Conversions
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases source with
      | native =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind] using valid
        have equal := ih caps types ctx left right accepted agreement
        simp [Expr.eval, equal]
      | jubjubScalar =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind] using valid
        have equal := ih caps types ctx left right accepted agreement
        simp [Expr.eval, equal]
      | jubjubPoint =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind] using valid
        have equal := ih caps types ctx left right accepted agreement
        simp [Expr.eval, equal]
      | bool => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | uint maximum => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | bytes length => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | opaqueBytes => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | opaqueString => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | foreign kind => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
  case fromBytes32 =>
    intro target value ih caps types ctx left right valid agreement
    cases supported : caps.bytes32Conversions
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases target with
      | native =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind] using valid
        have equal := ih caps types ctx left right accepted agreement
        simp [Expr.eval, equal]
      | jubjubScalar =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind] using valid
        have equal := ih caps types ctx left right accepted agreement
        simp [Expr.eval, equal]
      | jubjubPoint =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind] using valid
        have equal := ih caps types ctx left right accepted agreement
        simp [Expr.eval, equal]
      | bool => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | uint maximum => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | bytes length => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | opaqueBytes => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | opaqueString => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | foreign kind => simp [Expr.validate, supported, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
  case fromBytes =>
    intro target length value ih caps types ctx left right valid agreement
    cases target with
      | native =>
        have lengthOk : length ≤ maxByteOperationLength := by
          by_cases bound : length ≤ maxByteOperationLength
          · exact bound
          · simp [Expr.validate, BEq.beq, instBEqTy.beq, bound, Bind.bind, Except.bind, throw] at valid
        cases typeValid : Ty.native.validate caps with
        | error message => simp [Expr.validate, BEq.beq, instBEqTy.beq, lengthOk, typeValid, Bind.bind, Except.bind] at valid
        | ok checked =>
          have accepted : value.validate caps types = .ok () := by
            simpa [Expr.validate, BEq.beq, instBEqTy.beq, lengthOk, typeValid, Bind.bind, Except.bind] using valid
          have equal := ih caps types ctx left right accepted agreement
          simp [Expr.eval, equal]
      | jubjubScalar =>
        have lengthOk : length ≤ maxByteOperationLength := by
          by_cases bound : length ≤ maxByteOperationLength
          · exact bound
          · simp [Expr.validate, BEq.beq, instBEqTy.beq, bound, Bind.bind, Except.bind, throw] at valid
        cases typeValid : Ty.jubjubScalar.validate caps with
        | error message => simp [Expr.validate, BEq.beq, instBEqTy.beq, lengthOk, typeValid, Bind.bind, Except.bind] at valid
        | ok checked =>
          have accepted : value.validate caps types = .ok () := by
            simpa [Expr.validate, BEq.beq, instBEqTy.beq, lengthOk, typeValid, Bind.bind, Except.bind] using valid
          have equal := ih caps types ctx left right accepted agreement
          simp [Expr.eval, equal]
      | bool => simp [Expr.validate, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | uint maximum => simp [Expr.validate, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | bytes bytesLength => simp [Expr.validate, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | opaqueBytes => simp [Expr.validate, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | opaqueString => simp [Expr.validate, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | jubjubPoint => simp [Expr.validate, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
      | foreign kind => simp [Expr.validate, BEq.beq, instBEqTy.beq, Bind.bind, Except.bind, throw] at valid
  case jubjubCoordinate =>
    intro point index ih caps types ctx left right valid agreement
    cases supported : caps.jubjub
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases child : point.validate caps types with
      | error message => simp [Expr.validate, supported, child, Bind.bind, Except.bind] at valid
      | ok checked =>
        have accepted : point.validate caps types = .ok () := by
          simpa [Expr.validate, supported, child, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case foreignEncodedField =>
    intro kind value index ih caps types ctx left right valid agreement
    cases supported : caps.foreignValues
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases child : value.validate caps types with
      | error message => simp [Expr.validate, supported, child, Bind.bind, Except.bind] at valid
      | ok checked =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, child, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case foreignUnary =>
    intro operation value ih caps types ctx left right valid agreement
    cases supported : caps.foreignArithmetic
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases inputValid : (Ty.foreign operation.inputKind).validate caps with
      | error message => simp [Expr.validate, supported, inputValid, Bind.bind, Except.bind] at valid
      | ok inputChecked =>
        cases outputValid : (Ty.foreign operation.outputKind).validate caps with
        | error message => simp [Expr.validate, supported, inputValid, outputValid, Bind.bind, Except.bind] at valid
        | ok outputChecked =>
          cases child : value.validate caps types with
          | error message => simp [Expr.validate, supported, inputValid, outputValid, child, Bind.bind, Except.bind] at valid
          | ok checked =>
            have accepted : value.validate caps types = .ok () := child
            have equal := ih caps types ctx left right accepted agreement
            simp [Expr.eval, equal]
  case foreignBinary =>
    intro operation leftExpr rightExpr ihLeft ihRight caps types ctx left right valid agreement
    cases supported : caps.foreignArithmetic
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases leftTypeValid : (Ty.foreign operation.leftKind).validate caps with
      | error message => simp [Expr.validate, supported, leftTypeValid, Bind.bind, Except.bind] at valid
      | ok leftTypeChecked =>
        cases rightTypeValid : (Ty.foreign operation.rightKind).validate caps with
        | error message => simp [Expr.validate, supported, leftTypeValid, rightTypeValid, Bind.bind, Except.bind] at valid
        | ok rightTypeChecked =>
          cases outputTypeValid : (Ty.foreign operation.outputKind).validate caps with
          | error message => simp [Expr.validate, supported, leftTypeValid, rightTypeValid, outputTypeValid, Bind.bind, Except.bind] at valid
          | ok outputTypeChecked =>
            cases first : leftExpr.validate caps types with
            | error message => simp [Expr.validate, supported, leftTypeValid, rightTypeValid, outputTypeValid, first, Bind.bind, Except.bind] at valid
            | ok checked =>
              cases checked
              cases second : rightExpr.validate caps types with
              | error message => simp [Expr.validate, supported, leftTypeValid, rightTypeValid, outputTypeValid, first, second, Bind.bind, Except.bind] at valid
              | ok checked =>
                cases checked
                have acceptedLeft : leftExpr.validate caps types = .ok () := first
                have acceptedRight : rightExpr.validate caps types = .ok () := by
                  simpa [Expr.validate, supported, leftTypeValid, rightTypeValid, outputTypeValid, first, Bind.bind, Except.bind] using valid
                simp [Expr.eval, ihLeft caps types ctx left right acceptedLeft agreement,
                  ihRight caps types ctx left right acceptedRight agreement]
  case foreignToBytes =>
    intro kind value ih caps types ctx left right valid agreement
    cases supported : caps.foreignByteConversions
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases child : value.validate caps types with
      | error message => simp [Expr.validate, supported, child, Bind.bind, Except.bind] at valid
      | ok checked =>
        have accepted : value.validate caps types = .ok () := by
          simpa [Expr.validate, supported, child, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ih caps types ctx left right accepted agreement]
  case foreignFromBytes =>
    intro kind length value ih caps types ctx left right valid agreement
    cases supported : caps.foreignByteConversions
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases typeValid : (Ty.foreign kind).validate caps with
      | error message => simp [Expr.validate, supported, typeValid, Bind.bind, Except.bind] at valid
      | ok typeChecked =>
        have lengthOk : length ≤ maxByteOperationLength := by
          by_cases bound : length ≤ maxByteOperationLength
          · exact bound
          · simp [Expr.validate, supported, typeValid, bound, Bind.bind, Except.bind, throw] at valid
        cases pointEncoding : kind.byteLength == 33 with
        | false =>
          cases child : value.validate caps types with
          | error message => simp [Expr.validate, supported, typeValid, lengthOk, pointEncoding, child, Bind.bind, Except.bind] at valid
          | ok checked =>
            have accepted : value.validate caps types = .ok () := by
              simpa [Expr.validate, supported, typeValid, lengthOk, pointEncoding, child, Bind.bind, Except.bind] using valid
            simp [Expr.eval, ih caps types ctx left right accepted agreement]
        | true =>
          by_cases exactLength : length = 33
          · have exactBound : 33 ≤ maxByteOperationLength := by simpa [exactLength] using lengthOk
            cases child : value.validate caps types with
            | error message => simp [Expr.validate, supported, typeValid, lengthOk, exactBound, pointEncoding, exactLength, child, Bind.bind, Except.bind] at valid
            | ok checked =>
              have accepted : value.validate caps types = .ok () := by
                simpa [Expr.validate, supported, typeValid, lengthOk, exactBound, pointEncoding, exactLength, child, Bind.bind, Except.bind] using valid
              simp [Expr.eval, ih caps types ctx left right accepted agreement]
          · simp [Expr.validate, supported, typeValid, lengthOk, pointEncoding, exactLength, Bind.bind, Except.bind, throw] at valid
  case uadd =>
    intro m n a b ihA ihB caps types ctx left right valid agreement
    cases resultValid : (Ty.uint (m + n)).validate caps with
    | error message => simp [Expr.validate, resultValid, Bind.bind, Except.bind] at valid
    | ok resultChecked =>
      cases supported : caps.nativeArithmetic
      · simp [Expr.validate, resultValid, supported, Bind.bind, Except.bind, throw] at valid
      · cases first : a.validate caps types with
        | error message => simp [Expr.validate, resultValid, supported, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : b.validate caps types with
          | error message => simp [Expr.validate, resultValid, supported, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            have acceptedA : a.validate caps types = .ok () := first
            have acceptedB : b.validate caps types = .ok () := by
              simpa [Expr.validate, resultValid, supported, first, Bind.bind, Except.bind] using valid
            simp [Expr.eval, ihA caps types ctx left right acceptedA agreement,
              ihB caps types ctx left right acceptedB agreement]

  case usub =>
    intro m n a b ihA ihB caps types ctx left right valid agreement
    cases resultValid : (Ty.uint (m)).validate caps with
    | error message => simp [Expr.validate, resultValid, Bind.bind, Except.bind] at valid
    | ok resultChecked =>
      cases supported : caps.nativeArithmetic
      · simp [Expr.validate, resultValid, supported, Bind.bind, Except.bind, throw] at valid
      · cases first : a.validate caps types with
        | error message => simp [Expr.validate, resultValid, supported, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : b.validate caps types with
          | error message => simp [Expr.validate, resultValid, supported, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            have acceptedA : a.validate caps types = .ok () := first
            have acceptedB : b.validate caps types = .ok () := by
              simpa [Expr.validate, resultValid, supported, first, Bind.bind, Except.bind] using valid
            simp [Expr.eval, ihA caps types ctx left right acceptedA agreement,
              ihB caps types ctx left right acceptedB agreement]

  case umul =>
    intro m n a b ihA ihB caps types ctx left right valid agreement
    cases resultValid : (Ty.uint (m * n)).validate caps with
    | error message => simp [Expr.validate, resultValid, Bind.bind, Except.bind] at valid
    | ok resultChecked =>
      cases supported : caps.nativeArithmetic
      · simp [Expr.validate, resultValid, supported, Bind.bind, Except.bind, throw] at valid
      · cases first : a.validate caps types with
        | error message => simp [Expr.validate, resultValid, supported, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : b.validate caps types with
          | error message => simp [Expr.validate, resultValid, supported, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            have acceptedA : a.validate caps types = .ok () := first
            have acceptedB : b.validate caps types = .ok () := by
              simpa [Expr.validate, resultValid, supported, first, Bind.bind, Except.bind] using valid
            simp [Expr.eval, ihA caps types ctx left right acceptedA agreement,
              ihB caps types ctx left right acceptedB agreement]
  case inv =>
    intro ty value ih caps types ctx left right valid agreement
    cases ty with
    | native =>
      cases supported : caps.nativeArithmetic
      · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
      · cases child : value.validate caps types with
        | error message => simp [Expr.validate, supported, child, Bind.bind, Except.bind] at valid
        | ok checked =>
          have accepted : value.validate caps types = .ok () := child
          have equal := ih caps types ctx left right accepted agreement
          simp [Expr.eval, equal]
    | jubjubScalar =>
      cases supported : caps.jubjub
      · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
      · cases child : value.validate caps types with
        | error message => simp [Expr.validate, supported, child, Bind.bind, Except.bind] at valid
        | ok checked =>
          have accepted : value.validate caps types = .ok () := child
          have equal := ih caps types ctx left right accepted agreement
          simp [Expr.eval, equal]
    | bool => simp [Expr.validate, Bind.bind, Except.bind, throw] at valid
    | uint maximum => simp [Expr.validate, Bind.bind, Except.bind, throw] at valid
    | bytes length => simp [Expr.validate, Bind.bind, Except.bind, throw] at valid
    | opaqueBytes => simp [Expr.validate, Bind.bind, Except.bind, throw] at valid
    | opaqueString => simp [Expr.validate, Bind.bind, Except.bind, throw] at valid
    | jubjubPoint => simp [Expr.validate, Bind.bind, Except.bind, throw] at valid
    | foreign kind => simp [Expr.validate, Bind.bind, Except.bind, throw] at valid
  case cast =>
    intro source target value ih caps types ctx left right valid agreement
    cases source with
    | native =>
      cases target with
      | native =>
        cases targetValid : Ty.native.validate caps with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, Bind.bind, Except.bind] at valid
        | ok targetChecked =>
          cases child : value.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, child, Bind.bind, Except.bind] at valid
          | ok checked =>
            have accepted : value.validate caps types = .ok () := child
            have equal := ih caps types ctx left right accepted agreement
            simp [Expr.eval, equal]
      | bool =>
        cases targetValid : Ty.bool.validate caps with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, Bind.bind, Except.bind] at valid
        | ok targetChecked =>
          cases child : value.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, child, Bind.bind, Except.bind] at valid
          | ok checked =>
            have accepted : value.validate caps types = .ok () := child
            have equal := ih caps types ctx left right accepted agreement
            simp [Expr.eval, equal]
      | uint targetMax =>
        cases targetValid : (Ty.uint targetMax).validate caps with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, Bind.bind, Except.bind] at valid
        | ok targetChecked =>
          cases child : value.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, child, Bind.bind, Except.bind] at valid
          | ok checked =>
            have accepted : value.validate caps types = .ok () := child
            have equal := ih caps types ctx left right accepted agreement
            simp [Expr.eval, equal]
      | bytes length => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | opaqueBytes => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | opaqueString => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | jubjubScalar => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | jubjubPoint => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | foreign kind => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
    | bool =>
      cases target with
      | native =>
        cases targetValid : Ty.native.validate caps with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, Bind.bind, Except.bind] at valid
        | ok targetChecked =>
          cases child : value.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, child, Bind.bind, Except.bind] at valid
          | ok checked =>
            have accepted : value.validate caps types = .ok () := child
            have equal := ih caps types ctx left right accepted agreement
            simp [Expr.eval, equal]
      | bool =>
        cases targetValid : Ty.bool.validate caps with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, Bind.bind, Except.bind] at valid
        | ok targetChecked =>
          cases child : value.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, child, Bind.bind, Except.bind] at valid
          | ok checked =>
            have accepted : value.validate caps types = .ok () := child
            have equal := ih caps types ctx left right accepted agreement
            simp [Expr.eval, equal]
      | uint targetMax =>
        cases targetValid : (Ty.uint targetMax).validate caps with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, Bind.bind, Except.bind] at valid
        | ok targetChecked =>
          cases child : value.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, child, Bind.bind, Except.bind] at valid
          | ok checked =>
            have accepted : value.validate caps types = .ok () := child
            have equal := ih caps types ctx left right accepted agreement
            simp [Expr.eval, equal]
      | bytes length => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | opaqueBytes => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | opaqueString => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | jubjubScalar => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | jubjubPoint => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | foreign kind => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
    | uint sourceMax =>
      cases target with
      | native =>
        cases targetValid : Ty.native.validate caps with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, Bind.bind, Except.bind] at valid
        | ok targetChecked =>
          cases child : value.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, child, Bind.bind, Except.bind] at valid
          | ok checked =>
            have accepted : value.validate caps types = .ok () := child
            have equal := ih caps types ctx left right accepted agreement
            simp [Expr.eval, equal]
      | bool =>
        cases targetValid : Ty.bool.validate caps with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, Bind.bind, Except.bind] at valid
        | ok targetChecked =>
          cases child : value.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, child, Bind.bind, Except.bind] at valid
          | ok checked =>
            have accepted : value.validate caps types = .ok () := child
            have equal := ih caps types ctx left right accepted agreement
            simp [Expr.eval, equal]
      | uint targetMax =>
        cases targetValid : (Ty.uint targetMax).validate caps with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, Bind.bind, Except.bind] at valid
        | ok targetChecked =>
          cases child : value.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, targetValid, child, Bind.bind, Except.bind] at valid
          | ok checked =>
            have accepted : value.validate caps types = .ok () := child
            have equal := ih caps types ctx left right accepted agreement
            simp [Expr.eval, equal]
      | bytes length => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | opaqueBytes => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | opaqueString => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | jubjubScalar => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | jubjubPoint => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
      | foreign kind => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
    | bytes length =>
      cases target <;> simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
    | opaqueBytes =>
      cases target <;> simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
    | opaqueString =>
      cases target <;> simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
    | jubjubScalar =>
      cases target <;> simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
    | jubjubPoint =>
      cases target <;> simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
    | foreign kind =>
      cases target <;> simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
  case assertE =>
    intro ty condition body ihCondition ihBody caps types ctx left right valid agreement
    cases first : condition.validate caps types with
    | error message => simp [Expr.validate, first, Bind.bind, Except.bind] at valid
    | ok checked =>
      cases checked
      cases second : body.validate caps types with
      | error message => simp [Expr.validate, first, second, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        have acceptedCondition : condition.validate caps types = .ok () := first
        have acceptedBody : body.validate caps types = .ok () := by
          simpa [Expr.validate, first, Bind.bind, Except.bind] using valid
        simp [Expr.eval, ihCondition caps types ctx left right acceptedCondition agreement,
          ihBody caps types ctx left right acceptedBody agreement]
  case eq =>
    intro ty a b ihA ihB caps types ctx left right valid agreement
    cases ty with
    | native =>
      cases supported : caps.equality
      · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, Bind.bind, Except.bind, throw] at valid
      · cases first : a.validate caps types with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : b.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            have acceptedA : a.validate caps types = .ok () := first
            have acceptedB : b.validate caps types = .ok () := by
              simpa [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] using valid
            simp [Expr.eval, ihA caps types ctx left right acceptedA agreement,
              ihB caps types ctx left right acceptedB agreement]
    | bool =>
      cases supported : caps.equality
      · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, Bind.bind, Except.bind, throw] at valid
      · cases first : a.validate caps types with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : b.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            have acceptedA : a.validate caps types = .ok () := first
            have acceptedB : b.validate caps types = .ok () := by
              simpa [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] using valid
            simp [Expr.eval, ihA caps types ctx left right acceptedA agreement,
              ihB caps types ctx left right acceptedB agreement]
    | uint maximum =>
      cases supported : caps.equality
      · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, Bind.bind, Except.bind, throw] at valid
      · cases first : a.validate caps types with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : b.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            have acceptedA : a.validate caps types = .ok () := first
            have acceptedB : b.validate caps types = .ok () := by
              simpa [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] using valid
            simp [Expr.eval, ihA caps types ctx left right acceptedA agreement,
              ihB caps types ctx left right acceptedB agreement]
    | jubjubScalar =>
      cases supported : caps.equality
      · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, Bind.bind, Except.bind, throw] at valid
      · cases first : a.validate caps types with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : b.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            have acceptedA : a.validate caps types = .ok () := first
            have acceptedB : b.validate caps types = .ok () := by
              simpa [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] using valid
            simp [Expr.eval, ihA caps types ctx left right acceptedA agreement,
              ihB caps types ctx left right acceptedB agreement]
    | jubjubPoint =>
      cases supported : caps.equality
      · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, Bind.bind, Except.bind, throw] at valid
      · cases first : a.validate caps types with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : b.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            have acceptedA : a.validate caps types = .ok () := first
            have acceptedB : b.validate caps types = .ok () := by
              simpa [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] using valid
            simp [Expr.eval, ihA caps types ctx left right acceptedA agreement,
              ihB caps types ctx left right acceptedB agreement]
    | foreign kind =>
      cases supported : caps.equality
      · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, Bind.bind, Except.bind, throw] at valid
      · cases first : a.validate caps types with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : b.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            have acceptedA : a.validate caps types = .ok () := first
            have acceptedB : b.validate caps types = .ok () := by
              simpa [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, supported, first, Bind.bind, Except.bind] using valid
            simp [Expr.eval, ihA caps types ctx left right acceptedA agreement,
              ihB caps types ctx left right acceptedB agreement]
    | bytes length => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Bind.bind, Except.bind, throw] at valid
    | opaqueBytes | opaqueString =>
      cases supported : caps.equality
      · simp [Expr.validate, Ty.isBytes, supported, Bind.bind, Except.bind,
          throw] at valid
      · cases first : a.validate caps types with
        | error message =>
          simp [Expr.validate, Ty.isBytes, supported, first, Bind.bind,
            Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : b.validate caps types with
          | error message =>
            simp [Expr.validate, Ty.isBytes, supported, first, second,
              Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            have acceptedA : a.validate caps types = .ok () := first
            have acceptedB : b.validate caps types = .ok () := by
              simpa [Expr.validate, Ty.isBytes, supported, first,
                Bind.bind, Except.bind] using valid
            simp [Expr.eval, ihA caps types ctx left right acceptedA agreement,
              ihB caps types ctx left right acceptedB agreement]
  case select =>
    intro ty condition yes no ihCondition ihYes ihNo caps types ctx left right valid agreement
    cases ty with
    | native =>
      cases selectCap : caps.select
      · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, Bind.bind, Except.bind, throw] at valid
      · cases first : condition.validate caps types with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : yes.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            cases third : no.validate caps types with
            | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, first, second, third, Bind.bind, Except.bind] at valid
            | ok checked =>
              cases checked
              have acceptedCondition : condition.validate caps types = .ok () := first
              have acceptedYes : yes.validate caps types = .ok () := second
              have acceptedNo : no.validate caps types = .ok () := third
              simp [Expr.eval, ihCondition caps types ctx left right acceptedCondition agreement,
                ihYes caps types ctx left right acceptedYes agreement,
                ihNo caps types ctx left right acceptedNo agreement]
    | bool =>
      cases selectCap : caps.select
      · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, Bind.bind, Except.bind, throw] at valid
      · cases first : condition.validate caps types with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : yes.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            cases third : no.validate caps types with
            | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, first, second, third, Bind.bind, Except.bind] at valid
            | ok checked =>
              cases checked
              have acceptedCondition : condition.validate caps types = .ok () := first
              have acceptedYes : yes.validate caps types = .ok () := second
              have acceptedNo : no.validate caps types = .ok () := third
              simp [Expr.eval, ihCondition caps types ctx left right acceptedCondition agreement,
                ihYes caps types ctx left right acceptedYes agreement,
                ihNo caps types ctx left right acceptedNo agreement]
    | uint maximum =>
      cases selectCap : caps.select
      · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, Bind.bind, Except.bind, throw] at valid
      · cases first : condition.validate caps types with
        | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : yes.validate caps types with
          | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            cases third : no.validate caps types with
            | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, selectCap, first, second, third, Bind.bind, Except.bind] at valid
            | ok checked =>
              cases checked
              have acceptedCondition : condition.validate caps types = .ok () := first
              have acceptedYes : yes.validate caps types = .ok () := second
              have acceptedNo : no.validate caps types = .ok () := third
              simp [Expr.eval, ihCondition caps types ctx left right acceptedCondition agreement,
                ihYes caps types ctx left right acceptedYes agreement,
                ihNo caps types ctx left right acceptedNo agreement]
    | bytes length =>
      cases bytesSupported : caps.bytes32Conversions
      · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, bytesSupported, Bind.bind, Except.bind, throw] at valid
      · cases selectCap : caps.select
        · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, bytesSupported, selectCap, Bind.bind, Except.bind, throw] at valid
        · cases first : condition.validate caps types with
            | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, bytesSupported, selectCap, first, Bind.bind, Except.bind] at valid
            | ok checked =>
              cases checked
              cases second : yes.validate caps types with
              | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, bytesSupported, selectCap, first, second, Bind.bind, Except.bind] at valid
              | ok checked =>
                cases checked
                cases third : no.validate caps types with
                | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, bytesSupported, selectCap, first, second, third, Bind.bind, Except.bind] at valid
                | ok checked =>
                  cases checked
                  have acceptedCondition : condition.validate caps types = .ok () := first
                  have acceptedYes : yes.validate caps types = .ok () := second
                  have acceptedNo : no.validate caps types = .ok () := third
                  simp [Expr.eval, ihCondition caps types ctx left right acceptedCondition agreement,
                    ihYes caps types ctx left right acceptedYes agreement,
                    ihNo caps types ctx left right acceptedNo agreement]
    | foreign kind =>
      cases foreignSupported : caps.foreignValues
      · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, foreignSupported, Bind.bind, Except.bind, throw] at valid
      · cases selectCap : caps.select
        · simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, foreignSupported, selectCap, Bind.bind, Except.bind, throw] at valid
        · cases first : condition.validate caps types with
            | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, foreignSupported, selectCap, first, Bind.bind, Except.bind] at valid
            | ok checked =>
              cases checked
              cases second : yes.validate caps types with
              | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, foreignSupported, selectCap, first, second, Bind.bind, Except.bind] at valid
              | ok checked =>
                cases checked
                cases third : no.validate caps types with
                | error message => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, foreignSupported, selectCap, first, second, third, Bind.bind, Except.bind] at valid
                | ok checked =>
                  cases checked
                  have acceptedCondition : condition.validate caps types = .ok () := first
                  have acceptedYes : yes.validate caps types = .ok () := second
                  have acceptedNo : no.validate caps types = .ok () := third
                  simp [Expr.eval, ihCondition caps types ctx left right acceptedCondition agreement,
                    ihYes caps types ctx left right acceptedYes agreement,
                    ihNo caps types ctx left right acceptedNo agreement]
    | opaqueBytes | opaqueString =>
      cases selectCap : caps.select
      · simp [Expr.validate, Ty.isBytes, Ty.isJubjub, Ty.isForeign,
          selectCap, Bind.bind, Except.bind, throw] at valid
      · cases first : condition.validate caps types with
        | error message =>
          simp [Expr.validate, Ty.isBytes, Ty.isJubjub, Ty.isForeign,
            selectCap, first, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          cases second : yes.validate caps types with
          | error message =>
            simp [Expr.validate, Ty.isBytes, Ty.isJubjub, Ty.isForeign,
              selectCap, first, second, Bind.bind, Except.bind] at valid
          | ok checked =>
            cases checked
            cases third : no.validate caps types with
            | error message =>
              simp [Expr.validate, Ty.isBytes, Ty.isJubjub, Ty.isForeign,
                selectCap, first, second, third, Bind.bind, Except.bind] at valid
            | ok checked =>
              cases checked
              have acceptedCondition : condition.validate caps types = .ok () := first
              have acceptedYes : yes.validate caps types = .ok () := second
              have acceptedNo : no.validate caps types = .ok () := third
              simp [Expr.eval, ihCondition caps types ctx left right acceptedCondition agreement,
                ihYes caps types ctx left right acceptedYes agreement,
                ihNo caps types ctx left right acceptedNo agreement]
    | jubjubScalar => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
    | jubjubPoint => simp [Expr.validate, Ty.isBytes, Ty.isOpaqueBytes, Ty.isOpaqueString, Ty.isJubjub, Ty.isForeign, Bind.bind, Except.bind, throw] at valid
  case poseidon2 =>
    intro domain a b ihA ihB caps types ctx left right valid agreement
    have domainOk : domain < caps.nativeModulus := by
      by_cases domainBad : caps.nativeModulus ≤ domain
      · simp [Expr.validate, domainBad, Bind.bind, Except.bind, throw] at valid
      · omega
    have domainNotBad : ¬ caps.nativeModulus ≤ domain := Nat.not_le_of_gt domainOk
    cases supported : caps.poseidon2
    · simp [Expr.validate, supported, domainOk, domainNotBad, Bind.bind, Except.bind, throw] at valid
    ·
      cases first : a.validate caps types with
      | error message => simp [Expr.validate, supported, domainOk, domainNotBad, first, Bind.bind, Except.bind] at valid
      | ok checked =>
        cases checked
        cases second : b.validate caps types with
        | error message => simp [Expr.validate, supported, domainOk, domainNotBad, first, second, Bind.bind, Except.bind] at valid
        | ok checked =>
          cases checked
          have acceptedA : a.validate caps types = .ok () := first
          have acceptedB : b.validate caps types = .ok () := by
            simpa [Expr.validate, supported, domainOk, domainNotBad, first, Bind.bind, Except.bind] using valid
          simp [Expr.eval, ihA caps types ctx left right acceptedA agreement,
            ihB caps types ctx left right acceptedB agreement]
  case persistentHashVector32 =>
    intro values ihValues caps types ctx left right valid agreement
    cases supported : caps.persistentHashVector32
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · have lowerBound : 1 ≤ values.length := by
        by_cases bound : 1 ≤ values.length
        · exact bound
        · simp [Expr.validate, supported, bound, Bind.bind, Except.bind, throw] at valid
      have upperBound : values.length ≤ 32 := by
        by_cases bound : values.length ≤ 32
        · exact bound
        · simp [Expr.validate, supported, lowerBound, bound, Bind.bind, Except.bind, throw] at valid
      have nonempty : values ≠ [] := by
        intro empty
        simp [empty] at lowerBound
      have noTooLong : ¬ 32 < values.length := by omega
      have validationLoop : Except.bind
          (forIn values PUnit.unit (fun (value : Expr (.bytes 32)) (_ : PUnit) => do
            value.validate caps types
            pure (.yield .unit))) (fun _ => pure ()) = .ok () := by
        simpa [Expr.validate, supported, lowerBound, upperBound, Bind.bind, Except.bind] using valid
      have loopValid : forIn values PUnit.unit (fun (value : Expr (.bytes 32)) (_ : PUnit) => do
          value.validate caps types
          pure (.yield .unit)) = .ok .unit := by
        obtain ⟨step, success⟩ := bind_success_first validationLoop
        cases step
        exact success
      have memberValid := validateList_members caps types values loopValid
      have same : ∀ value ∈ values, value.eval ctx left = value.eval ctx right := by
        intro value member
        exact ihValues value member caps types ctx left right (memberValid value member) agreement
      simp [Expr.eval, nonempty, noTooLong]
      all_goals
        congr 1
        apply foldlM_fixedList_congr
        intro value member state
        simp [same value member]
  case persistentHashNativeVector =>
    intro values ihValues caps types ctx left right valid agreement
    cases supported : caps.persistentHashNative
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · have lowerBound : 1 ≤ values.length := by
        by_cases bound : 1 ≤ values.length
        · exact bound
        · simp [Expr.validate, supported, bound, Bind.bind, Except.bind, throw] at valid
      have upperBound : values.length ≤ 32 := by
        by_cases bound : values.length ≤ 32
        · exact bound
        · simp [Expr.validate, supported, lowerBound, bound, Bind.bind, Except.bind, throw] at valid
      have nonempty : values ≠ [] := by
        intro empty
        simp [empty] at lowerBound
      have noTooLong : ¬ 32 < values.length := by omega
      have validationLoop : Except.bind
          (forIn values PUnit.unit (fun (value : Expr Ty.native) (_ : PUnit) => do
            value.validate caps types
            pure (.yield .unit))) (fun _ => pure ()) = .ok () := by
        simpa [Expr.validate, supported, lowerBound, upperBound, Bind.bind, Except.bind] using valid
      have loopValid : forIn values PUnit.unit (fun (value : Expr Ty.native) (_ : PUnit) => do
          value.validate caps types
          pure (.yield .unit)) = .ok .unit := by
        obtain ⟨step, success⟩ := bind_success_first validationLoop
        cases step
        exact success
      have memberValid := validateList_members caps types values loopValid
      have same : ∀ value ∈ values, value.eval ctx left = value.eval ctx right := by
        intro value member
        exact ihValues value member caps types ctx left right (memberValid value member) agreement
      simp [Expr.eval, nonempty, noTooLong]
      all_goals
        congr 1
        apply foldlM_fixedList_congr
        intro value member state
        simp [same value member]
  case hashToCurve =>
    intro values ihValues caps types ctx left right valid agreement
    cases supported : caps.hashToCurve
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases jubjubSupported : caps.jubjub
      · simp [Expr.validate, supported, jubjubSupported, Bind.bind, Except.bind, throw] at valid
      · have upperBound : values.length ≤ Types.defaultLimits.maxVectorLength := by
          by_cases bound : values.length ≤ Types.defaultLimits.maxVectorLength
          · exact bound
          · simp [Expr.validate, supported, jubjubSupported, bound, Bind.bind, Except.bind, throw] at valid
        have noTooLong : ¬ Types.defaultLimits.maxVectorLength < values.length := by omega
        have validationLoop : Except.bind
            (forIn values PUnit.unit (fun (value : Expr Ty.native) (_ : PUnit) => do
              value.validate caps types
              pure (.yield .unit))) (fun _ => pure ()) = .ok () := by
          simpa [Expr.validate, supported, jubjubSupported, upperBound, Bind.bind, Except.bind] using valid
        have loopValid : forIn values PUnit.unit (fun (value : Expr Ty.native) (_ : PUnit) => do
            value.validate caps types
            pure (.yield .unit)) = .ok .unit := by
          obtain ⟨step, success⟩ := bind_success_first validationLoop
          cases step
          exact success
        have memberValid := validateList_members caps types values loopValid
        have same : ∀ value ∈ values, value.eval ctx left = value.eval ctx right := by
          intro value member
          exact ihValues value member caps types ctx left right (memberValid value member) agreement
        let leftStep : Expr Ty.native → List Nat → Except String (ForInStep (List Nat)) :=
          fun value reversedInputs => do
            let field ← value.eval ctx left
            if field >= ctx.modulus then throw "noncanonical hash_to_curve Native input"
            pure (.yield (field :: reversedInputs))
        let rightStep : Expr Ty.native → List Nat → Except String (ForInStep (List Nat)) :=
          fun value reversedInputs => do
            let field ← value.eval ctx right
            if field >= ctx.modulus then throw "noncanonical hash_to_curve Native input"
            pure (.yield (field :: reversedInputs))
        have loopEqual := forIn_fixedList_congr leftStep rightStep values [] (by
          intro value member state
          simp [leftStep, rightStep, same value member])
        simp only [Expr.eval, noTooLong]
        congr 1
        rw [loopEqual]
  case transientHash =>
    intro values ihValues caps types ctx left right valid agreement
    cases supported : caps.poseidon2
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · have upperBound : values.length ≤ Types.defaultLimits.maxVectorLength := by
        by_cases bound : values.length ≤ Types.defaultLimits.maxVectorLength
        · exact bound
        · simp [Expr.validate, supported, bound, Bind.bind, Except.bind, throw] at valid
      have noTooLong : ¬ Types.defaultLimits.maxVectorLength < values.length := by omega
      have validationLoop : Except.bind
          (forIn values PUnit.unit (fun (value : Expr Ty.native) (_ : PUnit) => do
            value.validate caps types
            pure (.yield .unit))) (fun _ => pure ()) = .ok () := by
        simpa [Expr.validate, supported, upperBound, Bind.bind, Except.bind] using valid
      have loopValid : forIn values PUnit.unit (fun (value : Expr Ty.native) (_ : PUnit) => do
          value.validate caps types
          pure (.yield .unit)) = .ok .unit := by
        obtain ⟨step, success⟩ := bind_success_first validationLoop
        cases step
        exact success
      have memberValid := validateList_members caps types values loopValid
      have same : ∀ value ∈ values, value.eval ctx left = value.eval ctx right := by
        intro value member
        exact ihValues value member caps types ctx left right (memberValid value member) agreement
      let leftStep : Expr Ty.native → List Nat → Except String (ForInStep (List Nat)) :=
        fun value inputs => do
          let field ← value.eval ctx left
          if field >= ctx.modulus then throw "noncanonical transient_hash Native input"
          pure (.yield (inputs ++ [field]))
      let rightStep : Expr Ty.native → List Nat → Except String (ForInStep (List Nat)) :=
        fun value inputs => do
          let field ← value.eval ctx right
          if field >= ctx.modulus then throw "noncanonical transient_hash Native input"
          pure (.yield (inputs ++ [field]))
      have loopEqual := forIn_fixedList_congr leftStep rightStep values [] (by
        intro value member state
        simp [leftStep, rightStep, same value member])
      simp only [Expr.eval, noTooLong]
      congr 1
      rw [loopEqual]
  case hashToCurveFab =>
    intro environment type values ihValues caps types ctx left right valid agreement
    cases hashSupported : caps.hashToCurve
    · simp [Expr.validate, hashSupported, Bind.bind, Except.bind, throw] at valid
    · cases jubjubSupported : caps.jubjub
      · simp [Expr.validate, hashSupported, jubjubSupported, Bind.bind, Except.bind, throw] at valid
      · cases layout : validateFabHashLayout environment type values with
        | error message => simp [Expr.validate, hashSupported, jubjubSupported, layout, Bind.bind, Except.bind] at valid
        | ok checkedLayout =>
          simp [Expr.validate, hashSupported, jubjubSupported, layout, Bind.bind, Except.bind] at valid
          cases fieldResult : fabHashLayoutFields checkedLayout with
          | error message => simp [fieldResult] at valid
          | ok fields =>
            have fieldBound : fabHashEncodedFieldCount fields ≤ Types.defaultLimits.maxVectorLength := by
              by_cases bound : fabHashEncodedFieldCount fields ≤ Types.defaultLimits.maxVectorLength
              · exact bound
              · simp [fieldResult, bound, Bind.bind, Except.bind] at valid
            have valuesValid := validateFabHashValues_members caps types values (by
              simpa [fieldResult, fieldBound] using valid)
            have same : ∀ item ∈ values, item.2.eval ctx left = item.2.eval ctx right := by
              intro item member
              exact ihValues item member caps types ctx left right (valuesValid item member) agreement
            exact Expr.eval_hashToCurveFab_env_congr ctx left right environment type values same
  case transientHashFab =>
    intro environment type values ihValues caps types ctx left right valid agreement
    cases supported : caps.poseidon2
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases schema : validateTransientFabHashFields environment type values with
      | error message =>
        have failed : discard (Except.error message : Except String (List (String × Types.Layout))) =
            (Except.error message : Except String PUnit) := rfl
        rw [Expr.validate, supported, schema, failed] at valid
        simp [Bind.bind, Except.bind] at valid
      | ok fields =>
        have passed : discard (Except.ok fields : Except String (List (String × Types.Layout))) =
            (Except.ok PUnit.unit : Except String PUnit) := rfl
        have valuesValid := validateFabHashValues_members caps types values (by
          simpa [Expr.validate, supported, schema, passed, Bind.bind, Except.bind] using valid)
        have same : ∀ item ∈ values, item.2.eval ctx left = item.2.eval ctx right := by
          intro item member
          exact ihValues item member caps types ctx left right (valuesValid item member) agreement
        exact Expr.eval_transientHashFab_env_congr ctx left right environment type values same
  case persistentHashFab =>
    intro environment type values ihValues caps types ctx left right valid agreement
    cases supported : caps.persistentHash32
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases schema : validateFabHashLayout environment type values with
      | error message =>
        have failed : discard (Except.error message : Except String Types.Layout) =
            (Except.error message : Except String PUnit) := rfl
        rw [Expr.validate, supported, schema, failed] at valid
        simp [Bind.bind, Except.bind] at valid
      | ok checkedLayout =>
        have passed : discard (Except.ok checkedLayout : Except String Types.Layout) =
            (Except.ok PUnit.unit : Except String PUnit) := rfl
        have valuesValid := validateFabHashValues_members caps types values (by
          simpa [Expr.validate, supported, schema, passed, Bind.bind, Except.bind] using valid)
        have same : ∀ item ∈ values, item.2.eval ctx left = item.2.eval ctx right := by
          intro item member
          exact ihValues item member caps types ctx left right (valuesValid item member) agreement
        exact Expr.eval_persistentHashFab_env_congr ctx left right environment type values same
  case sha512Fab =>
    intro environment type values ihValues caps types ctx left right valid agreement
    cases supported : caps.sha512
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases schema : validateFabHashLayout environment type values with
      | error message =>
        have failed : discard (Except.error message : Except String Types.Layout) =
            (Except.error message : Except String PUnit) := rfl
        rw [Expr.validate, supported, schema, failed] at valid
        simp [Bind.bind, Except.bind] at valid
      | ok checkedLayout =>
        have passed : discard (Except.ok checkedLayout : Except String Types.Layout) =
            (Except.ok PUnit.unit : Except String PUnit) := rfl
        have valuesValid := validateFabHashValues_members caps types values (by
          simpa [Expr.validate, supported, schema, passed, Bind.bind, Except.bind] using valid)
        have same : ∀ item ∈ values, item.2.eval ctx left = item.2.eval ctx right := by
          intro item member
          exact ihValues item member caps types ctx left right (valuesValid item member) agreement
        exact Expr.eval_sha512Fab_env_congr ctx left right environment type values same
  case keccak256Fab =>
    intro environment type values ihValues caps types ctx left right valid agreement
    cases supported : caps.keccak256
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases schema : validateFabHashLayout environment type values with
      | error message =>
        have failed : discard (Except.error message : Except String Types.Layout) =
            (Except.error message : Except String PUnit) := rfl
        rw [Expr.validate, supported, schema, failed] at valid
        simp [Bind.bind, Except.bind] at valid
      | ok checkedLayout =>
        have passed : discard (Except.ok checkedLayout : Except String Types.Layout) =
            (Except.ok PUnit.unit : Except String PUnit) := rfl
        have valuesValid := validateFabHashValues_members caps types values (by
          simpa [Expr.validate, supported, schema, passed, Bind.bind, Except.bind] using valid)
        have same : ∀ item ∈ values, item.2.eval ctx left = item.2.eval ctx right := by
          intro item member
          exact ihValues item member caps types ctx left right (valuesValid item member) agreement
        exact Expr.eval_keccak256Fab_env_congr ctx left right environment type values same
  case persistentCommitFab =>
    intro environment type opening values ihOpening ihValues caps types ctx left right valid agreement
    cases supported : caps.persistentHash32
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases schema : validateFabCommitLayout environment type values with
      | error message => simp [Expr.validate, supported, schema, Bind.bind, Except.bind] at valid
      | ok checkedLayout =>
        cases fields : fabCommitHashLayoutFields checkedLayout with
        | error message => simp [Expr.validate, supported, schema, fields, Bind.bind, Except.bind] at valid
        | ok layouts =>
          cases openingResult : opening.validate caps types with
          | error message =>
            by_cases bound : fabHashEncodedFieldCount layouts + 2 ≤ fabHashNativeOperandLimit
            · simp [Expr.validate, supported, schema, fields, openingResult, bound, Bind.bind, Except.bind] at valid
            · simp [Expr.validate, supported, schema, fields, openingResult, bound, Bind.bind, Except.bind] at valid
          | ok openingValue =>
            have openingValid : opening.validate caps types = .ok () := openingResult
            have valuesValid := validateFabHashValues_members caps types values (by
              by_cases bound : fabHashEncodedFieldCount layouts + 2 ≤ fabHashNativeOperandLimit
              · simpa [Expr.validate, supported, schema, fields, openingResult, bound, Bind.bind, Except.bind] using valid
              · simp [Expr.validate, supported, schema, fields, openingResult, bound, Bind.bind, Except.bind] at valid)
            have openingSame := ihOpening caps types ctx left right openingValid agreement
            have same : ∀ item ∈ values, item.2.eval ctx left = item.2.eval ctx right := by
              intro item member
              exact ihValues item member caps types ctx left right (valuesValid item member) agreement
            exact Expr.eval_persistentCommitFab_env_congr ctx left right environment type opening values openingSame same
  case transientCommitFab =>
    intro environment type opening values ihOpening ihValues caps types ctx left right valid agreement
    cases supported : caps.poseidon2
    · simp [Expr.validate, supported, Bind.bind, Except.bind, throw] at valid
    · cases schema : validateFabCommitLayout environment type values with
      | error message => simp [Expr.validate, supported, schema, Bind.bind, Except.bind] at valid
      | ok checkedLayout =>
        cases fields : fabCommitHashLayoutFields checkedLayout with
        | error message => simp [Expr.validate, supported, schema, fields, Bind.bind, Except.bind] at valid
        | ok layouts =>
          cases openingResult : opening.validate caps types with
          | error message =>
            by_cases bound : fabHashEncodedFieldCount layouts + 1 ≤ Types.defaultLimits.maxVectorLength
            · simp [Expr.validate, supported, schema, fields, openingResult, bound, Bind.bind, Except.bind] at valid
            · simp [Expr.validate, supported, schema, fields, openingResult, bound, Bind.bind, Except.bind] at valid
          | ok openingValue =>
            have openingValid : opening.validate caps types = .ok () := openingResult
            have valuesValid := validateFabHashValues_members caps types values (by
              by_cases bound : fabHashEncodedFieldCount layouts + 1 ≤ Types.defaultLimits.maxVectorLength
              · simpa [Expr.validate, supported, schema, fields, openingResult, bound, Bind.bind, Except.bind] using valid
              · simp [Expr.validate, supported, schema, fields, openingResult, bound, Bind.bind, Except.bind] at valid)
            have openingSame := ihOpening caps types ctx left right openingValid agreement
            have same : ∀ item ∈ values, item.2.eval ctx left = item.2.eval ctx right := by
              intro item member
              exact ihValues item member caps types ctx left right (valuesValid item member) agreement
            exact Expr.eval_transientCommitFab_env_congr ctx left right environment type opening values openingSame same
  all_goals
    first
    | unfold Agreements; intros; simp [Expr.eval]; done
    | intro item member
      have impossible : False := by simpa using member
      exact impossible.elim
    | intro head tail ihHead ihTail item member
      rcases List.mem_cons.mp member with equal | isMember
      · cases equal
        exact ihHead
      · exact ihTail item isMember
    | intro ty value ih
      exact ih
    | skip

/-- Validation limits expression dependencies to the declared type scope.
Evaluation therefore agrees across environments that agree on those names.
Local lets extend both scopes with the same evaluated value. -/
theorem eval_agree_of_valid (expression : Expr ty) (caps : Capabilities)
    (types : TypeEnv) (ctx : EvalContext) (left right : EvalEnv)
    (valid : expression.validate caps types = .ok ())
    (agreement : ∀ name ∈ types.map Prod.fst, left.lookup name = right.lookup name) :
    expression.eval ctx left = expression.eval ctx right :=
  eval_agreements ty expression caps types ctx left right valid agreement

#print axioms eval_agree_of_valid

end Noctium.Verification.GenericStateExpressionScope
