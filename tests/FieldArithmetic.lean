import Noctium.Compiler
import Noctium.Semantics

open Noctium

section Source
open scoped Noctium

noctium_circuit nativeFieldArithmetic where
  private left : Native
  private right : Native
  output sum : Native := disclose(add(left, right))
  output difference : Native := disclose(sub(left, right))
  output product : Native := disclose(mul(left, right))
  output subtractFromZero : Native := disclose(sub(0, left))
  output equal : Bool := disclose(eq(left, right))
  output notEqual : Bool := disclose(boolNot(eq(left, right)))
end

noctium_contract NativeFieldArithmetic where
  entry calculate uses nativeFieldArithmetic where
    return returnedSum : Native := sum
    return returnedDifference : Native := difference
    return returnedProduct : Native := product
    return returnedSubtractFromZero : Native := subtractFromZero
    return returnedEqual : Bool := equal
    return returnedNotEqual : Bool := notEqual
  end
end

private def fieldContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

private def modulus := Field.modulus

#guard match nativeFieldArithmetic.run fieldContext [
    ("left", .native (modulus - 1)), ("right", .native 1)] with
  | .ok values => values == [
      ("sum", .native 0),
      ("difference", .native (modulus - 2)),
      ("product", .native (modulus - 1)),
      ("subtractFromZero", .native 1),
      ("equal", .bool Bool.false),
      ("notEqual", .bool Bool.true)]
  | _ => Bool.false

#guard match nativeFieldArithmetic.run fieldContext [
    ("left", .native (modulus - 1)), ("right", .native (modulus - 1))] with
  | .ok values => values == [
      ("sum", .native (modulus - 2)),
      ("difference", .native 0),
      ("product", .native 1),
      ("subtractFromZero", .native 1),
      ("equal", .bool Bool.true),
      ("notEqual", .bool Bool.false)]
  | _ => Bool.false

#guard match nativeFieldArithmetic.run fieldContext [
    ("left", .native 0), ("right", .native 1)] with
  | .ok values => values == [
      ("sum", .native 1),
      ("difference", .native (modulus - 1)),
      ("product", .native 0),
      ("subtractFromZero", .native 0),
      ("equal", .bool Bool.false),
      ("notEqual", .bool Bool.true)]
  | _ => Bool.false

noctium_circuit ordinaryMixed where
  private fieldValue : Native
  private amount : UInt 248
  private zero : UIntRange 1
  output sumFieldFirstOutput : Native := disclose(add(fieldValue, amount))
  output sumUIntFirstOutput : Native := disclose(add(amount, fieldValue))
  output differenceFieldFirstOutput : Native := disclose(sub(fieldValue, amount))
  output differenceUIntFirstOutput : Native := disclose(sub(amount, fieldValue))
  output productFieldFirstOutput : Native := disclose(mul(fieldValue, amount))
  output productUIntFirstOutput : Native := disclose(mul(amount, fieldValue))
  output withZeroOutput : Native := disclose(add(fieldValue, zero))
  output equalFieldFirstOutput : Bool := disclose(eq(fieldValue, amount))
  output equalUIntFirstOutput : Bool := disclose(eq(amount, fieldValue))
  output notEqualFieldFirstOutput : Bool := disclose(boolNot(eq(fieldValue, amount)))
  output notEqualUIntFirstOutput : Bool := disclose(boolNot(eq(amount, fieldValue)))
end

noctium_witness_circuit readableMixed where
  private fieldValue : Native
  private amount : UInt 248
  private zero : UIntRange 1
  output sumFieldFirstOutput : Native := disclose(add(fieldValue, amount))
  output sumUIntFirstOutput : Native := disclose(add(amount, fieldValue))
  output differenceFieldFirstOutput : Native := disclose(sub(fieldValue, amount))
  output differenceUIntFirstOutput : Native := disclose(sub(amount, fieldValue))
  output productFieldFirstOutput : Native := disclose(mul(fieldValue, amount))
  output productUIntFirstOutput : Native := disclose(mul(amount, fieldValue))
  output withZeroOutput : Native := disclose(add(fieldValue, zero))
  output equalFieldFirstOutput : Bool := disclose(eq(fieldValue, amount))
  output equalUIntFirstOutput : Bool := disclose(eq(amount, fieldValue))
  output notEqualFieldFirstOutput : Bool := disclose(boolNot(eq(fieldValue, amount)))
  output notEqualUIntFirstOutput : Bool := disclose(boolNot(eq(amount, fieldValue)))
end

noctium_contract MixedFieldArithmetic where
  entry ordinary uses ordinaryMixed where
    return sumFieldFirst : Native := sumFieldFirstOutput
    return sumUIntFirst : Native := sumUIntFirstOutput
    return differenceFieldFirst : Native := differenceFieldFirstOutput
    return differenceUIntFirst : Native := differenceUIntFirstOutput
    return productFieldFirst : Native := productFieldFirstOutput
    return productUIntFirst : Native := productUIntFirstOutput
    return withZero : Native := withZeroOutput
    return equalFieldFirst : Bool := equalFieldFirstOutput
    return equalUIntFirst : Bool := equalUIntFirstOutput
    return notEqualFieldFirst : Bool := notEqualFieldFirstOutput
    return notEqualUIntFirst : Bool := notEqualUIntFirstOutput
  end
  entry readable uses readableMixed arguments [fieldValue, amount, zero] where
    return sumFieldFirst : Native := sumFieldFirstOutput
    return sumUIntFirst : Native := sumUIntFirstOutput
    return differenceFieldFirst : Native := differenceFieldFirstOutput
    return differenceUIntFirst : Native := differenceUIntFirstOutput
    return productFieldFirst : Native := productFieldFirstOutput
    return productUIntFirst : Native := productUIntFirstOutput
    return withZero : Native := withZeroOutput
    return equalFieldFirst : Bool := equalFieldFirstOutput
    return equalUIntFirst : Bool := equalUIntFirstOutput
    return notEqualFieldFirst : Bool := notEqualFieldFirstOutput
    return notEqualUIntFirst : Bool := notEqualUIntFirstOutput
  end
end

end Source
