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

end Source
