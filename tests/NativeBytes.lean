import Noctium.Frontend
import Noctium.Disclosure
import Noctium.Helpers

open scoped Noctium
open Noctium

noctium_circuit byteValues where
  private payload : Bytes 64
  private other31 : Bytes 31
  private wide33 : Bytes 33
  private empty0 : Bytes 0
  public chooseReverse : Bool
  let reversed : Bytes 64 := reverseBytes(payload)
  let selected : Bytes 64 := select(chooseReverse, reversed, payload)
  let joined : Bytes 64 := concatBytes(concatBytes(other31, bytes(0, "")), wide33)
  let part : Bytes 32 := sliceBytes(payload, 31, 63)
  let literal : Bytes 4 := bytes(4, "ABCD")
  assert eq(concatBytes(sliceBytes(payload, 0, 31), sliceBytes(payload, 31, 64)), payload)
  assert eq(reverseBytes(empty0), empty0)
  output payload31 : UInt 8 := disclose(byteAt(payload, 31))
  output payload32 : UInt 8 := disclose(byteAt(payload, 32))
  output payload62 : UInt 8 := disclose(byteAt(payload, 62))
  output payload63 : UInt 8 := disclose(byteAt(payload, 63))
  output selectedFirst : UInt 8 := disclose(byteAt(selected, 0))
  output selectedLast : UInt 8 := disclose(byteAt(selected, 63))
  output joined31 : UInt 8 := disclose(byteAt(joined, 31))
  output joined32 : UInt 8 := disclose(byteAt(joined, 32))
  output joined62 : UInt 8 := disclose(byteAt(joined, 62))
  output joined63 : UInt 8 := disclose(byteAt(joined, 63))
  output sliceFirst : UInt 8 := disclose(byteAt(part, 0))
  output sliceLast : UInt 8 := disclose(byteAt(part, 31))
  output literalLast : UInt 8 := disclose(byteAt(literal, 3))
end

noctium_contract NativeBytes where
  cell payload31 : UInt 8
  cell payload32 : UInt 8
  cell payload62 : UInt 8
  cell payload63 : UInt 8
  cell selectedFirst : UInt 8
  cell selectedLast : UInt 8
  cell joined31 : UInt 8
  cell joined32 : UInt 8
  cell joined62 : UInt 8
  cell joined63 : UInt 8
  cell sliceFirst : UInt 8
  cell sliceLast : UInt 8
  cell literalLast : UInt 8
  entry inspect uses byteValues where
    write payload31 := payload31
    write payload32 := payload32
    write payload62 := payload62
    write payload63 := payload63
    write selectedFirst := selectedFirst
    write selectedLast := selectedLast
    write joined31 := joined31
    write joined32 := joined32
    write joined62 := joined62
    write joined63 := joined63
    write sliceFirst := sliceFirst
    write sliceLast := sliceLast
    write literalLast := literalLast
    return selectedBytes : Bytes 64 := disclose(select(chooseReverse, reverseBytes(payload), payload))
    return joinedBytes : Bytes 64 := disclose(concatBytes(concatBytes(other31, bytes(0, "")), wide33))
    return sliceBytes : Bytes 32 := disclose(sliceBytes(payload, 31, 63))
    return otherBytes : Bytes 31 := disclose(other31)
    return wideBytes : Bytes 33 := disclose(wide33)
    return emptyBytes : Bytes 0 := disclose(empty0)
  end
end

noctium_circuit emptyGuard where
  private enabled : Bool
  private empty0 : Bytes 0
  output emptyChecked : Bytes 0 := disclose(reverseBytes(assertThen(enabled, empty0)))
end

noctium_contract NativeEmptyBytes where
  entry inspect uses emptyGuard where
    return emptyBytes : Bytes 0 := emptyChecked
  end
end

private def bytesSemanticContext : EvalContext :=
  {modulus := Field.modulus, poseidon2 := fun _ _ _ => pure 0}

private def ascendingBytes64 : Expr (.bytes 64) :=
  .bytesLiteral 64 (List.range 64)

#guard match (Expr.reverseBytes (.bytesLiteral 64 (List.range 64))).eval bytesSemanticContext [] with
  | .ok value => value == (List.range 64).reverse
  | .error _ => _root_.Bool.false
#guard match (Expr.sliceBytes ascendingBytes64 31 63).eval bytesSemanticContext [] with
  | .ok value => value == ((List.range 32).map (· + 31))
  | .error _ => _root_.Bool.false
#guard match (Expr.concatBytes (.bytesLiteral 31 (List.range 31))
    (.bytesLiteral 33 (List.range 33))).eval bytesSemanticContext [] with
  | .ok value => value == (List.range 31) ++ (List.range 33)
  | .error _ => _root_.Bool.false
private def zeroByteEqualityTerm : Helpers.Term :=
  Helpers.Term.eq
    (Helpers.Term.bytes (Helpers.BytesOp.sliceBytes 32 0 0) [
      Helpers.Term.bytes Helpers.BytesOp.persistentHash32 [
        Helpers.Term.bytes32Literal (List.replicate 32 0)]])
    (Helpers.Term.bytes (Helpers.BytesOp.bytesLiteral 0 []) [])

private def zeroByteEqualityDeclaration : Helpers.Declaration := {
  id := ⟨0, 0⟩
  name := "main"
  result := Noctium.Helpers.ResultType.scalar Noctium.Ty.bool
  body := [Noctium.Helpers.Statement.«return» (some zeroByteEqualityTerm)]
}

private def zeroByteEqualityProgram : Helpers.Program := {
  declarations := [zeroByteEqualityDeclaration]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}

#guard match Helpers.compile zeroByteEqualityProgram "main" with
  | .error _ => _root_.Bool.false
  | .ok circuit => match circuit.run bytesSemanticContext [] with
    | .error _ => _root_.Bool.true
    | .ok _ => _root_.Bool.false
example : (Expr.reverseBytes (Expr.reverseBytes ascendingBytes64)).eval
    bytesSemanticContext [] = ascendingBytes64.eval bytesSemanticContext [] :=
  Expr.eval_reverseBytes_twice bytesSemanticContext [] ascendingBytes64

#guard match (Expr.sliceBytes ascendingBytes64 63 65).validate Capabilities.source [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
#guard match (Expr.concatBytes (.bytesLiteral 1024 (List.replicate 1024 0))
    (.bytesLiteral 1 [0])).validate Capabilities.source [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
#guard match (Ty.bytes 1054).validate Capabilities.source with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false
#guard match (Ty.bytes 1055).validate Capabilities.source with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
#guard match ({name := "bytes31MapKey", state := [
    {name := "lookup", kind := .map (.bytes 31) .native}]} : Contract).validate Capabilities.source with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false
#guard match ({name := "bytes32MapKey", state := [
    {name := "lookup", kind := .map (.bytes 32) .native}]} : Contract).validate Capabilities.source with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard match Disclosure.circuit {
  name := "undisclosedGenericBytes"
  inputs := [{name := "payload", ty := .bytes 64, visibility := .private}]
  outputs := [{name := "reversed", ty := .bytes 64, value := (Expr.reverseBytes (.ref "payload"))}]
} with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

/-- error: byte slice bounds must satisfy 0 ≤ start ≤ end ≤ 64 -/
#guard_msgs in
noctium_circuit invalidByteSliceBounds where
  private payload : Bytes 64
  output invalid : Bytes 2 := sliceBytes(payload, 63, 65)
end
