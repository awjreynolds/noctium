import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir
import Noctium.Semantics

open scoped Noctium
open Noctium
open Noctium.Types

private def wideFabVectorsEnvironment : CompositeEnv := {}

private def wideFabVectors33Type : CompositeType :=
  .vector 33 (.scalar (.uint 65535))

private def wideFabVectors64Type : CompositeType :=
  .vector 64 (.scalar (.uint 65535))

noctium_circuit wideFabVectors33Inputs where
  private lane0 : UInt 16
  private lane1 : UInt 16
  private lane2 : UInt 16
  private lane3 : UInt 16
  private lane4 : UInt 16
  private lane5 : UInt 16
  private lane6 : UInt 16
  private lane7 : UInt 16
  private lane8 : UInt 16
  private lane9 : UInt 16
  private lane10 : UInt 16
  private lane11 : UInt 16
  private lane12 : UInt 16
  private lane13 : UInt 16
  private lane14 : UInt 16
  private lane15 : UInt 16
  private lane16 : UInt 16
  private lane17 : UInt 16
  private lane18 : UInt 16
  private lane19 : UInt 16
  private lane20 : UInt 16
  private lane21 : UInt 16
  private lane22 : UInt 16
  private lane23 : UInt 16
  private lane24 : UInt 16
  private lane25 : UInt 16
  private lane26 : UInt 16
  private lane27 : UInt 16
  private lane28 : UInt 16
  private lane29 : UInt 16
  private lane30 : UInt 16
  private lane31 : UInt 16
  private lane32 : UInt 16
  output digest : Bytes32 := disclose(persistentHashFab(
    wideFabVectorsEnvironment, wideFabVectors33Type, [lane0, lane1, lane2, lane3, lane4, lane5, lane6, lane7, lane8, lane9, lane10, lane11, lane12, lane13, lane14, lane15, lane16, lane17, lane18, lane19, lane20, lane21, lane22, lane23, lane24, lane25, lane26, lane27, lane28, lane29, lane30, lane31, lane32]))
  output shaDigest : Bytes 64 := disclose(sha512Fab(
    wideFabVectorsEnvironment, wideFabVectors33Type, [lane0, lane1, lane2, lane3, lane4, lane5, lane6, lane7, lane8, lane9, lane10, lane11, lane12, lane13, lane14, lane15, lane16, lane17, lane18, lane19, lane20, lane21, lane22, lane23, lane24, lane25, lane26, lane27, lane28, lane29, lane30, lane31, lane32]))
  output keccakDigest : Bytes32 := disclose(keccak256Fab(
    wideFabVectorsEnvironment, wideFabVectors33Type, [lane0, lane1, lane2, lane3, lane4, lane5, lane6, lane7, lane8, lane9, lane10, lane11, lane12, lane13, lane14, lane15, lane16, lane17, lane18, lane19, lane20, lane21, lane22, lane23, lane24, lane25, lane26, lane27, lane28, lane29, lane30, lane31, lane32]))
end

noctium_circuit wideFabVectors64Inputs where
  private lane0 : UInt 16
  private lane1 : UInt 16
  private lane2 : UInt 16
  private lane3 : UInt 16
  private lane4 : UInt 16
  private lane5 : UInt 16
  private lane6 : UInt 16
  private lane7 : UInt 16
  private lane8 : UInt 16
  private lane9 : UInt 16
  private lane10 : UInt 16
  private lane11 : UInt 16
  private lane12 : UInt 16
  private lane13 : UInt 16
  private lane14 : UInt 16
  private lane15 : UInt 16
  private lane16 : UInt 16
  private lane17 : UInt 16
  private lane18 : UInt 16
  private lane19 : UInt 16
  private lane20 : UInt 16
  private lane21 : UInt 16
  private lane22 : UInt 16
  private lane23 : UInt 16
  private lane24 : UInt 16
  private lane25 : UInt 16
  private lane26 : UInt 16
  private lane27 : UInt 16
  private lane28 : UInt 16
  private lane29 : UInt 16
  private lane30 : UInt 16
  private lane31 : UInt 16
  private lane32 : UInt 16
  private lane33 : UInt 16
  private lane34 : UInt 16
  private lane35 : UInt 16
  private lane36 : UInt 16
  private lane37 : UInt 16
  private lane38 : UInt 16
  private lane39 : UInt 16
  private lane40 : UInt 16
  private lane41 : UInt 16
  private lane42 : UInt 16
  private lane43 : UInt 16
  private lane44 : UInt 16
  private lane45 : UInt 16
  private lane46 : UInt 16
  private lane47 : UInt 16
  private lane48 : UInt 16
  private lane49 : UInt 16
  private lane50 : UInt 16
  private lane51 : UInt 16
  private lane52 : UInt 16
  private lane53 : UInt 16
  private lane54 : UInt 16
  private lane55 : UInt 16
  private lane56 : UInt 16
  private lane57 : UInt 16
  private lane58 : UInt 16
  private lane59 : UInt 16
  private lane60 : UInt 16
  private lane61 : UInt 16
  private lane62 : UInt 16
  private lane63 : UInt 16
  output digest : Bytes32 := disclose(persistentHashFab(
    wideFabVectorsEnvironment, wideFabVectors64Type, [lane0, lane1, lane2, lane3, lane4, lane5, lane6, lane7, lane8, lane9, lane10, lane11, lane12, lane13, lane14, lane15, lane16, lane17, lane18, lane19, lane20, lane21, lane22, lane23, lane24, lane25, lane26, lane27, lane28, lane29, lane30, lane31, lane32, lane33, lane34, lane35, lane36, lane37, lane38, lane39, lane40, lane41, lane42, lane43, lane44, lane45, lane46, lane47, lane48, lane49, lane50, lane51, lane52, lane53, lane54, lane55, lane56, lane57, lane58, lane59, lane60, lane61, lane62, lane63]))
end

noctium_contract WideFabVectors where
  entry hash33 uses wideFabVectors33Inputs where
    return digestResult : Bytes32 := digest
    return shaDigestResult : Bytes 64 := shaDigest
    return keccakDigestResult : Bytes32 := keccakDigest
  end
  entry hash64 uses wideFabVectors64Inputs where
    return digestResult : Bytes32 := digest
  end
end

private def wideFabVectorsNibble (value : Char) : Nat :=
  if '0' ≤ value && value ≤ '9' then value.toNat - '0'.toNat
  else value.toNat - 'a'.toNat + 10

private def bytesFromHex (text : String) : List Nat :=
  go text.toList
where
  go : List Char → List Nat
  | high :: low :: rest =>
    (wideFabVectorsNibble high * 16 + wideFabVectorsNibble low) :: go rest
  | _ => []

private def wideFabVectorsDigest33 : List Nat :=
  bytesFromHex "eaa4e04a3b174594a50aadaa01338f6934790a85f6be3d54587937c916d32d89"

private def wideFabVectorsDigest64 : List Nat :=
  bytesFromHex "d9f3c8064105485f0821fb42ba0846faef768a4d1987c65cdb7dfdba1e4a5656"

private def wideFabVectorsPreimage (count : Nat) : List Nat :=
  (List.range count).flatMap fun lane => [lane % 256, lane / 256]

private def wideFabVectorsValues (count : Nat) : List (Sigma Expr) :=
  (List.range count).map fun lane =>
    ⟨.uint 65535, .ref s!"lane{lane}"⟩

private def wideFabVectorsExpression (count : Nat) : Expr (.bytes 32) :=
  .persistentHashFab wideFabVectorsEnvironment
    (.vector count (.scalar (.uint 65535))) (wideFabVectorsValues count)

private def wideFabVectorsInputs (count : Nat) : List (String × Value) :=
  (List.range count).map fun lane =>
    (s!"lane{lane}", .uint 65535 lane)

private def wideFabVectorsContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
  persistentHash32 := fun preimage =>
    if preimage == wideFabVectorsPreimage 33 then pure wideFabVectorsDigest33
    else if preimage == wideFabVectorsPreimage 64 then pure wideFabVectorsDigest64
    else throw "wide FAB vector fixture received a different byte preimage"
}

#guard match (wideFabVectorsExpression 33).eval wideFabVectorsContext (wideFabVectorsInputs 33) with
  | .ok digest => digest == wideFabVectorsDigest33
  | .error _ => _root_.Bool.false

#guard match (wideFabVectorsExpression 64).eval wideFabVectorsContext (wideFabVectorsInputs 64) with
  | .ok digest => digest == wideFabVectorsDigest64
  | .error _ => _root_.Bool.false
