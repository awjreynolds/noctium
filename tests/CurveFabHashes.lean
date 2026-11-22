import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Types

private def curveFabEnvironment : CompositeEnv := {
  structures := [
    {id := "CurveFabHashes.Inner", fields := [
      {name := "scalar", type := .scalar .jubjubScalar},
      {name := "point", type := .scalar .jubjubPoint}
    ]},
    {id := "CurveFabHashes.CurvePayload", fields := [
      {name := "inner", type := .structure "CurveFabHashes.Inner"},
      {name := "secpBase", type := .scalar (.foreign (.base .secp256k1))},
      {name := "secpPoint", type := .scalar (.foreign (.point .secp256k1))},
      {name := "pair", type := .tuple [
        .scalar .jubjubPoint,
        .scalar (.foreign (.point .secp256k1))
      ]}
    ]}
  ]
}

private def curveFabPayloadType : CompositeType :=
  .structure "CurveFabHashes.CurvePayload"

noctium_circuit curveFabHashInputs where
  private jubjubScalar : JubjubScalar
  private jubjubPoint : JubjubPoint
  private secpBase : Secp256k1Base
  private secpPoint : Secp256k1Point
  private pairJubjubPoint : JubjubPoint
  private pairSecpPoint : Secp256k1Point
  output persistentDigest : Bytes32 := disclose(persistentHashFab(
    curveFabEnvironment, curveFabPayloadType,
    [jubjubScalar, jubjubPoint, secpBase, secpPoint, pairJubjubPoint, pairSecpPoint]))
  output transientDigest : Native := disclose(transientHashFab(
    curveFabEnvironment, curveFabPayloadType,
    [jubjubScalar, jubjubPoint, secpBase, secpPoint, pairJubjubPoint, pairSecpPoint]))
  output curveDigest : JubjubPoint := disclose(hashToCurveFab(
    curveFabEnvironment, curveFabPayloadType,
    [jubjubScalar, jubjubPoint, secpBase, secpPoint, pairJubjubPoint, pairSecpPoint]))
  -- Thirty-two tab bytes encode the oracle opening [9;32].
  output persistentCommitResult : Bytes32 := disclose(persistentCommitFab(
    curveFabEnvironment, curveFabPayloadType,
    bytes32("\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t"),
    [jubjubScalar, jubjubPoint, secpBase, secpPoint, pairJubjubPoint, pairSecpPoint]))
  output transientCommitResult : Native := disclose(transientCommitFab(
    curveFabEnvironment, curveFabPayloadType, 77,
    [jubjubScalar, jubjubPoint, secpBase, secpPoint, pairJubjubPoint, pairSecpPoint]))
  output sha512Result : Bytes 64 := disclose(sha512Fab(
    curveFabEnvironment, curveFabPayloadType,
    [jubjubScalar, jubjubPoint, secpBase, secpPoint, pairJubjubPoint, pairSecpPoint]))
end

private def persistentOpeningIsNine : _root_.Bool :=
  match curveFabHashInputs.outputs.find? (·.name == "persistentCommitResult") with
  | some found =>
    if h : found.ty = .bytes 32 then
      match h ▸ found.value with
      | .disclose _ (.persistentCommitFab _ _ (.bytes32Literal values) _) =>
        values == List.replicate 32 9
      | _ => _root_.Bool.false
    else _root_.Bool.false
  | none => _root_.Bool.false

#guard persistentOpeningIsNine

noctium_contract CurveFabHashes where
  entry hash uses curveFabHashInputs where
    return persistentResult : Bytes32 := persistentDigest
    return transientResult : Native := transientDigest
    return curveResult : JubjubPoint := curveDigest
    return persistentCommitOutput : Bytes32 := persistentCommitResult
    return transientCommitOutput : Native := transientCommitResult
    return sha512Output : Bytes 64 := sha512Result
  end
end

private def curveFabEntry : Entrypoint :=
  match CurveFabHashes.entrypoints with
  | candidate :: _ => candidate
  | _ => {name := "missing", circuit := {name := "missing"}}

private def curveFabAtoms : Except String (List String) := do
  let checked ← (Types.checkedLayout Types.defaultLimits curveFabEnvironment
    curveFabPayloadType).mapError (·.message)
  let fields ← Noctium.fabHashLayoutFields checked.value
  let atoms ← fields.mapM fun field => Noctium.fabHashLayoutAtoms field.2
  pure atoms.flatten

private def curveFabAtomsMatch : _root_.Bool :=
  match curveFabAtoms with
  | .ok atoms => atoms == [
      "field", "field", "field", "bytes:24", "bytes:8",
      "bytes:24", "bytes:8", "bytes:24", "bytes:8", "field",
      "field", "field", "bytes:24", "bytes:8", "bytes:24", "bytes:8", "field"
    ]
  | .error _ => _root_.Bool.false

#guard curveFabAtomsMatch

#guard match Backend.Native.expectedEntrypoint CurveFabHashes.state curveFabEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint CurveFabHashes.state curveFabEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Native.expectedEntrypoint CurveFabHashes.state curveFabEntry,
    Backend.Zkir.lowerEntrypoint CurveFabHashes.state curveFabEntry with
  | .ok expected, .ok program =>
    match Backend.Native.validate expected program with
    | .ok _ => Bool.true
    | .error _ => Bool.false
  | _, _ => Bool.false

#guard match Noctium.validateTransientFabHashFields curveFabEnvironment
    curveFabPayloadType [⟨.jubjubScalar, .jubjubScalarFromNative (.native 17)⟩] with
  | .error _ => Bool.true
  | .ok _ => Bool.false
