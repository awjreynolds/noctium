import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir
import Noctium.Semantics

open scoped Noctium
open Noctium
open Noctium.Types

private def rootFabVectorEnvironment : CompositeEnv := {}

private def rootFabVectorValuesType : CompositeType :=
  .vector 2 (.scalar (.uint 65535))

private def rootFabVectorEmptyType : CompositeType :=
  .vector 0 (.scalar (.uint 65535))

noctium_circuit rootFabVectorValuesInputs where
  private first : UInt 16
  private second : UInt 16
  output digest : Bytes32 := disclose(persistentHashFab(
    rootFabVectorEnvironment, rootFabVectorValuesType, [first, second]))
end

noctium_circuit rootFabVectorEmptyInputs where
  output digest : Bytes32 := disclose(persistentHashFab(
    rootFabVectorEnvironment, rootFabVectorEmptyType, []))
end

noctium_contract RootFabVector where
  entry hashValues uses rootFabVectorValuesInputs where
    return digestResult : Bytes32 := digest
  end
  entry hashEmpty uses rootFabVectorEmptyInputs where
    return digestResult : Bytes32 := digest
  end
end

private def rootFabVectorContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
  persistentHash32 := fun preimage =>
    if preimage == [2, 1, 4, 3] then pure (List.replicate 32 45)
    else if preimage.isEmpty then pure (List.replicate 32 46)
    else throw "root FAB vector fixture received a different preimage"
}

#guard match (Expr.persistentHashFab rootFabVectorEnvironment rootFabVectorValuesType [
    ⟨.uint 65535, .uint 65535 258⟩,
    ⟨.uint 65535, .uint 65535 772⟩]).eval rootFabVectorContext [] with
  | .ok digest => digest == List.replicate 32 45
  | .error _ => _root_.Bool.false

#guard match (Expr.persistentHashFab rootFabVectorEnvironment rootFabVectorEmptyType []).eval
    rootFabVectorContext [] with
  | .ok digest => digest == List.replicate 32 46
  | .error _ => _root_.Bool.false

private def rootFabVectorWrongArity : Expr (.bytes 32) :=
  .persistentHashFab rootFabVectorEnvironment rootFabVectorValuesType [
    ⟨.uint 65535, .uint 65535 258⟩]

private def rootFabVectorWrongType : Expr (.bytes 32) :=
  .persistentHashFab rootFabVectorEnvironment rootFabVectorValuesType [
    ⟨.bool, .bool _root_.Bool.true⟩,
    ⟨.uint 65535, .uint 65535 772⟩]

private def rootFabVectorRejected (value : Expr (.bytes 32)) : _root_.Bool :=
  match value.validate Capabilities.source [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard rootFabVectorRejected rootFabVectorWrongArity &&
  rootFabVectorRejected rootFabVectorWrongType

private def rootFabVectorCompiled : Except LayoutDiagnostic CompiledType :=
  compileType rootFabVectorEnvironment rootFabVectorValuesType

private def rootFabVectorEmptyCompiled : Except LayoutDiagnostic CompiledType :=
  compileType rootFabVectorEnvironment rootFabVectorEmptyType

#guard match rootFabVectorCompiled with
  | .ok compiled =>
    match Helpers.Wire.fabDigestOperands compiled (.ref "payload") with
    | .ok operands => operands.map Prod.fst == [.uint 65535, .uint 65535]
    | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

#guard match rootFabVectorEmptyCompiled with
  | .ok compiled =>
    match Helpers.Wire.fabDigestOperands compiled (.ref "payload") with
    | .ok operands => operands.isEmpty
    | .error _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def rootFabVectorHelperProgram (type : CompositeType) : Except String Helpers.Program := do
  let compiled ← (Types.compileType rootFabVectorEnvironment type).mapError (·.message)
  let operands ← Helpers.Wire.fabDigestOperands compiled (.ref "payload")
  pure {
    composites := rootFabVectorEnvironment
    declarations := [{
      id := ⟨0, 0⟩
      name := "hashPayload"
      parameters := [{name := "payload", ty := .native}]
      compositeParameters := [("payload", type)]
      result := .scalar (.bytes 32)
      body := [.return (some (.bytes
        (.fabDigest .persistentHash type (operands.map Prod.fst))
        (operands.map Prod.snd)))]
    }]
    exports := [{
      name := "hashPayload"
      target := ⟨0, 0⟩
      compositeInputs := [{name := "payload", type, visibility := .public}]
    }]
  }

private def rootFabVectorHelperCompiles (type : CompositeType) : _root_.Bool :=
  match rootFabVectorHelperProgram type with
  | .error _ => _root_.Bool.false
  | .ok program => (Helpers.compile program "hashPayload").isOk

#guard rootFabVectorHelperCompiles rootFabVectorValuesType &&
  rootFabVectorHelperCompiles rootFabVectorEmptyType

#guard Backend.Native.persistentHashFabTerm [] [] ==
  Backend.Native.fixedByteHashTerm "persistent_hash" 0 []

#guard Backend.Native.fabByteHashTerm "sha512" [] [] ==
  Backend.Native.fixedByteHashTerm "sha512" 0 []

#guard Backend.Native.fabByteHashTerm "keccak256" [] [] ==
  Backend.Native.fixedByteHashTerm "keccak256" 0 []
