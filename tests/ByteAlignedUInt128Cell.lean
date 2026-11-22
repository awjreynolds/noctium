import Noctium.Backend.Impact
import Noctium.Frontend

open Noctium
open Noctium.Backend.Impact
open scoped Noctium

noctium_circuit uint128CellInput where
  public amount : UInt 128
  public enabled : Bool
end

noctium_contract ByteAlignedUInt128Cell where
  cell totalSupply : UInt 128 alignedBytes
  cell ordinary : UInt 128
  constructor() where
    initialize totalSupply := 0
  end
  entry update uses uint128CellInput where
    read totalSupply as previous
    when enabled write totalSupply := disclose(amount)
    when enabled read totalSupply as current
    return previousAmount : UInt 128 := previous
    return currentAmount : UInt 128 := current
  end
end

private def uint128Maximum := 2 ^ 128 - 1

private def uint128Entry : Entrypoint :=
  ByteAlignedUInt128Cell.entrypoints.headD {name := "missing", circuit := {name := "missing"}}

private def uint128Context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
}

private def runUInt128Update (amount initial : Nat) :=
  uint128Entry.run uint128Context [
    ("amount", .uint uint128Maximum amount), ("enabled", .bool _root_.Bool.true)] {
    cells := [("totalSupply", .uint uint128Maximum initial)]
  }

#guard match ByteAlignedUInt128Cell.state with
  | [aligned, ordinary] =>
      aligned.kind == .cell (.uint uint128Maximum) && aligned.cellAlignment? == some .u128 &&
        ordinary.kind == .cell (.uint uint128Maximum) && ordinary.cellAlignment? == none
  | _ => _root_.Bool.false
#guard match ByteAlignedUInt128Cell.constructor with
  | some ctor =>
      match ctor.initializers with
      | [initializer] =>
          match initializer.type, initializer.value with
          | .scalar (.uint maximum), .scalar (.uint valueMaximum value) =>
              initializer.state == "totalSupply" && maximum == uint128Maximum &&
                valueMaximum == uint128Maximum && value == 0
          | _, _ => _root_.Bool.false
      | _ => _root_.Bool.false
  | none => _root_.Bool.false

private def hasU128FieldEncoding (value : Nat) : _root_.Bool :=
  match (Aligned.u128 (.uint uint128Maximum value)).fields with
  | [.native 1, .native 16, .cast .native (.uint maximum encoded)] =>
      maximum == uint128Maximum && encoded == value
  | _ => _root_.Bool.false

private def expectedU128AlignedJson (atoms : List (List Nat)) : Lean.Json :=
  Lean.Json.mkObj [
    ("value", Lean.toJson atoms),
    ("alignment", Lean.Json.arr #[Lean.Json.mkObj [
      ("tag", Lean.toJson ("atom" : String)),
      ("value", Lean.Json.mkObj [
        ("tag", Lean.toJson ("bytes" : String)),
        ("length", Lean.toJson (16 : Nat))])]])]

private def hasCanonicalU128AlignedJson (value : Nat) (atoms : List (List Nat)) : _root_.Bool :=
  match (Aligned.u128 (.uint uint128Maximum value)).toJson uint128Context [] with
  | .ok json => json == expectedU128AlignedJson atoms
  | .error _ => _root_.Bool.false

#guard hasU128FieldEncoding 0
#guard hasU128FieldEncoding uint128Maximum
#guard hasCanonicalU128AlignedJson 0 [[]]
#guard hasCanonicalU128AlignedJson uint128Maximum [List.replicate 16 255]

#guard match runUInt128Update 0 0 with
  | .ok ([ ("previousAmount", .uint maximum 0), ("currentAmount", .uint _ 0) ], state) =>
      maximum == uint128Maximum && state.cells.lookup "totalSupply" == some (.uint uint128Maximum 0)
  | _ => _root_.Bool.false

#guard match runUInt128Update uint128Maximum 0 with
  | .ok ([ ("previousAmount", .uint maximum 0), ("currentAmount", .uint _ current) ], state) =>
      maximum == uint128Maximum && current == uint128Maximum &&
        state.cells.lookup "totalSupply" == some (.uint uint128Maximum uint128Maximum)
  | _ => _root_.Bool.false
