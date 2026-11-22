import Noctium.Verification.GenericStateEncoding

open Noctium Noctium.Verification.NativeRelation
open Noctium.Verification.NativeState
open Noctium.Verification.GenericStateEncoding

private def declarations : List StateDecl := [
  {name := "quota", kind := .cell (.uint 5)},
  {name := "active", kind := .cell .bool},
  {name := "head", kind := .cell .native}
]

private def initialState : LedgerState := {
  cells := [
    ("head", .native 17),
    ("active", .bool true),
    ("quota", .uint 5 4)
  ]
}

-- Slots follow declaration order, independent of association-list order.
#guard decide (encodeInitialState declarations initialState = some [
  .cell (field (scalar 4)), .cell (field one), .cell (field (scalar 17))
])

-- Both native-field and bounded-UInt canonical checks run before admission.
#guard decide (encodeInitialState [{name := "head", kind := .cell .native}]
  {cells := [("head", .native Field.modulus)]} = none)
#guard decide (encodeInitialState [{name := "quota", kind := .cell (.uint 5)}]
  {cells := [("quota", .uint 5 6)]} = none)

-- Unsupported declarations reject even when a map has no entries.
#guard decide (encodeInitialState [{name := "raw", kind := .cell (.bytes 1)}]
  {cells := [("raw", .bytes 1 [7])]} = none)
#guard decide (encodeState [{name := "empty", kind := .map (.bytes 1) .native}]
  {maps := [("empty", [])]} = some [.map []])
#guard decide (encodeInitialState [{name := "empty", kind := .map (.bytes 1) .native}]
  {maps := [("empty", [])]} = none)
#guard decide (encodeInitialState [{name := "tree", kind := .tree .counter}] ({} : LedgerState) = none)

-- The checked conversion rejects unmodeled roots and duplicate association keys.
#guard decide (encodeInitialState [] {cells := [("extra", .native 1)]} = none)
#guard decide (encodeInitialState [] {maps := [("extra", [])]} = none)
#guard decide (encodeInitialState [] {trees := [("extra", .null)]} = none)
#guard decide (encodeInitialState declarations {initialState with
  cells := initialState.cells ++ [("extra", .native 1)]} = none)
#guard decide (encodeInitialState declarations {initialState with
  cells := [("head", .native 1), ("head", .native 2), ("active", .bool true)]} = none)
#guard decide (encodeInitialState [
  {name := "same", kind := .cell .native},
  {name := "same", kind := .cell .bool}
] {cells := [("same", .native 1), ("same", .bool true)]} = none)
#guard decide (encodeInitialState declarations {initialState with
  events := [(.paused, [])], shieldedMints := [([], 1)]} = none)
