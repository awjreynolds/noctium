import Noctium.Verification.GenericStateInputValues

open Noctium.Verification.NativeRelation
open Noctium.Verification.GenericStateInputValues

private def scalarReadCandidates : List Noctium.Backend.Impact.Read :=
  [{name := "nativeRead", ty := .native},
   {name := "boolRead", ty := .bool},
   {name := "uintRead", ty := .uint 31}]

private def scalarReadWitness : Assignment := fun name =>
  if name == "%input_nativeRead" then scalar 17 else
  if name == "%input_boolRead" then one else
  if name == "%input_uintRead" then scalar 23 else zero

#guard match decodeReads scalarReadCandidates scalarReadWitness with
  | .ok values =>
    values == [("nativeRead", .native 17), ("boolRead", .bool true),
      ("uintRead", .uint 31 23)]
  | .error _ => false

#guard match decodeReads [{name := "bytesRead", ty := .bytes 32}] scalarReadWitness with
  | .error message => message == "unsupported non-scalar read type"
  | .ok _ => false
