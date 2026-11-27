import Noctium.Frontend

open scoped Noctium
open Noctium

private def vectorWire : Helpers.Wire.Codec := {
  payload := .vector 2 (.scalar (.uint 255))
  frameBytes := 2
}

private def tupleWire : Helpers.Wire.Codec := {
  payload := .tuple [.scalar (.uint 255), .scalar (.uint 65535)]
  frameBytes := 3
}

noctium_witness vectorArm() : Payload vectorWire
noctium_witness tupleArm() : Payload tupleWire

noctium_witness_circuit selectMixed using vectorWire, tupleWire where
  public choice : Bool
  let selected := if choice then witness vectorArm() else witness tupleArm()
  output result := disclose(selected)
end

/- error: conditional branches require a common type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectDifferentArity using vectorWire where
  public choice : Bool
  let selected := if choice then witness vectorArm() else tuple(uint(7))
  output result := disclose(selected)
end

/- error: conditional branches require a common type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectIncomparableBounds using vectorWire where
  public choice : Bool
  public nibble : UInt 4
  public wide : UInt 16
  let selected := if choice then witness vectorArm() else tuple(nibble, wide)
  output result := disclose(selected)
end

noctium_contract MixedSequenceJoin where
  entry choose uses selectMixed where
    return result
  end
end
