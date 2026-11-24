import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit constructorBytePatternNoInputs where
end

noctium_contract ConstructorBytePattern where
  cell first : UInt 8
  cell last : UInt 8
  constructor(source : Bytes 3 as [firstByte, _, lastByte]) where
    initialize first := firstByte
    initialize last := lastByte
  end
  entry inspect uses constructorBytePatternNoInputs where
    read first as firstValue
    read last as lastValue
    return firstResult : UInt 8 := firstValue
    return lastResult : UInt 8 := lastValue
  end
end

#guard match ConstructorBytePattern.constructor with
  | some ctor =>
      match ctor.parameters, ctor.initializers with
      | [{name := "source", type := .scalar (.bytes 3)}], [first, last] =>
          first.state == "first" && last.state == "last" &&
          match first.value, last.value with
          | .scalar (.bytesAt (.ref "source") 0), .scalar (.bytesAt (.ref "source") 2) => _root_.Bool.true
          | _, _ => _root_.Bool.false
      | _, _ => _root_.Bool.false
  | none => _root_.Bool.false

/- error: byte constructor pattern requires exactly 3 items -/
#guard_msgs (substring := true) in
noctium_contract RejectsShortConstructorBytePattern where
  constructor(source : Bytes 3 as [firstByte, lastByte]) where
  end
end

/- error: duplicate constructor parameter or byte binding 'source' -/
#guard_msgs (substring := true) in
noctium_contract RejectsConstructorBytePatternCollision where
  constructor(source : Bytes 3 as [source, _, lastByte]) where
  end
end

/-- error: duplicate constructor parameter 'other' -/
#guard_msgs (substring := true) in
noctium_contract RejectsLaterConstructorBytePatternCollision where
  constructor(source : Bytes 1 as [other], other : UInt 8) where
  end
end

/-- error: byte constructor patterns require a fixed Bytes parameter -/
#guard_msgs (substring := true) in
noctium_contract RejectsNonByteConstructorPattern where
  constructor(source : Bool as [firstByte]) where
  end
end
