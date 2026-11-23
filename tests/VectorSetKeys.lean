import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit vectorSetKeyInputs where
  private first : Native
  private second : Native
  private third : Native
end

noctium_circuit vectorSetNoInputs where
end

noctium_circuit vectorSetPrivateInputs where
  private first : Native
  private second : Native
end

noctium_contract VectorSetKeys where
  set vectorKeys : Vector(2, Native)

  entry update uses vectorSetKeyInputs arguments [first, second, third] where
    insert vectorKeys[fields(disclose(first), disclose(second))]
    insert vectorKeys[fields(disclose(first), disclose(third))]
    insert vectorKeys[fields(disclose(second), disclose(first))]
    insert vectorKeys[fields(disclose(first), disclose(second))]
    member vectorKeys[fields(disclose(first), disclose(second))] as memberA
    member vectorKeys[fields(disclose(first), disclose(third))] as memberB
    member vectorKeys[fields(disclose(second), disclose(first))] as memberC
    size vectorKeys as setSize
    return containsA : Bool := memberA
    return containsB : Bool := memberB
    return containsC : Bool := memberC
    return keyCount : UInt 64 := setSize
  end

  entry «remove» uses vectorSetKeyInputs arguments [first, second, third] where
    remove vectorKeys[fields(disclose(first), disclose(second))]
    member vectorKeys[fields(disclose(first), disclose(second))] as memberA
    member vectorKeys[fields(disclose(first), disclose(third))] as memberB
    member vectorKeys[fields(disclose(second), disclose(first))] as memberC
    size vectorKeys as setSize
    return containsA : Bool := memberA
    return containsB : Bool := memberB
    return containsC : Bool := memberC
    return keyCount : UInt 64 := setSize
  end

  entry «reset» uses vectorSetNoInputs arguments [] where
    reset vectorKeys
    size vectorKeys as setSize
    isEmpty vectorKeys as wasEmpty
    return keyCount : UInt 64 := setSize
    return isEmpty : Bool := wasEmpty
  end
end

#guard (VectorSetKeys.validate Capabilities.source).isOk

/-- ledger record field count does not match its checked layout -/
#guard_msgs (substring := true) in
noctium_contract VectorSetWrongWidth where
  set vectorKeys : Vector(2, Native)

  entry update uses vectorSetKeyInputs arguments [first, second, third] where
    insert vectorKeys[fields(first)]
  end
end

/-- root Set vectors require Native elements -/
#guard_msgs (substring := true) in
noctium_contract VectorSetWrongElement where
  set vectorKeys : Vector(2, Bool)
end

/-- undisclosed private parameter 'first' -/
#guard_msgs (substring := true) in
noctium_contract VectorSetUndisclosed where
  set vectorKeys : Vector(2, Native)

  entry update uses vectorSetPrivateInputs where
    insert vectorKeys[fields(first, second)]
  end
end
