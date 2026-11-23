import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit vectorMapKeyInputs where
  private first : Native
  private second : Native
  private third : Native
end

noctium_circuit vectorMapNoInputs where
end

noctium_circuit vectorMapPrivateInputs where
  private first : Native
  private second : Native
end

noctium_contract VectorMapKeys where
  map vectorValues : Vector(2, Native) => Native

  entry update uses vectorMapKeyInputs arguments [first, second, third] where
    insert vectorValues[fields(disclose(first), disclose(second))] := 101
    insert vectorValues[fields(disclose(first), disclose(third))] := 303
    insert vectorValues[fields(disclose(first), disclose(second))] := 202
    member vectorValues[fields(disclose(first), disclose(second))] as presentA
    member vectorValues[fields(disclose(first), disclose(third))] as presentB
    size vectorValues as mapSize
    return memberA : Bool := presentA
    return memberB : Bool := presentB
    return size : UInt 64 := mapSize
  end

  entry lookup uses vectorMapKeyInputs arguments [first, second, third] where
    member vectorValues[fields(disclose(first), disclose(second))] as presentA
    member vectorValues[fields(disclose(first), disclose(third))] as presentB
    member vectorValues[fields(disclose(second), disclose(third))] as presentMissing
    when presentA read vectorValues[fields(disclose(first), disclose(second))] as storedA
    when presentB read vectorValues[fields(disclose(first), disclose(third))] as storedB
    when presentMissing read vectorValues[fields(disclose(second), disclose(third))] as storedMissing
    return lookupA : Native := storedA
    return lookupB : Native := storedB
    return lookupMissing : Native := storedMissing
  end

  entry «member» uses vectorMapKeyInputs arguments [first, second, third] where
    member vectorValues[fields(disclose(first), disclose(second))] as presentA
    member vectorValues[fields(disclose(first), disclose(third))] as presentB
    member vectorValues[fields(disclose(second), disclose(third))] as presentMissing
    return memberA : Bool := presentA
    return memberB : Bool := presentB
    return memberMissing : Bool := presentMissing
  end

  entry «size» uses vectorMapNoInputs arguments [] where
    size vectorValues as mapSize
    return size : UInt 64 := mapSize
  end

  entry «remove» uses vectorMapKeyInputs arguments [first, second, third] where
    remove vectorValues[fields(disclose(first), disclose(second))]
    member vectorValues[fields(disclose(first), disclose(second))] as presentA
    member vectorValues[fields(disclose(first), disclose(third))] as presentB
    when presentA read vectorValues[fields(disclose(first), disclose(second))] as storedA
    size vectorValues as mapSize
    return memberA : Bool := presentA
    return memberB : Bool := presentB
    return lookupA : Native := storedA
    return size : UInt 64 := mapSize
  end
end

#guard (VectorMapKeys.validate Capabilities.source).isOk

private def vectorMapKeyEntry (name : String) : Entrypoint :=
  (VectorMapKeys.entrypoints.find? (·.name == name)).getD
    {name := "missing", circuit := {name := "missing"}}

#guard ((vectorMapKeyEntry "update").validate Capabilities.source VectorMapKeys.state).isOk
#guard ((vectorMapKeyEntry "lookup").validate Capabilities.source VectorMapKeys.state).isOk
#guard ((vectorMapKeyEntry "member").validate Capabilities.source VectorMapKeys.state).isOk
#guard ((vectorMapKeyEntry "size").validate Capabilities.source VectorMapKeys.state).isOk
#guard ((vectorMapKeyEntry "remove").validate Capabilities.source VectorMapKeys.state).isOk

#guard match VectorMapKeys.state with
  | [{kind := .tree (.recordMapKey environment (.vector 2 (.scalar .native)) .native), ..}] =>
      match LedgerValueType.ledgerRecordWriteFields environment (.vector 2 (.scalar .native)) with
      | .ok fields => fields == [("0_value", .native), ("1_value", .native)]
      | .error _ => _root_.Bool.false
  | _ => _root_.Bool.false

/-- ledger record field count does not match its checked layout -/
#guard_msgs (substring := true) in
noctium_contract VectorMapWrongWidth where
  map vectorValues : Vector(2, Native) => Native

  entry update uses vectorMapKeyInputs arguments [first, second, third] where
    insert vectorValues[fields(first)] := 101
  end
end

/-- root Map vector keys require Native elements -/
#guard_msgs (substring := true) in
noctium_contract VectorMapWrongElement where
  map vectorValues : Vector(2, Bool) => Native
end

/-- undisclosed private parameter 'first' -/
#guard_msgs (substring := true) in
noctium_contract VectorMapUndisclosed where
  map vectorValues : Vector(2, Native) => Native

  entry update uses vectorMapPrivateInputs where
    insert vectorValues[fields(first, second)] := 101
  end
end
