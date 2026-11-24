import Noctium.Frontend

open scoped Noctium

noctium_circuit rootFixedByteRecordSetInputs where
  public tag : Bytes 1
  public firstId : Bytes 33
  public lateId : Bytes 33
end

noctium_contract RootFixedByteRecordSet where
  set members : struct Key {
    tag : Bytes 1
    id : Bytes 33
  }

  entry update uses rootFixedByteRecordSetInputs where
    insert members[fields(tag, firstId)]
    insert members[fields(tag, lateId)]
    member members[fields(tag, firstId)] as firstBefore
    member members[fields(tag, lateId)] as lateBefore
    remove members[fields(tag, firstId)]
    member members[fields(tag, firstId)] as firstRemaining
    member members[fields(tag, lateId)] as lateRemaining
    size members as remaining
    return first : Bool := firstBefore
    return late : Bool := lateBefore
    return firstAfter : Bool := firstRemaining
    return lateAfter : Bool := lateRemaining
    return count : UInt 64 := remaining
  end
end
