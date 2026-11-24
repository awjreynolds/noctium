import Noctium.Frontend

open scoped Noctium

noctium_circuit inspectRecordSetInputs where
  public tag : Bytes 1
  public firstId : Bytes 33
  public lateId : Bytes 33
end

noctium_contract RecordSetConstructor where
  set members : struct Key {
    tag : Bytes 1
    id : Bytes 33
  }

  constructor(enabled : Bool, tag : Bytes 1, firstId : Bytes 33, lateId : Bytes 33) where
    insert members[fields(tag, firstId)]
    when enabled insert members[fields(tag, lateId)]
    when enabled insert members[fields(tag, lateId)]
  end

  entry inspect uses inspectRecordSetInputs where
    member members[fields(tag, firstId)] as firstPresent
    member members[fields(tag, lateId)] as latePresent
    size members as memberCount
    return first : Bool := firstPresent
    return late : Bool := latePresent
    return count : UInt 64 := memberCount
  end
end
