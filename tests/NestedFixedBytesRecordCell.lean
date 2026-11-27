import Noctium.Frontend

open scoped Noctium

noctium_circuit nestedFixedBytesRecordWriteInputs where
  private payloadArg : Bytes 40
  private markerArg : Native
  private counterArg : UInt 64
end

noctium_circuit nestedFixedBytesRecordNoInputs where
end

noctium_contract NestedFixedBytesRecordCell where
  cell record : struct NestedRecord {
    nested : struct FixedBytesRecord {
      payload : Bytes 40
      marker : Native
    }
    count : UInt 64
  }

  constructor() where
  end

  entry writeRecord uses nestedFixedBytesRecordWriteInputs
      arguments [payloadArg, markerArg, counterArg] where
    write record := fields(disclose(payloadArg), disclose(markerArg), disclose(counterArg))
  end

  entry inspect uses nestedFixedBytesRecordNoInputs where
    read record as observed
    return payloadResult : Bytes 40 := observed_nested_payload
    return markerResult : Native := observed_nested_marker
    return counterResult : UInt 64 := observed_count
  end

  entry clearRecord uses nestedFixedBytesRecordNoInputs where
    reset record
  end
end
