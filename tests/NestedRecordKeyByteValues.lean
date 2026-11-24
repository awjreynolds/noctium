import Noctium.Frontend
import Noctium.Backend.LedgerReadOptimization

open scoped Noctium
open Noctium

noctium_circuit nestedRecordKeyByteStoreInputs where
  public owner : Bytes 32
  public tag : Bytes 1
  public id : Bytes 33
  public label : Bytes 1
  public digest : Bytes 33
end

noctium_circuit nestedRecordKeyByteLookupInputs where
  public owner : Bytes 32
  public tag : Bytes 1
  public id : Bytes 33
end

noctium_contract NestedRecordKeyByteValues where
  tree profiles : Bytes 32 => struct ProfileKey {
    tag : Bytes 1
    id : Bytes 33
  } => struct Profile {
    label : Bytes 1
    digest : Bytes 33
  }

  entry store uses nestedRecordKeyByteStoreInputs where
    member profiles[owner] as ownerPresent
    when eq(ownerPresent, false) insertDefault profiles[owner]
    insert profiles[owner][fields(tag, id)] := fields(label, digest)
  end

  entry lookup uses nestedRecordKeyByteLookupInputs where
    read profiles[owner][fields(tag, id)] as profile
    return label : Bytes 1 := profile_label
    return digest : Bytes 33 := profile_digest
  end

  entry «remove» uses nestedRecordKeyByteLookupInputs where
    remove profiles[owner][fields(tag, id)]
  end
end

#guard (NestedRecordKeyByteValues.validate Capabilities.source).isOk
#guard NestedRecordKeyByteValues.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint NestedRecordKeyByteValues.state operation).isOk

#guard match Backend.LedgerReadOptimization.lowerRecordMap
    NestedRecordKeyByteValues "lookup" "profile" with
  | .ok operation => operation.certificate.fieldWidths == [1, 33] &&
      operation.certificate.chunks ==
        [("%input__noctium_bytes_profile_label_0", 8),
         ("%input__noctium_bytes_profile_digest_0", 16),
         ("%input__noctium_bytes_profile_digest_1", 248)]
  | .error _ => _root_.Bool.false

private def guardedRecordKeyByteLookup : Contract :=
  {NestedRecordKeyByteValues with entrypoints :=
    NestedRecordKeyByteValues.entrypoints.map fun operation =>
      if operation.name == "lookup" then
        {operation with effectGuards := [some (.bool _root_.Bool.true)]}
      else operation}

#guard match Backend.LedgerReadBound.checkRecordMap guardedRecordKeyByteLookup "lookup" "profile" with
  | .error message => message == "guarded record Map reads do not have unconditional byte bounds"
  | .ok _ => _root_.Bool.false
