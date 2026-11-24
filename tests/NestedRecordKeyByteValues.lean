import Noctium.Frontend
import Noctium.Backend.Zkir

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
