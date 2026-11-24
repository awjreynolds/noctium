import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit twoParentRecordKeyStoreInputs where
  public owner : Bytes 32
  public group : Bytes 32
  public tag : Bytes 1
  public id : Bytes 33
  public label : Bytes 1
  public digest : Bytes 33
end

noctium_circuit twoParentRecordKeyLookupInputs where
  public owner : Bytes 32
  public group : Bytes 32
  public tag : Bytes 1
  public id : Bytes 33
end

noctium_contract NestedTwoParentRecordKeyValues where
  tree profiles : Bytes 32 => Bytes 32 => struct ProfileKey {
    tag : Bytes 1
    id : Bytes 33
  } => struct Profile {
    label : Bytes 1
    digest : Bytes 33
  }

  entry store uses twoParentRecordKeyStoreInputs where
    member profiles[owner] as ownerPresent
    when eq(ownerPresent, false) insertDefault profiles[owner]
    member profiles[owner][group] as groupPresent
    when eq(groupPresent, false) insertDefault profiles[owner][group]
    insert profiles[owner][group][fields(tag, id)] := fields(label, digest)
  end

  entry lookup uses twoParentRecordKeyLookupInputs where
    read profiles[owner][group][fields(tag, id)] as profile
    return label : Bytes 1 := profile_label
    return digest : Bytes 33 := profile_digest
  end

  entry «remove» uses twoParentRecordKeyLookupInputs where
    remove profiles[owner][group][fields(tag, id)]
  end
end

#guard (NestedTwoParentRecordKeyValues.validate Capabilities.source).isOk
#guard NestedTwoParentRecordKeyValues.entrypoints.all fun operation =>
  (Backend.Zkir.lowerEntrypoint NestedTwoParentRecordKeyValues.state operation).isOk
