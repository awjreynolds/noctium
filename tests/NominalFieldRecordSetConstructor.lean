import Noctium.Frontend

open scoped Noctium
open Noctium

namespace NominalFieldRecordSetConstructor

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_circuit lookupInputs where
  public amount : Amount
end

noctium_contract Registry where
  sealed set members : struct Key {
    amount : Amount
  }

  constructor(seed : Amount, extra : Native, enabled : Bool) where
    insert members[fields(seed)]
    when enabled insert members[fields(cast(Amount, extra))]
  end

  entry inspect uses lookupInputs where
    member members[fields(amount)] as present
    return isPresent : Bool := present
  end
end

#guard (Registry.validate Capabilities.source).isOk

#guard match Registry.constructor with
  | some ctor => match ctor.actions with
    | [.insertRecordSet "members" [first] none,
       .insertRecordSet "members" [second] (some (.ref "enabled"))] =>
        first.ty == .native && second.ty == .native
    | _ => _root_.Bool.false
  | none => _root_.Bool.false

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectRawKey where
  sealed set members : struct Key {
    amount : Amount
  }

  constructor(seed : Native) where
    insert members[fields(seed)]
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_contract RejectWrongAlias where
  sealed set members : struct Key {
    amount : Amount
  }

  constructor(seed : Count, enabled : Bool) where
    when enabled insert members[fields(seed)]
  end
end

end NominalFieldRecordSetConstructor
