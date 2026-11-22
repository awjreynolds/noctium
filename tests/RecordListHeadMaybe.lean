import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit recordListHeadMaybeNoInputs where
end

noctium_contract RecordListHeadMaybe where
  list inbox : struct Memo {
    first : Native
    second : Native
  }

  entry seed uses recordListHeadMaybeNoInputs where
    pushFront inbox := fields(17, 23)
  end

  entry peek uses recordListHeadMaybeNoInputs where
    headOrDefault inbox as (present, payload)
    returnMaybe head as (present, payload)
  end
end

#guard RecordListHeadMaybe.entrypoints.map (·.name) == ["seed", "peek"]

/-- error: returnMaybe payload must reference a scalar binding -/
#guard_msgs in
noctium_contract RecordListHeadMaybeMismatchedPair where
  list inbox : struct Memo {
    first : Native
    second : Native
  }

  entry peek uses recordListHeadMaybeNoInputs where
    headOrDefault inbox as (present, payload)
    headOrDefault inbox as (otherPresent, otherPayload)
    returnMaybe head as (otherPresent, payload)
  end
end
