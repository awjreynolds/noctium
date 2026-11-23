import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit nestedRecordListPushInputs where
  private first : Native
  private active : Bool
  private tag : Native
end

noctium_circuit nestedRecordListNoInputs where
end

noctium_contract NestedRecordList where
  list records : struct Envelope {
    memo : struct Inner {
      first : Native
      active : Bool
    }
    tag : Native
  }

  entry push uses nestedRecordListPushInputs arguments [first, active, tag] where
    pushFront records := fields(disclose(first), disclose(active), disclose(tag))
  end

  entry head uses nestedRecordListNoInputs where
    headOrDefault records as (present, head)
    returnMaybe head as (present, head)
  end

  entry pop uses nestedRecordListNoInputs where
    popFront records
  end
end

#guard (NestedRecordList.validate Capabilities.source).isOk

/-- error: nested List record fields produce duplicate physical names -/
#guard_msgs in
noctium_contract NestedRecordListCollision where
  list records : struct Envelope {
    memo : struct Inner {
      first : Native
    }
    memo_first : Native
  }
end

/-- error: nested List record fields must be Native or Bool -/
#guard_msgs in
noctium_contract NestedRecordListWrongLeaf where
  list records : struct Envelope {
    memo : struct Inner {
      first : UInt 16
    }
    tag : Native
  }
end

/-- error: nested List records support one nested level -/
#guard_msgs in
noctium_contract NestedRecordListTooDeep where
  list records : struct Envelope {
    memo : struct Middle {
      inner : struct Inner {
        first : Native
      }
    }
    tag : Native
  }
end

private def nestedRecordListUndisclosedEntry : Entrypoint := {
  name := "privateProbe"
  circuit := {name := "privateProbe", inputs := [
    {name := "first", ty := .native, visibility := .«private»},
    {name := "active", ty := .bool, visibility := .«private»},
    {name := "tag", ty := .native, visibility := .«private»}]}
  effects := [.listPushFront "records" [] (.structure "NestedRecordList.Envelope") [
    .mk .native (.ref "first"), .mk .bool (.ref "active"), .mk .native (.ref "tag")]]
  effectSpans := [{}]
}

#guard match Disclosure.entrypoint nestedRecordListUndisclosedEntry with
  | .error diagnostic =>
      diagnostic.message.contains "undisclosed private parameter 'first'" &&
        diagnostic.message.contains "public List push field 0 of 'records'"
  | .ok _ => _root_.Bool.false

private def nestedRecordListBadPayloadEntry : Entrypoint := {
  name := "badPayload"
  circuit := {name := "badPayload"}
  effects := [.listPushFront "records" [] (.structure "NestedRecordList.Envelope") [
    .mk .native (.native 11), .mk .bool (.bool _root_.Bool.true)]]
  effectSpans := [{}]
}

#guard match Backend.Impact.lower NestedRecordList.state nestedRecordListBadPayloadEntry with
  | .error diagnostic => diagnostic.message.contains "list push record field type mismatch"
  | .ok _ => _root_.Bool.false
