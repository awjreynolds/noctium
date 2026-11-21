#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, artifacts,
    collection_ffi::noctium_ledger_collection_page,
    field_value,
    native_ffi::{
        INVALID_ARGUMENT, OK, noctium_native_result_copy, noctium_native_result_free,
        noctium_native_result_length,
    },
};
use onchain_runtime::state::{ChargedState, ContractState, StateValue};
use serde_json::{Value, json};
use serialize::tagged_serialize;
use std::sync::Mutex;
use storage::{arena::Sp, storage::HashMap};
use transient_crypto::curve::Fr;

// Keep the pagination cases within the shared native ABI work limit.
static PAGE_TESTS: Mutex<()> = Mutex::new(());

struct Snapshot {
    plan: Vec<u8>,
    state: Vec<u8>,
}

impl Snapshot {
    fn new(plan: Value, state: ChargedState<Db>) -> Self {
        let mut contract = ContractState::<Db>::default();
        contract.data = state;
        let mut state_bytes = Vec::new();
        tagged_serialize(&contract, &mut state_bytes).unwrap();
        Self {
            plan: serde_json::to_vec(&plan).unwrap(),
            state: state_bytes,
        }
    }

    fn page(&self, name: &str, offset: usize, limit: usize) -> Value {
        self.page_at(name, Vec::new(), offset, limit)
    }

    fn page_at(&self, name: &str, keys: Vec<Value>, offset: usize, limit: usize) -> Value {
        let request = serde_json::to_vec(&json!({
            "abiVersion": 1,
            "planSha256": artifacts::digest(&self.plan),
            "stateSha256": artifacts::digest(&self.state),
            "name": name,
            "keys": keys,
            "offset": offset,
            "limit": limit,
        }))
        .unwrap();
        let mut token = 0;
        unsafe {
            assert_eq!(
                noctium_ledger_collection_page(
                    request.as_ptr(),
                    request.len(),
                    self.plan.as_ptr(),
                    self.plan.len(),
                    self.state.as_ptr(),
                    self.state.len(),
                    &mut token,
                ),
                OK
            );
            let mut length = 0;
            assert_eq!(noctium_native_result_length(token, &mut length), OK);
            let mut output = vec![0; length];
            let mut written = 0;
            assert_eq!(
                noctium_native_result_copy(token, output.as_mut_ptr(), length, &mut written),
                OK
            );
            assert_eq!(written, length);
            assert_eq!(noctium_native_result_free(token), OK);
            serde_json::from_slice(&output).unwrap()
        }
    }

    fn status(&self, name: &str, offset: usize, limit: usize, state_sha256: &str) -> i32 {
        self.status_at(name, Vec::new(), offset, limit, state_sha256)
    }

    fn status_at(
        &self,
        name: &str,
        keys: Vec<Value>,
        offset: usize,
        limit: usize,
        state_sha256: &str,
    ) -> i32 {
        let request = serde_json::to_vec(&json!({
            "abiVersion": 1,
            "planSha256": artifacts::digest(&self.plan),
            "stateSha256": state_sha256,
            "name": name,
            "keys": keys,
            "offset": offset,
            "limit": limit,
        }))
        .unwrap();
        let mut token = 0;
        let status = unsafe {
            noctium_ledger_collection_page(
                request.as_ptr(),
                request.len(),
                self.plan.as_ptr(),
                self.plan.len(),
                self.state.as_ptr(),
                self.state.len(),
                &mut token,
            )
        };
        if status == OK {
            assert_eq!(noctium_native_result_free(token), OK);
        } else {
            assert_eq!(token, 0);
        }
        status
    }
}

fn bytes32_key(value: u8) -> Value {
    json!({"type":"Bytes<32>","value":{"kind":"bytes","values":vec![value;32]}})
}

fn native_key(value: u64) -> Value {
    json!({"type":"Native","value":value.to_string()})
}

fn plan(state: Vec<Value>) -> Value {
    let provenance: Value = serde_json::from_str(include_str!(
        "fixtures/issue65/PrivateClaim.claim-321.impact.json"
    ))
    .unwrap();
    json!({
        "schemaVersion": 1,
        "target": provenance["target"],
        "targetProfile": provenance["targetProfile"],
        "state": state,
        "operations": [],
    })
}

fn map_set_snapshot(reverse: bool) -> Snapshot {
    let mut map_entries = vec![(10u64, 1u64), (2, 0), (1, 1)];
    let mut set_entries = vec![[9u8; 32], [1; 32], [4; 32]];
    if reverse {
        map_entries.reverse();
        set_entries.reverse();
    }
    let map = map_entries
        .into_iter()
        .fold(HashMap::new(), |map, (key, value)| {
            map.insert(
                field_value(Fr::from(key)),
                StateValue::Cell(Sp::new(field_value(Fr::from(value)))),
            )
        });
    let set = set_entries.into_iter().fold(HashMap::new(), |set, key| {
        set.insert(AlignedValue::from(key), StateValue::Null)
    });
    let state = ChargedState::new(StateValue::Array(
        vec![StateValue::Map(map), StateValue::Map(set)].into(),
    ));
    Snapshot::new(
        plan(vec![
            json!({"name":"flags","kind":{"map":["Native","Bool"]}}),
            json!({"name":"members","kind":{"tree":{"set":"Bytes<32>"}}}),
        ]),
        state,
    )
}

fn scalar_list(values: &[u64]) -> StateValue<Db> {
    let mut list = StateValue::Array(
        vec![
            StateValue::Null,
            StateValue::Null,
            StateValue::Cell(Sp::new(AlignedValue::from(0u64))),
        ]
        .into(),
    );
    for (index, value) in values.iter().enumerate().rev() {
        list = StateValue::Array(
            vec![
                StateValue::Cell(Sp::new(field_value(Fr::from(*value)))),
                list,
                StateValue::Cell(Sp::new(AlignedValue::from((values.len() - index) as u64))),
            ]
            .into(),
        );
    }
    list
}

fn composite_record_schema() -> Value {
    let plan: Value = serde_json::from_str(include_str!(
        "fixtures/generic-state/issue69-composite/321/Issue69CompositeMap.update.impact.json"
    ))
    .unwrap();
    plan["state"][0]["kind"]["tree"]["map"][1]["composite"].clone()
}

fn composite_record(values: [u64; 4]) -> AlignedValue {
    let cells = values.map(|value| field_value(Fr::from(value)));
    AlignedValue::concat(cells.iter())
}

fn composite_list(values: &[[u64; 4]]) -> StateValue<Db> {
    let mut list = StateValue::Array(
        vec![
            StateValue::Null,
            StateValue::Null,
            StateValue::Cell(Sp::new(AlignedValue::from(0u64))),
        ]
        .into(),
    );
    for (index, value) in values.iter().enumerate().rev() {
        list = StateValue::Array(
            vec![
                StateValue::Cell(Sp::new(composite_record(*value))),
                list,
                StateValue::Cell(Sp::new(AlignedValue::from((values.len() - index) as u64))),
            ]
            .into(),
        );
    }
    list
}

fn composite_collection_snapshot(map_value: AlignedValue, list_values: &[[u64; 4]]) -> Snapshot {
    let record_schema = composite_record_schema();
    let map = HashMap::new().insert(
        AlignedValue::from([7u8; 32]),
        StateValue::Cell(Sp::new(map_value)),
    );
    Snapshot::new(
        plan(vec![
            json!({"name":"records","kind":{"tree":{"map":["Bytes<32>",{"composite":record_schema.clone()}]}}}),
            json!({"name":"recordList","kind":{"tree":{"list":{"composite":record_schema}}}}),
        ]),
        ChargedState::new(StateValue::Array(
            vec![StateValue::Map(map), composite_list(list_values)].into(),
        )),
    )
}

fn list_snapshot(values: &[u64]) -> Snapshot {
    Snapshot::new(
        plan(vec![
            json!({"name":"values","kind":{"tree":{"list":{"scalar":"Native"}}}}),
            json!({"name":"empty","kind":{"tree":{"list":{"scalar":"Native"}}}}),
        ]),
        ChargedState::new(StateValue::Array(
            vec![scalar_list(values), scalar_list(&[])].into(),
        )),
    )
}

fn malformed_list_snapshot() -> Snapshot {
    let tail = StateValue::Array(
        vec![
            StateValue::Cell(Sp::new(field_value(Fr::from(2u64)))),
            scalar_list(&[]),
            StateValue::Cell(Sp::new(AlignedValue::from(8u64))),
        ]
        .into(),
    );
    let list = StateValue::Array(
        vec![
            StateValue::Cell(Sp::new(field_value(Fr::from(1u64)))),
            tail,
            StateValue::Cell(Sp::new(AlignedValue::from(2u64))),
        ]
        .into(),
    );
    Snapshot::new(
        plan(vec![json!({
            "name":"values",
            "kind":{"tree":{"list":{"scalar":"Native"}}}
        })]),
        ChargedState::new(StateValue::Array(vec![list].into())),
    )
}

fn nested_collection_snapshot() -> Snapshot {
    let owner = [7u8; 32];
    let flags = [(10u64, true), (2, false), (1, true)].into_iter().fold(
        HashMap::new(),
        |map, (key, value)| {
            map.insert(
                field_value(Fr::from(key)),
                StateValue::Cell(Sp::new(field_value(Fr::from(if value { 1 } else { 0 })))),
            )
        },
    );
    let nested_flags = HashMap::new().insert(AlignedValue::from(owner), StateValue::Map(flags));

    let members = [[9u8; 32], [1; 32], [4; 32]]
        .into_iter()
        .fold(HashMap::new(), |set, member| {
            set.insert(AlignedValue::from(member), StateValue::Null)
        });
    let nested_members = HashMap::new().insert(AlignedValue::from(owner), StateValue::Map(members));
    let nested_values =
        HashMap::new().insert(AlignedValue::from(owner), scalar_list(&[11, 22, 33]));

    Snapshot::new(
        plan(vec![
            json!({"name":"nestedFlags","kind":{"tree":{"map":["Bytes<32>",{"map":["Native","Bool"]}]}}}),
            json!({"name":"nestedMembers","kind":{"tree":{"map":["Bytes<32>",{"set":"Bytes<32>"}]}}}),
            json!({"name":"nestedValues","kind":{"tree":{"map":["Bytes<32>",{"list":{"scalar":"Native"}}]}}}),
        ]),
        ChargedState::new(StateValue::Array(
            vec![
                StateValue::Map(nested_flags),
                StateValue::Map(nested_members),
                StateValue::Map(nested_values),
            ]
            .into(),
        )),
    )
}

#[test]
fn map_and_set_pages_are_typed_stable_and_bounded() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let snapshot = map_set_snapshot(false);
    let reverse = map_set_snapshot(true);

    let first_map_page = snapshot.page("flags", 0, 2);
    assert_eq!(
        first_map_page,
        json!({
            "abiVersion": 1,
            "kind": "map",
            "entries": [
                {"key":"1","value":true},
                {"key":"2","value":false}
            ],
            "nextOffset": 2
        })
    );
    assert_eq!(
        snapshot.page("flags", 2, 2),
        json!({
            "abiVersion": 1,
            "kind": "map",
            "entries": [{"key":"10","value":true}],
            "nextOffset": null
        })
    );
    assert_eq!(reverse.page("flags", 0, 2), first_map_page);
    assert_eq!(reverse.page("flags", 2, 2), snapshot.page("flags", 2, 2));

    let first_set_page = snapshot.page("members", 0, 2);
    assert_eq!(
        first_set_page,
        json!({
            "abiVersion": 1,
            "kind": "set",
            "entries": [
                {"kind":"bytes","values":vec![1u8;32]},
                {"kind":"bytes","values":vec![4u8;32]}
            ],
            "nextOffset": 2
        })
    );
    assert_eq!(reverse.page("members", 0, 2), first_set_page);
    assert_eq!(
        reverse.page("members", 2, 2),
        snapshot.page("members", 2, 2)
    );
    assert_eq!(
        snapshot.page("members", 2, 2),
        json!({
            "abiVersion": 1,
            "kind": "set",
            "entries": [{"kind":"bytes","values":vec![9u8;32]}],
            "nextOffset": null
        })
    );

    assert_eq!(
        snapshot.status("flags", 0, 2, &"0".repeat(64)),
        INVALID_ARGUMENT
    );
}

#[test]
fn scalar_list_pages_validate_count_and_empty_sentinel() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let snapshot = list_snapshot(&[11, 22, 33]);
    assert_eq!(
        snapshot.page("empty", 0, 2),
        json!({
            "abiVersion": 1,
            "kind": "list",
            "entries": [],
            "nextOffset": null
        })
    );
    assert_eq!(
        snapshot.page("values", 0, 2),
        json!({
            "abiVersion": 1,
            "kind": "list",
            "entries": ["11", "22"],
            "nextOffset": 2
        })
    );
    assert_eq!(
        snapshot.page("values", 2, 2),
        json!({
            "abiVersion": 1,
            "kind": "list",
            "entries": ["33"],
            "nextOffset": null
        })
    );

    let malformed = malformed_list_snapshot();
    assert_eq!(
        malformed.status("values", 0, 2, &artifacts::digest(&malformed.state)),
        INVALID_ARGUMENT
    );
}

#[test]
fn composite_record_map_and_list_pages_decode_checked_values() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let snapshot = composite_collection_snapshot(composite_record([1, 2, 3, 4]), &[[5, 6, 7, 8]]);
    let map_record = json!({
        "kind":"struct",
        "id":"Issue69CompositeMap.Ciphertext4",
        "fields":[
            {"name":"c1x","value":{"kind":"native","value":"1"}},
            {"name":"c1y","value":{"kind":"native","value":"2"}},
            {"name":"c2x","value":{"kind":"native","value":"3"}},
            {"name":"c2y","value":{"kind":"native","value":"4"}}
        ]
    });
    assert_eq!(
        snapshot.page("records", 0, 2),
        json!({
            "abiVersion":1,
            "kind":"map",
            "entries":[{"key":{"kind":"bytes","values":vec![7u8;32]},"value":map_record}],
            "nextOffset":null
        })
    );
    assert_eq!(
        snapshot.page("recordList", 0, 2),
        json!({
            "abiVersion":1,
            "kind":"list",
            "entries":[{
                "kind":"struct",
                "id":"Issue69CompositeMap.Ciphertext4",
                "fields":[
                    {"name":"c1x","value":{"kind":"native","value":"5"}},
                    {"name":"c1y","value":{"kind":"native","value":"6"}},
                    {"name":"c2x","value":{"kind":"native","value":"7"}},
                    {"name":"c2y","value":{"kind":"native","value":"8"}}
                ]
            }],
            "nextOffset":null
        })
    );

    let malformed = composite_collection_snapshot(AlignedValue::from(1u64), &[]);
    assert_eq!(
        malformed.status("records", 0, 2, &artifacts::digest(&malformed.state)),
        INVALID_ARGUMENT
    );
}

#[test]
fn nested_scalar_collection_pages_follow_typed_paths() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let snapshot = nested_collection_snapshot();
    let owner_path = vec![bytes32_key(7)];

    assert_eq!(
        snapshot.page_at("nestedFlags", owner_path.clone(), 0, 2),
        json!({
            "abiVersion": 1,
            "kind": "map",
            "entries": [
                {"key":"1","value":true},
                {"key":"2","value":false}
            ],
            "nextOffset": 2
        })
    );
    assert_eq!(
        snapshot.page_at("nestedMembers", owner_path.clone(), 0, 2),
        json!({
            "abiVersion": 1,
            "kind": "set",
            "entries": [
                {"kind":"bytes","values":vec![1u8;32]},
                {"kind":"bytes","values":vec![4u8;32]}
            ],
            "nextOffset": 2
        })
    );
    assert_eq!(
        snapshot.page_at("nestedValues", owner_path.clone(), 1, 2),
        json!({
            "abiVersion": 1,
            "kind": "list",
            "entries": ["22", "33"],
            "nextOffset": null
        })
    );

    let state_digest = artifacts::digest(&snapshot.state);
    assert_eq!(
        snapshot.status_at("nestedFlags", vec![native_key(7)], 0, 2, &state_digest),
        INVALID_ARGUMENT
    );
    assert_eq!(
        snapshot.status_at("nestedFlags", vec![bytes32_key(8)], 0, 2, &state_digest),
        INVALID_ARGUMENT
    );
    assert_eq!(
        snapshot.status_at(
            "nestedFlags",
            vec![bytes32_key(7), native_key(1)],
            0,
            2,
            &state_digest
        ),
        INVALID_ARGUMENT
    );
}
