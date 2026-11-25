#![cfg(feature = "zkir-321")]

use base_crypto::{
    fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom},
    hash::HashOutput,
};
use coin_structure::coin::{Info, Nonce, ShieldedTokenType};
use noctium_runtime::{
    Db, Plan, artifacts, check, create_state,
    collection_ffi::{
        noctium_ledger_cell_get, noctium_ledger_collection_page, noctium_ledger_collection_size,
        noctium_ledger_list_head, noctium_ledger_map_lookup, noctium_ledger_set_member,
    },
    field_value,
    native_ffi::{
        INVALID_ARGUMENT, OK, noctium_native_result_copy, noctium_native_result_free,
        noctium_native_result_length,
    },
    prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, ContractState, StateValue};
use serde_json::{Value, json};
use serialize::tagged_serialize;
use std::{collections::BTreeMap, sync::Mutex};
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
        Self::from_plan_bytes(serde_json::to_vec(&plan).unwrap(), state)
    }

    fn from_plan_bytes(plan: Vec<u8>, state: ChargedState<Db>) -> Self {
        let mut contract = ContractState::<Db>::default();
        contract.data = state;
        let mut state_bytes = Vec::new();
        tagged_serialize(&contract, &mut state_bytes).unwrap();
        Self {
            plan,
            state: state_bytes,
        }
    }

    fn cell_get(&self, name: &str) -> Value {
        self.cell_get_with_request(json!({
            "abiVersion": 1,
            "planSha256": artifacts::digest(&self.plan),
            "stateSha256": artifacts::digest(&self.state),
            "name": name,
            "keys": [],
        }))
        .unwrap_or_else(|status| panic!("read Cell {name}: status {status}"))
    }

    fn cell_get_with_request(&self, request: Value) -> Result<Value, i32> {
        let request = serde_json::to_vec(&request).unwrap();
        let mut token = 0;
        let status = unsafe {
            noctium_ledger_cell_get(
                request.as_ptr(),
                request.len(),
                self.plan.as_ptr(),
                self.plan.len(),
                self.state.as_ptr(),
                self.state.len(),
                &mut token,
            )
        };
        if status != OK {
            assert_eq!(token, 0);
            return Err(status);
        }

        let mut length = 0;
        assert_eq!(unsafe { noctium_native_result_length(token, &mut length) }, OK);
        let mut output = vec![0; length];
        let mut written = 0;
        assert_eq!(
            unsafe { noctium_native_result_copy(token, output.as_mut_ptr(), length, &mut written) },
            OK
        );
        assert_eq!(written, length);
        assert_eq!(noctium_native_result_free(token), OK);
        Ok(serde_json::from_slice(&output).unwrap())
    }

    fn page(&self, name: &str, offset: usize, limit: usize) -> Value {
        self.page_at(name, Vec::new(), offset, limit)
    }

    fn page_at(&self, name: &str, keys: Vec<Value>, offset: usize, limit: usize) -> Value {
        self.page_at_with_digests(
            name,
            keys,
            offset,
            limit,
            &artifacts::digest(&self.plan),
            &artifacts::digest(&self.state),
        )
        .unwrap()
    }

    fn page_at_with_digests(
        &self,
        name: &str,
        keys: Vec<Value>,
        offset: usize,
        limit: usize,
        plan_sha256: &str,
        state_sha256: &str,
    ) -> Result<Value, i32> {
        let request = serde_json::to_vec(&json!({
            "abiVersion": 1,
            "planSha256": plan_sha256,
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
        if status != OK {
            assert_eq!(token, 0);
            return Err(status);
        }

        let mut length = 0;
        assert_eq!(
            unsafe { noctium_native_result_length(token, &mut length) },
            OK
        );
        let mut output = vec![0; length];
        let mut written = 0;
        assert_eq!(
            unsafe {
                noctium_native_result_copy(token, output.as_mut_ptr(), length, &mut written)
            },
            OK
        );
        assert_eq!(written, length);
        assert_eq!(noctium_native_result_free(token), OK);
        Ok(serde_json::from_slice(&output).unwrap())
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
        match self.page_at_with_digests(
            name,
            keys,
            offset,
            limit,
            &artifacts::digest(&self.plan),
            state_sha256,
        ) {
            Ok(_) => OK,
            Err(status) => status,
        }
    }

    fn lookup(&self, name: &str, key: Value) -> Value {
        self.lookup_at(name, Vec::new(), key)
    }

    fn lookup_at(&self, name: &str, keys: Vec<Value>, key: Value) -> Value {
        let request = serde_json::to_vec(&json!({
            "abiVersion": 1,
            "planSha256": artifacts::digest(&self.plan),
            "stateSha256": artifacts::digest(&self.state),
            "name": name,
            "keys": keys,
            "key": key,
        }))
        .unwrap();
        let mut token = 0;
        unsafe {
            assert_eq!(
                noctium_ledger_map_lookup(
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

    fn lookup_status_at(
        &self,
        name: &str,
        keys: Vec<Value>,
        key: Option<Value>,
        state_sha256: &str,
    ) -> i32 {
        let mut request = json!({
            "abiVersion": 1,
            "planSha256": artifacts::digest(&self.plan),
            "stateSha256": state_sha256,
            "name": name,
            "keys": keys,
        });
        if let Some(key) = key {
            request["key"] = key;
        }
        self.lookup_status(request)
    }

    fn lookup_status(&self, request: Value) -> i32 {
        let request = serde_json::to_vec(&request).unwrap();
        let mut token = 0;
        let status = unsafe {
            noctium_ledger_map_lookup(
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

    fn member(&self, name: &str, key: Value) -> Value {
        self.member_at(name, Vec::new(), key)
    }

    fn member_at(&self, name: &str, keys: Vec<Value>, key: Value) -> Value {
        let request = serde_json::to_vec(&json!({
            "abiVersion": 1,
            "planSha256": artifacts::digest(&self.plan),
            "stateSha256": artifacts::digest(&self.state),
            "name": name,
            "keys": keys,
            "key": key,
        }))
        .unwrap();
        let mut token = 0;
        unsafe {
            assert_eq!(
                noctium_ledger_set_member(
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

    fn member_status_at(
        &self,
        name: &str,
        keys: Vec<Value>,
        key: Option<Value>,
        plan_sha256: &str,
        state_sha256: &str,
    ) -> i32 {
        let mut request = json!({
            "abiVersion": 1,
            "planSha256": plan_sha256,
            "stateSha256": state_sha256,
            "name": name,
            "keys": keys,
        });
        if let Some(key) = key {
            request["key"] = key;
        }
        self.member_status(request)
    }

    fn member_status(&self, request: Value) -> i32 {
        let request = serde_json::to_vec(&request).unwrap();
        let mut token = 0;
        let status = unsafe {
            noctium_ledger_set_member(
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

    fn head_at(&self, name: &str, keys: Vec<Value>) -> Value {
        self.head_with_digests(
            name,
            keys,
            &artifacts::digest(&self.plan),
            &artifacts::digest(&self.state),
        )
        .unwrap()
    }

    fn head_with_digests(
        &self,
        name: &str,
        keys: Vec<Value>,
        plan_sha256: &str,
        state_sha256: &str,
    ) -> Result<Value, i32> {
        let request = serde_json::to_vec(&json!({
            "abiVersion": 1,
            "planSha256": plan_sha256,
            "stateSha256": state_sha256,
            "name": name,
            "keys": keys,
        }))
        .unwrap();
        let mut token = 0;
        let status = unsafe {
            noctium_ledger_list_head(
                request.as_ptr(),
                request.len(),
                self.plan.as_ptr(),
                self.plan.len(),
                self.state.as_ptr(),
                self.state.len(),
                &mut token,
            )
        };
        if status != OK {
            assert_eq!(token, 0);
            return Err(status);
        }

        let mut length = 0;
        assert_eq!(unsafe { noctium_native_result_length(token, &mut length) }, OK);
        let mut output = vec![0; length];
        let mut written = 0;
        assert_eq!(
            unsafe { noctium_native_result_copy(token, output.as_mut_ptr(), length, &mut written) },
            OK
        );
        assert_eq!(written, length);
        assert_eq!(noctium_native_result_free(token), OK);
        Ok(serde_json::from_slice(&output).unwrap())
    }

    fn size_at(&self, name: &str, keys: Vec<Value>) -> Value {
        self.size_with_digests(
            name,
            keys,
            &artifacts::digest(&self.plan),
            &artifacts::digest(&self.state),
        )
        .unwrap()
    }

    fn size_with_digests(
        &self,
        name: &str,
        keys: Vec<Value>,
        plan_sha256: &str,
        state_sha256: &str,
    ) -> Result<Value, i32> {
        let request = serde_json::to_vec(&json!({
            "abiVersion": 1,
            "planSha256": plan_sha256,
            "stateSha256": state_sha256,
            "name": name,
            "keys": keys,
        }))
        .unwrap();
        let mut token = 0;
        let status = unsafe {
            noctium_ledger_collection_size(
                request.as_ptr(),
                request.len(),
                self.plan.as_ptr(),
                self.plan.len(),
                self.state.as_ptr(),
                self.state.len(),
                &mut token,
            )
        };
        if status != OK {
            assert_eq!(token, 0);
            return Err(status);
        }

        let mut length = 0;
        assert_eq!(unsafe { noctium_native_result_length(token, &mut length) }, OK);
        let mut output = vec![0; length];
        let mut written = 0;
        assert_eq!(
            unsafe { noctium_native_result_copy(token, output.as_mut_ptr(), length, &mut written) },
            OK
        );
        assert_eq!(written, length);
        assert_eq!(noctium_native_result_free(token), OK);
        Ok(serde_json::from_slice(&output).unwrap())
    }
}

fn bytes32_key(value: u8) -> Value {
    json!({"type":"Bytes<32>","value":{"kind":"bytes","values":vec![value;32]}})
}

fn bytes32_member_key(value: u8) -> Value {
    json!({"kind":"bytes","values":vec![value;32]})
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

fn corrupt_map_lookup_snapshot() -> Snapshot {
    let map = HashMap::new().insert(
        field_value(Fr::from(1u64)),
        StateValue::Cell(Sp::new(field_value(Fr::from(2u64)))),
    );
    Snapshot::new(
        plan(vec![json!({
            "name":"flags",
            "kind":{"map":["Native","Bool"]}
        })]),
        ChargedState::new(StateValue::Array(vec![StateValue::Map(map)].into())),
    )
}

fn corrupt_set_member_snapshot() -> Snapshot {
    let set = HashMap::new().insert(
        AlignedValue::from([1u8; 32]),
        StateValue::Cell(Sp::new(field_value(Fr::from(1u64)))),
    );
    Snapshot::new(
        plan(vec![json!({
            "name":"members",
            "kind":{"tree":{"set":"Bytes<32>"}}
        })]),
        ChargedState::new(StateValue::Array(vec![StateValue::Map(set)].into())),
    )
}

fn qualified_coin_record_schema() -> Value {
    json!({
        "id":"QualifiedCoinSet.Coin",
        "fields":[
            {"name":"nonce","type":"Bytes<32>"},
            {"name":"color","type":"Bytes<32>"},
            {"name":"value","type":"UIntRange<340282366920938463463374607431768211456>"},
            {"name":"mtIndex","type":"UIntRange<18446744073709551616>"}
        ]
    })
}

fn qualified_coin_info(nonce: u8, value: u128) -> Info {
    Info {
        nonce: Nonce(HashOutput([nonce; 32])),
        type_: ShieldedTokenType(HashOutput([1; 32])),
        value,
    }
}

fn qualified_coin_key(nonce: u8, value: u128, mt_index: u64) -> AlignedValue {
    AlignedValue::from(qualified_coin_info(nonce, value).qualify(mt_index))
}

fn qualified_coin_set_snapshot(entries: Vec<(AlignedValue, StateValue<Db>)>) -> Snapshot {
    let set = entries
        .into_iter()
        .fold(HashMap::new(), |set, (key, marker)| set.insert(key, marker));
    Snapshot::new(
        plan(vec![json!({
            "name":"coinSet",
            "kind":{"tree":{"set":{"composite":qualified_coin_record_schema()}}}
        })]),
        ChargedState::new(StateValue::Array(vec![StateValue::Map(set)].into())),
    )
}

fn qualified_coin_json(nonce: u8, value: u128, mt_index: u64) -> Value {
    json!({
        "nonce":{"kind":"bytes","values":vec![nonce;32]},
        "color":{"kind":"bytes","values":vec![1u8;32]},
        "value":value.to_string(),
        "mtIndex":mt_index.to_string()
    })
}

fn flat_record_set_schema() -> Value {
    json!({
        "id":"RecordSetCollections.Memo",
        "fields":[
            {"name":"active","type":"Bool"},
            {"name":"amount","type":"UIntRange<65536>"}
        ]
    })
}

fn flat_record_set_key(active: bool, amount: u16) -> AlignedValue {
    AlignedValue::concat(
        [
            field_value(Fr::from(u8::from(active))),
            field_value(Fr::from(u64::from(amount))),
        ]
        .iter(),
    )
}

fn flat_record_set_snapshot(entries: Vec<(AlignedValue, StateValue<Db>)>) -> Snapshot {
    let set = entries
        .into_iter()
        .fold(HashMap::new(), |set, (key, marker)| set.insert(key, marker));
    Snapshot::new(
        plan(vec![json!({
            "name":"memoSet",
            "kind":{"tree":{"set":{"composite":flat_record_set_schema()}}}
        })]),
        ChargedState::new(StateValue::Array(vec![StateValue::Map(set)].into())),
    )
}

fn flat_record_set_snapshot_from_rows(rows: &[(bool, u16)]) -> Snapshot {
    flat_record_set_snapshot(
        rows.iter()
            .map(|(active, amount)| {
                (flat_record_set_key(*active, *amount), StateValue::Null)
            })
            .collect(),
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

fn native_collection_page_plan() -> Value {
    plan(vec![
        json!({"name":"flags","kind":{"map":["Native","Bool"]}}),
        json!({"name":"members","kind":{"tree":{"set":"Bytes<32>"}}}),
        json!({"name":"values","kind":{"tree":{"list":{"scalar":"Native"}}}}),
    ])
}

fn native_collection_page_snapshot(
    plan: &[u8],
    flags: &[(u64, bool)],
    members: &[u8],
    values: &[u64],
) -> Snapshot {
    let flags = flags.iter().fold(HashMap::new(), |map, (key, value)| {
        map.insert(
            field_value(Fr::from(*key)),
            StateValue::Cell(Sp::new(field_value(Fr::from(u64::from(*value))))),
        )
    });
    let members = members.iter().fold(HashMap::new(), |set, value| {
        set.insert(AlignedValue::from([*value; 32]), StateValue::Null)
    });
    Snapshot::from_plan_bytes(
        plan.to_vec(),
        ChargedState::new(StateValue::Array(
            vec![
                StateValue::Map(flags),
                StateValue::Map(members),
                scalar_list(values),
            ]
            .into(),
        )),
    )
}

fn write_native_collection_page_fixtures(directory: &std::path::Path) -> anyhow::Result<()> {
    const COLLECTIONS: &[&str] = &["flags", "members", "values"];
    let flags = [(10, true), (2, false), (1, true)];
    let values = [11, 22, 33];

    std::fs::create_dir_all(directory)?;
    let plan_bytes = serde_json::to_vec_pretty(&native_collection_page_plan())?;
    std::fs::write(directory.join("plan.impact.json"), &plan_bytes)?;
    let snapshots = [
        (
            "empty",
            native_collection_page_snapshot(&plan_bytes, &[], &[], &[]),
            COLLECTIONS,
            &[0][..],
        ),
        (
            "populated",
            native_collection_page_snapshot(&plan_bytes, &flags, &[9, 1, 4], &values),
            COLLECTIONS,
            &[0, 2][..],
        ),
        (
            "removed",
            native_collection_page_snapshot(&plan_bytes, &flags, &[9, 1], &values),
            &["members"][..],
            &[0][..],
        ),
    ];
    let mut snapshot_manifest = serde_json::Map::new();
    let mut cases = Vec::new();
    for (name, snapshot, collections, offsets) in snapshots {
        let file = format!("{name}.state");
        std::fs::write(directory.join(&file), &snapshot.state)?;
        snapshot_manifest.insert(
            name.to_owned(),
            json!({
                "file": file,
                "sha256": artifacts::digest(&snapshot.state),
            }),
        );
        for &collection in collections {
            for &offset in offsets {
                cases.push(json!({
                    "snapshot": name,
                    "name": collection,
                    "offset": offset,
                    "limit": 2,
                    "expected": snapshot.page(collection, offset, 2),
                }));
            }
        }
    }

    let manifest = json!({
        "schemaVersion": 1,
        "plan": {
            "file": "plan.impact.json",
            "sha256": artifacts::digest(&plan_bytes),
        },
        "snapshots": snapshot_manifest,
        "cases": cases,
    });
    std::fs::write(
        directory.join("manifest.json"),
        serde_json::to_vec_pretty(&manifest)?,
    )?;
    Ok(())
}

fn read_pinned_fixture(
    directory: &std::path::Path,
    descriptor: &Value,
    expected_file: &str,
) -> anyhow::Result<(Vec<u8>, String)> {
    assert_eq!(descriptor["file"], expected_file);
    let digest = descriptor["sha256"]
        .as_str()
        .expect("fixture digest must be a string")
        .to_owned();
    assert_eq!(digest.len(), 64);
    let bytes = std::fs::read(directory.join(expected_file))?;
    assert_eq!(artifacts::digest(&bytes), digest);
    Ok((bytes, digest))
}

fn tamper_digest(digest: &str) -> String {
    let replacement = if digest.starts_with('0') { '1' } else { '0' };
    format!("{replacement}{}", &digest[1..])
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
            json!({"name":"nestedFlags","kind":{"tree":{"map":["Bytes<32>",{"map":["Native",{"scalar":"Bool"}]}]}}}),
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

fn emitted_list_snapshots(
    directory: &std::path::Path,
    contract: &str,
    read_entry: &str,
    seed_entry: &str,
    list_name: &str,
    seed_inputs: BTreeMap<String, Value>,
) -> anyhow::Result<(Snapshot, Snapshot)> {
    let read_stem = format!("{contract}.{read_entry}");
    let read_plan_bytes = std::fs::read(directory.join(format!("{read_stem}.impact.json")))?;
    let read_plan: Plan = serde_json::from_slice(&read_plan_bytes)?;
    let seed_stem = format!("{contract}.{seed_entry}");
    let seed_plan: Plan = serde_json::from_slice(&std::fs::read(
        directory.join(format!("{seed_stem}.impact.json")),
    )?)?;
    let seed_circuit = IrSource::load(
        std::fs::read(directory.join(format!("{seed_stem}.zkir")))?.as_slice(),
    )?;

    let empty_state = create_state(
        &read_plan,
        &BTreeMap::from([(list_name.to_owned(), json!([]))]),
    )?;
    let seeded = prepare(
        &seed_plan,
        &seed_inputs,
        &empty_state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    check(&seeded, &seed_circuit)?;
    Ok((
        Snapshot::from_plan_bytes(read_plan_bytes.clone(), empty_state),
        Snapshot::from_plan_bytes(read_plan_bytes, seeded.after.state),
    ))
}

#[test]
fn map_and_set_pages_are_typed_stable_and_bounded() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let snapshot = map_set_snapshot(false);
    let reverse = map_set_snapshot(true);

    assert_eq!(
        snapshot.size_at("flags", Vec::new()),
        json!({"abiVersion":1,"kind":"collectionSize","collection":"map","size":"3"})
    );
    assert_eq!(
        snapshot.size_at("members", Vec::new()),
        json!({"abiVersion":1,"kind":"collectionSize","collection":"set","size":"3"})
    );

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
fn map_lookup_returns_typed_root_values_and_null_for_missing_keys() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let snapshot = map_set_snapshot(false);

    assert_eq!(
        snapshot.lookup("flags", json!("1")),
        json!({
            "abiVersion":1,
            "kind":"mapLookup",
            "found":true,
            "value":true
        })
    );
    assert_eq!(
        snapshot.lookup("flags", json!("2")),
        json!({
            "abiVersion":1,
            "kind":"mapLookup",
            "found":true,
            "value":false
        })
    );
    assert_eq!(
        snapshot.lookup("flags", json!("3")),
        json!({
            "abiVersion":1,
            "kind":"mapLookup",
            "found":false,
            "value":null
        })
    );

    let state_digest = artifacts::digest(&snapshot.state);
    assert_eq!(
        snapshot.lookup_status_at("flags", Vec::new(), Some(json!({"type":"Native","value":"1"})), &state_digest),
        INVALID_ARGUMENT
    );
    assert_eq!(
        snapshot.lookup_status_at("flags", Vec::new(), None, &state_digest),
        INVALID_ARGUMENT
    );
    assert_eq!(
        snapshot.lookup_status_at("flags", Vec::new(), Some(json!("1")), &"0".repeat(64)),
        INVALID_ARGUMENT
    );

    assert_eq!(
        snapshot.lookup_status(json!({
            "abiVersion": 1,
            "planSha256": "0".repeat(64),
            "stateSha256": state_digest,
            "name": "flags",
            "keys": [],
            "key": "1"
        })),
        INVALID_ARGUMENT
    );

    let corrupt = corrupt_map_lookup_snapshot();
    let corrupt_digest = artifacts::digest(&corrupt.state);
    assert_eq!(
        corrupt.lookup_status_at("flags", Vec::new(), Some(json!("1")), &corrupt_digest),
        INVALID_ARGUMENT
    );
}

#[test]
fn set_member_reports_root_membership_and_rejects_invalid_requests() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let snapshot = map_set_snapshot(false);

    assert_eq!(
        snapshot.member("members", bytes32_member_key(1)),
        json!({"abiVersion":1,"kind":"setMember","member":true})
    );
    assert_eq!(
        snapshot.member("members", bytes32_member_key(2)),
        json!({"abiVersion":1,"kind":"setMember","member":false})
    );

    let plan_digest = artifacts::digest(&snapshot.plan);
    let state_digest = artifacts::digest(&snapshot.state);
    assert_eq!(
        snapshot.member_status_at(
            "members",
            Vec::new(),
            Some(bytes32_member_key(1)),
            &plan_digest,
            &"0".repeat(64),
        ),
        INVALID_ARGUMENT
    );
    assert_eq!(
        snapshot.member_status_at(
            "members",
            Vec::new(),
            Some(bytes32_member_key(1)),
            &"0".repeat(64),
            &state_digest,
        ),
        INVALID_ARGUMENT
    );
    assert_eq!(
        snapshot.member_status_at(
            "members",
            Vec::new(),
            Some(json!({"kind":"bytes","values":vec![1u8;31]})),
            &plan_digest,
            &state_digest,
        ),
        INVALID_ARGUMENT
    );
    assert_eq!(
        snapshot.member_status_at(
            "members",
            Vec::new(),
            None,
            &plan_digest,
            &state_digest,
        ),
        INVALID_ARGUMENT
    );
    assert_eq!(
        snapshot.member_status_at(
            "flags",
            Vec::new(),
            Some(json!("1")),
            &plan_digest,
            &state_digest,
        ),
        INVALID_ARGUMENT
    );

    let corrupt = corrupt_set_member_snapshot();
    assert_eq!(
        corrupt.member_status_at(
            "members",
            Vec::new(),
            Some(bytes32_member_key(1)),
            &artifacts::digest(&corrupt.plan),
            &artifacts::digest(&corrupt.state),
        ),
        INVALID_ARGUMENT
    );
}

#[test]
fn set_member_decodes_checked_record_keys() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let snapshot = flat_record_set_snapshot_from_rows(&[(true, 513)]);

    assert_eq!(
        snapshot.member(
            "memoSet",
            json!({"active":true,"amount":"513"}),
        ),
        json!({"abiVersion":1,"kind":"setMember","member":true})
    );
    assert_eq!(
        snapshot.member(
            "memoSet",
            json!({"active":false,"amount":"513"}),
        ),
        json!({"abiVersion":1,"kind":"setMember","member":false})
    );

    let digest_plan = artifacts::digest(&snapshot.plan);
    let digest_state = artifacts::digest(&snapshot.state);
    assert_eq!(
        snapshot.member_status_at(
            "memoSet",
            Vec::new(),
            Some(json!({"active":true,"amount":"65536"})),
            &digest_plan,
            &digest_state,
        ),
        INVALID_ARGUMENT
    );
}

#[test]
fn nested_set_member_uses_the_selected_parent() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let snapshot = nested_collection_snapshot();
    let owner_path = vec![bytes32_key(7)];

    assert_eq!(
        snapshot.size_at("nestedFlags", owner_path.clone()),
        json!({"abiVersion":1,"kind":"collectionSize","collection":"map","size":"3"})
    );
    assert_eq!(
        snapshot.size_at("nestedMembers", owner_path.clone()),
        json!({"abiVersion":1,"kind":"collectionSize","collection":"set","size":"3"})
    );
    assert_eq!(
        snapshot.size_at("nestedValues", owner_path.clone()),
        json!({"abiVersion":1,"kind":"collectionSize","collection":"list","size":"3"})
    );

    assert_eq!(
        snapshot.member_at(
            "nestedMembers",
            owner_path.clone(),
            bytes32_member_key(1),
        ),
        json!({"abiVersion":1,"kind":"setMember","member":true})
    );
    assert_eq!(
        snapshot.member_at(
            "nestedMembers",
            owner_path.clone(),
            bytes32_member_key(2),
        ),
        json!({"abiVersion":1,"kind":"setMember","member":false})
    );

    let plan_digest = artifacts::digest(&snapshot.plan);
    let state_digest = artifacts::digest(&snapshot.state);
    assert_eq!(
        snapshot.member_status_at(
            "nestedMembers",
            vec![bytes32_key(8)],
            Some(bytes32_member_key(1)),
            &plan_digest,
            &state_digest,
        ),
        INVALID_ARGUMENT
    );
    assert_eq!(
        snapshot.member_status_at(
            "nestedMembers",
            vec![native_key(7)],
            Some(bytes32_member_key(1)),
            &plan_digest,
            &state_digest,
        ),
        INVALID_ARGUMENT
    );
}

#[test]
fn qualified_coin_set_pages_decode_records_and_validate_all_members() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let first = (qualified_coin_key(2, 5, 17), StateValue::Null);
    let second = (qualified_coin_key(3, 7, 42), StateValue::Null);
    let snapshot = qualified_coin_set_snapshot(vec![first, second]);
    let reverse = qualified_coin_set_snapshot(vec![
        (qualified_coin_key(3, 7, 42), StateValue::Null),
        (qualified_coin_key(2, 5, 17), StateValue::Null),
    ]);

    let first_page = snapshot.page("coinSet", 0, 1);
    assert_eq!(
        first_page,
        json!({
            "abiVersion": 1,
            "kind": "set",
            "entries": [qualified_coin_json(2, 5, 17)],
            "nextOffset": 1
        })
    );
    let second_page = snapshot.page("coinSet", 1, 1);
    assert_eq!(
        second_page,
        json!({
            "abiVersion": 1,
            "kind": "set",
            "entries": [qualified_coin_json(3, 7, 42)],
            "nextOffset": null
        })
    );
    assert_eq!(reverse.page("coinSet", 0, 1), first_page);
    assert_eq!(reverse.page("coinSet", 1, 1), second_page);

    assert_eq!(
        snapshot.member("coinSet", qualified_coin_json(2, 5, 17)),
        json!({"abiVersion":1,"kind":"setMember","member":true})
    );
    assert_eq!(
        snapshot.member("coinSet", qualified_coin_json(2, 5, 18)),
        json!({"abiVersion":1,"kind":"setMember","member":false})
    );

    let malformed_key = qualified_coin_set_snapshot(vec![
        (qualified_coin_key(2, 5, 17), StateValue::Null),
        (qualified_coin_key(3, 7, 42), StateValue::Null),
        (AlignedValue::from(1u64), StateValue::Null),
    ]);
    assert_eq!(
        malformed_key.status("coinSet", 0, 1, &artifacts::digest(&malformed_key.state)),
        INVALID_ARGUMENT
    );

    let malformed_marker = qualified_coin_set_snapshot(vec![
        (qualified_coin_key(2, 5, 17), StateValue::Null),
        (qualified_coin_key(3, 7, 42), StateValue::Null),
        (
            qualified_coin_key(4, 9, 63),
            StateValue::Cell(Sp::new(field_value(Fr::from(1u64)))),
        ),
    ]);
    assert_eq!(
        malformed_marker.status("coinSet", 0, 1, &artifacts::digest(&malformed_marker.state)),
        INVALID_ARGUMENT
    );
}

#[test]
fn flat_record_set_pages_follow_declared_typed_order_after_removal() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let rows = [(true, 513), (false, 513), (true, 514)];
    let snapshot = flat_record_set_snapshot_from_rows(&rows);
    let reverse = flat_record_set_snapshot_from_rows(&[
        (true, 514),
        (false, 513),
        (true, 513),
    ]);

    let first_page = json!({
        "abiVersion":1,
        "kind":"set",
        "entries":[
            {"active":false,"amount":"513"},
            {"active":true,"amount":"513"}
        ],
        "nextOffset":2
    });
    let second_page = json!({
        "abiVersion":1,
        "kind":"set",
        "entries":[{"active":true,"amount":"514"}],
        "nextOffset":null
    });
    assert_eq!(snapshot.page("memoSet", 0, 2), first_page);
    assert_eq!(snapshot.page("memoSet", 2, 2), second_page);
    assert_eq!(reverse.page("memoSet", 0, 2), first_page);
    assert_eq!(reverse.page("memoSet", 2, 2), second_page);

    let empty = flat_record_set_snapshot_from_rows(&[]);
    assert_eq!(
        empty.page("memoSet", 0, 2),
        json!({
            "abiVersion":1,
            "kind":"set",
            "entries":[],
            "nextOffset":null
        })
    );

    let after_remove_rows = rows
        .iter()
        .copied()
        .filter(|row| *row != (false, 513))
        .collect::<Vec<_>>();
    let after_remove = flat_record_set_snapshot_from_rows(&after_remove_rows);
    assert_eq!(
        after_remove.page("memoSet", 0, 1),
        json!({
            "abiVersion":1,
            "kind":"set",
            "entries":[{"active":true,"amount":"513"}],
            "nextOffset":1
        })
    );
    assert_eq!(
        after_remove.page("memoSet", 1, 1),
        json!({
            "abiVersion":1,
            "kind":"set",
            "entries":[{"active":true,"amount":"514"}],
            "nextOffset":null
        })
    );

    let malformed_marker = flat_record_set_snapshot(vec![
        (flat_record_set_key(true, 513), StateValue::Null),
        (flat_record_set_key(false, 513), StateValue::Null),
        (
            flat_record_set_key(true, 514),
            StateValue::Cell(Sp::new(field_value(Fr::from(1u64)))),
        ),
    ]);
    assert_eq!(
        malformed_marker.status(
            "memoSet",
            0,
            1,
            &artifacts::digest(&malformed_marker.state)
        ),
        INVALID_ARGUMENT
    );

    let mut swapped_schema: Value = serde_json::from_slice(&snapshot.plan).unwrap();
    swapped_schema["state"][0]["kind"]["tree"]["set"]["composite"]["fields"]
        .as_array_mut()
        .unwrap()
        .swap(0, 1);
    let malformed_record = Snapshot {
        plan: serde_json::to_vec(&swapped_schema).unwrap(),
        state: snapshot.state.clone(),
    };
    assert_eq!(
        malformed_record.status(
            "memoSet",
            0,
            1,
            &artifacts::digest(&malformed_record.state)
        ),
        INVALID_ARGUMENT
    );
}

#[test]
fn scalar_list_pages_validate_count_and_empty_sentinel() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let snapshot = list_snapshot(&[11, 22, 33]);
    assert_eq!(
        snapshot.size_at("values", Vec::new()),
        json!({"abiVersion":1,"kind":"collectionSize","collection":"list","size":"3"})
    );
    assert_eq!(
        snapshot.size_at("empty", Vec::new()),
        json!({"abiVersion":1,"kind":"collectionSize","collection":"list","size":"0"})
    );
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
    assert_eq!(
        malformed.size_with_digests(
            "values",
            Vec::new(),
            &artifacts::digest(&malformed.plan),
            &artifacts::digest(&malformed.state),
        ),
        Err(INVALID_ARGUMENT)
    );
}

#[test]
fn collection_size_rejects_invalid_collection_parent_and_pins() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let snapshot = nested_collection_snapshot();
    let plan_sha256 = artifacts::digest(&snapshot.plan);
    let state_sha256 = artifacts::digest(&snapshot.state);

    assert_eq!(
        snapshot.size_with_digests("missing", Vec::new(), &plan_sha256, &state_sha256),
        Err(INVALID_ARGUMENT)
    );
    assert_eq!(
        snapshot.size_with_digests(
            "nestedValues",
            vec![bytes32_key(8)],
            &plan_sha256,
            &state_sha256,
        ),
        Err(INVALID_ARGUMENT)
    );
    assert_eq!(
        snapshot.size_with_digests(
            "nestedValues",
            vec![native_key(7)],
            &plan_sha256,
            &state_sha256,
        ),
        Err(INVALID_ARGUMENT)
    );
    assert_eq!(
        snapshot.size_with_digests(
            "nestedValues",
            vec![bytes32_key(7)],
            &"0".repeat(64),
            &state_sha256,
        ),
        Err(INVALID_ARGUMENT)
    );
    assert_eq!(
        snapshot.size_with_digests(
            "nestedValues",
            vec![bytes32_key(7)],
            &plan_sha256,
            &"0".repeat(64),
        ),
        Err(INVALID_ARGUMENT)
    );
}

#[test]
fn list_head_reads_typed_values_and_rejects_invalid_paths_and_snapshots() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let scalar = list_snapshot(&[11, 22, 33]);
    assert_eq!(
        scalar.head_at("values", Vec::new()),
        json!({"abiVersion":1,"kind":"listHead","found":true,"value":"11"})
    );
    let empty = list_snapshot(&[]);
    assert_eq!(
        empty.head_at("values", Vec::new()),
        json!({"abiVersion":1,"kind":"listHead","found":false,"value":null})
    );

    let nested = nested_collection_snapshot();
    assert_eq!(
        nested.head_at("nestedValues", vec![bytes32_key(7)]),
        json!({"abiVersion":1,"kind":"listHead","found":true,"value":"11"})
    );
    let nested_plan_sha256 = artifacts::digest(&nested.plan);
    let state_sha256 = artifacts::digest(&nested.state);
    assert_eq!(
        nested.head_with_digests(
            "nestedValues",
            vec![bytes32_key(8)],
            &nested_plan_sha256,
            &state_sha256,
        ),
        Err(INVALID_ARGUMENT)
    );
    assert_eq!(
        nested.head_with_digests(
            "nestedValues",
            vec![native_key(7)],
            &nested_plan_sha256,
            &state_sha256,
        ),
        Err(INVALID_ARGUMENT)
    );
    assert_eq!(
        scalar.head_with_digests(
            "values",
            Vec::new(),
            &"0".repeat(64),
            &artifacts::digest(&scalar.state),
        ),
        Err(INVALID_ARGUMENT)
    );
    assert_eq!(
        scalar.head_with_digests(
            "values",
            Vec::new(),
            &artifacts::digest(&scalar.plan),
            &"0".repeat(64),
        ),
        Err(INVALID_ARGUMENT)
    );

    let checked_record = composite_collection_snapshot(AlignedValue::from(0u64), &[[5, 6, 7, 8]]);
    assert_eq!(
        checked_record.head_at("recordList", Vec::new()),
        json!({
            "abiVersion":1,
            "kind":"listHead",
            "found":true,
            "value":{
                "kind":"struct",
                "id":"Issue69CompositeMap.Ciphertext4",
                "fields":[
                    {"name":"c1x","value":{"kind":"native","value":"5"}},
                    {"name":"c1y","value":{"kind":"native","value":"6"}},
                    {"name":"c2x","value":{"kind":"native","value":"7"}},
                    {"name":"c2y","value":{"kind":"native","value":"8"}}
                ]
            }
        })
    );

    let malformed = malformed_list_snapshot();
    assert_eq!(
        malformed.head_with_digests(
            "values",
            Vec::new(),
            &artifacts::digest(&malformed.plan),
            &artifacts::digest(&malformed.state),
        ),
        Err(INVALID_ARGUMENT)
    );
}

#[test]
#[ignore = "requires fresh NativeScalarListMaybe and RecordListHeadMaybe outputs in the ABI fixture directories"]
fn list_head_reads_source_emitted_scalar_and_record_snapshots() -> anyhow::Result<()> {
    let _guard = PAGE_TESTS.lock().unwrap();
    let scalar_directory = std::path::PathBuf::from(std::env::var(
        "NOCTIUM_LIST_HEAD_SCALAR_DIR",
    )?);
    let (empty_scalar, populated_scalar) = emitted_list_snapshots(
        &scalar_directory,
        "NativeScalarListMaybe",
        "head",
        "push",
        "values",
        BTreeMap::from([("value".into(), json!("37"))]),
    )?;
    for (snapshot, length) in [(&empty_scalar, "0"), (&populated_scalar, "1")] {
        assert_eq!(
            snapshot.size_at("values", Vec::new()),
            json!({"abiVersion":1,"kind":"collectionSize","collection":"list","size":length})
        );
    }
    assert_eq!(
        empty_scalar.head_at("values", Vec::new()),
        json!({"abiVersion":1,"kind":"listHead","found":false,"value":null})
    );
    assert_eq!(
        populated_scalar.head_at("values", Vec::new()),
        json!({"abiVersion":1,"kind":"listHead","found":true,"value":"37"})
    );

    let record_directory = std::path::PathBuf::from(std::env::var(
        "NOCTIUM_LIST_HEAD_RECORD_DIR",
    )?);
    let (empty_record, populated_record) = emitted_list_snapshots(
        &record_directory,
        "RecordListHeadMaybe",
        "peek",
        "seed",
        "inbox",
        BTreeMap::new(),
    )?;
    assert_eq!(
        empty_record.head_at("inbox", Vec::new()),
        json!({"abiVersion":1,"kind":"listHead","found":false,"value":null})
    );
    assert_eq!(
        populated_record.head_at("inbox", Vec::new()),
        json!({
            "abiVersion":1,
            "kind":"listHead",
            "found":true,
            "value":{
                "kind":"struct",
                "id":"RecordListHeadMaybe.Memo",
                "fields":[
                    {"name":"first","value":{"kind":"native","value":"17"}},
                    {"name":"second","value":{"kind":"native","value":"23"}}
                ]
            }
        })
    );
    Ok(())
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
        snapshot.lookup(
            "records",
            json!({"kind":"bytes","values":vec![7u8;32]})
        ),
        json!({
            "abiVersion":1,
            "kind":"mapLookup",
            "found":true,
            "value":map_record
        })
    );
    assert_eq!(
        snapshot.lookup(
            "records",
            json!({"kind":"bytes","values":vec![8u8;32]})
        ),
        json!({
            "abiVersion":1,
            "kind":"mapLookup",
            "found":false,
            "value":null
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
#[ignore = "requires fresh RecordMapKeys outputs in NOCTIUM_RECORD_MAP_KEY_PAGE_DIR"]
fn record_key_map_pages_sort_and_validate_typed_keys() -> anyhow::Result<()> {
    let _guard = PAGE_TESTS.lock().unwrap();
    let directory = std::path::PathBuf::from(std::env::var("NOCTIUM_RECORD_MAP_KEY_PAGE_DIR")?);
    let stem = "RecordMapKeys.update";
    let plan_bytes = std::fs::read(directory.join(format!("{stem}.impact.json")))?;
    let plan: Plan = serde_json::from_slice(&plan_bytes)?;
    let circuit = IrSource::load(std::fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?;
    let empty = create_state(&plan, &BTreeMap::from([("memos".into(), json!([]))]))?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let records = [(true, 513u16, 33u16), (false, 513, 22), (true, 514, 44)];
    let snapshot = |reverse: bool| -> anyhow::Result<Snapshot> {
        let mut state = empty.clone();
        let mut records = records;
        if reverse {
            records.reverse();
        }
        for (active, amount, value) in records {
            let arguments = BTreeMap::from([
                ("active".into(), json!(active)),
                ("amount".into(), json!(amount.to_string())),
                ("value".into(), json!(value.to_string())),
            ]);
            let execution = prepare(&plan, &arguments, &state, parameters, address)?;
            assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
            assert_eq!(execution.returns_json()["presentBefore"], json!(false));
            assert_eq!(execution.returns_json()["presentAfter"], json!(true));
            state = execution.after.state;
        }
        Ok(Snapshot::from_plan_bytes(plan_bytes.clone(), state))
    };

    let forward = snapshot(false)?;
    let reverse = snapshot(true)?;
    let first_page = json!({
        "abiVersion":1,
        "kind":"map",
        "entries":[
            {"key":{"active":false,"amount":"513"},"value":"22"},
            {"key":{"active":true,"amount":"513"},"value":"33"}
        ],
        "nextOffset":2
    });
    let second_page = json!({
        "abiVersion":1,
        "kind":"map",
        "entries":[
            {"key":{"active":true,"amount":"514"},"value":"44"}
        ],
        "nextOffset":null
    });
    assert_eq!(forward.page("memos", 0, 2), first_page);
    assert_eq!(forward.page("memos", 2, 2), second_page);
    assert_eq!(reverse.page("memos", 0, 2), first_page);
    assert_eq!(reverse.page("memos", 2, 2), second_page);
    assert_eq!(
        forward.lookup("memos", json!({"active":false,"amount":"513"})),
        json!({
            "abiVersion":1,
            "kind":"mapLookup",
            "found":true,
            "value":"22"
        })
    );
    assert_eq!(
        forward.lookup("memos", json!({"active":true,"amount":"513"})),
        json!({
            "abiVersion":1,
            "kind":"mapLookup",
            "found":true,
            "value":"33"
        })
    );
    assert_eq!(
        forward.lookup("memos", json!({"active":true,"amount":"515"})),
        json!({
            "abiVersion":1,
            "kind":"mapLookup",
            "found":false,
            "value":null
        })
    );

    let mut malformed_schema: Value = serde_json::from_slice(&plan_bytes)?;
    malformed_schema["state"][0]["kind"]["tree"]["map"][0]["composite"]["fields"][1]
        ["type"] = json!("Bool");
    let malformed_schema = Snapshot {
        plan: serde_json::to_vec(&malformed_schema)?,
        state: forward.state.clone(),
    };
    assert_eq!(
        malformed_schema.status("memos", 0, 2, &artifacts::digest(&malformed_schema.state)),
        INVALID_ARGUMENT
    );

    let malformed_key = field_value(Fr::from(513u64));
    let malformed_map = HashMap::new().insert(
        malformed_key,
        StateValue::Cell(Sp::new(field_value(Fr::from(33u64)))),
    );
    let malformed_payload = Snapshot::from_plan_bytes(
        plan_bytes,
        ChargedState::new(StateValue::Array(vec![StateValue::Map(malformed_map)].into())),
    );
    assert_eq!(
        malformed_payload.status("memos", 0, 2, &artifacts::digest(&malformed_payload.state)),
        INVALID_ARGUMENT
    );
    Ok(())
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

    assert_eq!(
        snapshot.lookup_at("nestedFlags", owner_path.clone(), json!("1")),
        json!({
            "abiVersion":1,
            "kind":"mapLookup",
            "found":true,
            "value":true
        })
    );
    assert_eq!(
        snapshot.lookup_at("nestedFlags", owner_path.clone(), json!("99")),
        json!({
            "abiVersion":1,
            "kind":"mapLookup",
            "found":false,
            "value":null
        })
    );

    let state_digest = artifacts::digest(&snapshot.state);
    assert_eq!(
        snapshot.lookup_status_at(
            "nestedFlags",
            Vec::new(),
            Some(json!("1")),
            &state_digest
        ),
        INVALID_ARGUMENT
    );
    assert_eq!(
        snapshot.lookup_status_at(
            "nestedFlags",
            vec![native_key(7)],
            Some(json!("1")),
            &state_digest
        ),
        INVALID_ARGUMENT
    );
    assert_eq!(
        snapshot.lookup_status_at(
            "nestedFlags",
            vec![bytes32_key(8)],
            Some(json!("1")),
            &state_digest
        ),
        INVALID_ARGUMENT
    );
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

#[test]
#[ignore = "requires fresh Lean outputs in NOCTIUM_SET_DIR and NOCTIUM_RECORD_SET_COLLECTIONS_DIR"]
fn source_emitted_sets_support_native_and_checked_record_membership() -> anyhow::Result<()> {
    let _guard = PAGE_TESTS.lock().unwrap();
    let native_dir = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_SET_DIR").expect("NativeSet Lean outputs"),
    );
    let native_plan_bytes = std::fs::read(native_dir.join("NativeSet.update.impact.json"))?;
    let native_plan: Plan = serde_json::from_slice(&native_plan_bytes)?;
    let native_circuit = IrSource::load(
        std::fs::read(native_dir.join("NativeSet.update.zkir"))?.as_slice(),
    )?;
    let native_state = create_state(
        &native_plan,
        &BTreeMap::from([
            ("registered".into(), json!([])),
            ("groups".into(), json!([])),
        ]),
    )?;
    let initial = Snapshot::from_plan_bytes(native_plan_bytes.clone(), native_state.clone());
    assert_eq!(
        initial.size_at("groups", Vec::new()),
        json!({"abiVersion":1,"kind":"collectionSize","collection":"map","size":"0"})
    );
    let native_inputs = BTreeMap::from([
        ("bucket".into(), json!("1")),
        ("tag".into(), bytes32_member_key(7)),
        ("adding".into(), json!(true)),
        ("removing".into(), json!(false)),
        ("clearing".into(), json!(false)),
    ]);
    let native_step = prepare(
        &native_plan,
        &native_inputs,
        &native_state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(
        check(&native_step, &native_circuit)?,
        native_step.activity_schedule
    );
    let native = Snapshot::from_plan_bytes(native_plan_bytes, native_step.after.state);
    assert_eq!(
        native.size_at("groups", Vec::new()),
        json!({"abiVersion":1,"kind":"collectionSize","collection":"map","size":"1"})
    );
    assert_eq!(
        native.size_at("groups", vec![native_key(1)]),
        json!({"abiVersion":1,"kind":"collectionSize","collection":"set","size":"1"})
    );
    assert_eq!(
        native.member("registered", bytes32_member_key(7)),
        json!({"abiVersion":1,"kind":"setMember","member":true})
    );
    assert_eq!(
        native.member_at("groups", vec![native_key(1)], bytes32_member_key(7)),
        json!({"abiVersion":1,"kind":"setMember","member":true})
    );

    let record_dir = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_RECORD_SET_COLLECTIONS_DIR")
            .expect("RecordSetCollections Lean outputs"),
    );
    let record_plan_bytes =
        std::fs::read(record_dir.join("RecordSetCollections.update.impact.json"))?;
    let record_plan: Plan = serde_json::from_slice(&record_plan_bytes)?;
    let record_circuit = IrSource::load(
        std::fs::read(record_dir.join("RecordSetCollections.update.zkir"))?.as_slice(),
    )?;
    let record_state = create_state(&record_plan, &BTreeMap::from([("memoSet".into(), json!([]))]))?;
    let record_inputs = BTreeMap::from([
        ("active".into(), json!(true)),
        ("amount".into(), json!("513")),
        ("adding".into(), json!(true)),
        ("clear".into(), json!(false)),
    ]);
    let record_step = prepare(
        &record_plan,
        &record_inputs,
        &record_state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    assert_eq!(
        check(&record_step, &record_circuit)?,
        record_step.activity_schedule
    );
    let record = Snapshot::from_plan_bytes(record_plan_bytes, record_step.after.state);
    assert_eq!(
        record.member("memoSet", json!({"active":true,"amount":"513"})),
        json!({"abiVersion":1,"kind":"setMember","member":true})
    );
    assert_eq!(
        record.member("memoSet", json!({"active":false,"amount":"513"})),
        json!({"abiVersion":1,"kind":"setMember","member":false})
    );
    Ok(())
}

#[test]
fn pinned_cell_get_decodes_scalar_record_u128_and_opaque_values() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let scalar = Snapshot::new(
        plan(vec![json!({"name":"total","kind":{"cell":"Native"}})]),
        ChargedState::new(StateValue::Array(
            vec![StateValue::Cell(Sp::new(field_value(Fr::from(42u64))))].into(),
        )),
    );
    assert_eq!(
        scalar.cell_get("total"),
        json!({"abiVersion":1,"kind":"cell","value":"42"})
    );

    let record = Snapshot::new(
        plan(vec![json!({
            "name":"memo",
            "kind":{"tree":{"composite":flat_record_set_schema()}}
        })]),
        ChargedState::new(StateValue::Array(
            vec![StateValue::Cell(Sp::new(flat_record_set_key(true, 513)))].into(),
        )),
    );
    assert_eq!(
        record.cell_get("memo"),
        json!({
            "abiVersion":1,
            "kind":"cell",
            "value":{"active":true,"amount":"513"}
        })
    );

    let u128_value = u128::MAX;
    let u128_cell = Snapshot::new(
        plan(vec![json!({
            "name":"totalSupply",
            "kind":{"cell":"UIntRange<340282366920938463463374607431768211456>"},
            "cellAlignment":"u128"
        })]),
        ChargedState::new(StateValue::Array(
            vec![StateValue::Cell(Sp::new(AlignedValue::from(u128_value)))].into(),
        )),
    );
    assert_eq!(
        u128_cell.cell_get("totalSupply"),
        json!({
            "abiVersion":1,
            "kind":"cell",
            "value":"340282366920938463463374607431768211455"
        })
    );

    let opaque = Snapshot::new(
        plan(vec![json!({"name":"label","kind":{"opaqueString":true}})]),
        ChargedState::new(StateValue::Array(
            vec![StateValue::Cell(Sp::new(AlignedValue {
                value: FabValue(vec![ValueAtom::from(b"stored label".as_slice())]),
                alignment: Alignment::singleton(AlignmentAtom::Compress),
            }))]
            .into(),
        )),
    );
    assert_eq!(
        opaque.cell_get("label"),
        json!({
            "abiVersion":1,
            "kind":"cell",
            "value":{"kind":"opaqueString","value":"stored label"}
        })
    );
}

#[test]
fn pinned_cell_get_rejects_bad_alignment_pins_keys_and_collections() {
    let _guard = PAGE_TESTS.lock().unwrap();
    let malformed_alignment = Snapshot::new(
        plan(vec![json!({"name":"total","kind":{"cell":"Native"}})]),
        ChargedState::new(StateValue::Array(
            vec![StateValue::Cell(Sp::new(AlignedValue::from([1u8; 16])))].into(),
        )),
    );
    assert_eq!(
        malformed_alignment.cell_get_with_request(json!({
            "abiVersion":1,
            "planSha256":artifacts::digest(&malformed_alignment.plan),
            "stateSha256":artifacts::digest(&malformed_alignment.state),
            "name":"total",
            "keys":[]
        })),
        Err(INVALID_ARGUMENT)
    );

    let scalar = Snapshot::new(
        plan(vec![json!({"name":"total","kind":{"cell":"Native"}})]),
        ChargedState::new(StateValue::Array(
            vec![StateValue::Cell(Sp::new(field_value(Fr::from(1u64))))].into(),
        )),
    );
    let valid_request = json!({
        "abiVersion":1,
        "planSha256":artifacts::digest(&scalar.plan),
        "stateSha256":artifacts::digest(&scalar.state),
        "name":"total",
        "keys":[]
    });

    for (field, digest) in [
        ("planSha256", artifacts::digest(&scalar.plan)),
        ("stateSha256", artifacts::digest(&scalar.state)),
    ] {
        let mut request = valid_request.clone();
        request[field] = json!(if digest.starts_with('0') {
            format!("1{}", &digest[1..])
        } else {
            format!("0{}", &digest[1..])
        });
        assert_eq!(
            scalar.cell_get_with_request(request),
            Err(INVALID_ARGUMENT)
        );
    }

    let mut keyed_request = valid_request;
    keyed_request["keys"] = json!([native_key(1)]);
    assert_eq!(
        scalar.cell_get_with_request(keyed_request),
        Err(INVALID_ARGUMENT)
    );

    let map = map_set_snapshot(false);
    assert_eq!(
        map.cell_get_with_request(json!({
            "abiVersion":1,
            "planSha256":artifacts::digest(&map.plan),
            "stateSha256":artifacts::digest(&map.state),
            "name":"flags",
            "keys":[]
        })),
        Err(INVALID_ARGUMENT)
    );
}

#[test]
#[ignore = "requires fresh ByteAlignedUInt128Cell and TypedRecordCell outputs in their artifact directories"]
fn source_emitted_cell_get_reads_u128_and_checked_record() -> anyhow::Result<()> {
    let _guard = PAGE_TESTS.lock().unwrap();
    let u128_directory = std::path::PathBuf::from(std::env::var(
        "NOCTIUM_BYTE_ALIGNED_UINT128_CELL_DIR",
    )?);
    let u128_plan_bytes = std::fs::read(
        u128_directory.join("ByteAlignedUInt128Cell.update.impact.json"),
    )?;
    let u128_plan: Plan = serde_json::from_slice(&u128_plan_bytes)?;
    let u128_state = create_state(
        &u128_plan,
        &BTreeMap::from([
            ("totalSupply".into(), json!(u128::MAX.to_string())),
            ("ordinary".into(), json!("9")),
        ]),
    )?;
    let u128_snapshot = Snapshot::from_plan_bytes(u128_plan_bytes, u128_state);
    assert_eq!(
        u128_snapshot.cell_get("totalSupply"),
        json!({
            "abiVersion":1,
            "kind":"cell",
            "value":"340282366920938463463374607431768211455"
        })
    );

    let record_directory =
        std::path::PathBuf::from(std::env::var("NOCTIUM_TYPED_RECORD_CELL_DIR")?);
    let record_plan_bytes =
        std::fs::read(record_directory.join("TypedRecordCell.inspectMemo.impact.json"))?;
    let record_plan: Plan = serde_json::from_slice(&record_plan_bytes)?;
    let record_state = create_state(
        &record_plan,
        &BTreeMap::from([("memo".into(), json!({"active":true,"amount":"513"}))]),
    )?;
    let record_snapshot = Snapshot::from_plan_bytes(record_plan_bytes, record_state);
    assert_eq!(
        record_snapshot.cell_get("memo"),
        json!({
            "abiVersion":1,
            "kind":"cell",
            "value":{"active":true,"amount":"513"}
        })
    );
    Ok(())
}

#[test]
fn retained_collection_snapshot_pages_match_c_abi() -> anyhow::Result<()> {
    let _guard = PAGE_TESTS.lock().unwrap();
    let fixture_directory = match std::env::var_os("NOCTIUM_COLLECTION_FIXTURE_EXPORT") {
        Some(directory) => {
            let directory = std::path::PathBuf::from(directory);
            assert!(
                directory.is_absolute(),
                "NOCTIUM_COLLECTION_FIXTURE_EXPORT must be an absolute path"
            );
            write_native_collection_page_fixtures(&directory)?;
            directory
        }
        None => std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../tests/fixtures/native-collection-pages"),
    };

    let manifest: Value =
        serde_json::from_slice(&std::fs::read(fixture_directory.join("manifest.json"))?)?;
    assert_eq!(manifest["schemaVersion"], 1);
    assert_eq!(manifest["snapshots"].as_object().unwrap().len(), 3);
    let (plan_bytes, plan_sha256) =
        read_pinned_fixture(&fixture_directory, &manifest["plan"], "plan.impact.json")?;
    let plan_json: Value = serde_json::from_slice(&plan_bytes)?;
    assert_eq!(plan_json["state"], native_collection_page_plan()["state"]);

    let mut snapshots = BTreeMap::new();
    let mut state_sha256 = BTreeMap::new();
    for (name, file) in [
        ("empty", "empty.state"),
        ("populated", "populated.state"),
        ("removed", "removed.state"),
    ] {
        let (state, digest) =
            read_pinned_fixture(&fixture_directory, &manifest["snapshots"][name], file)?;
        snapshots.insert(
            name.to_owned(),
            Snapshot {
                plan: plan_bytes.clone(),
                state,
            },
        );
        state_sha256.insert(name.to_owned(), digest);
    }

    let cases = manifest["cases"].as_array().expect("manifest cases array");
    assert_eq!(cases.len(), 10);
    for case in cases {
        let snapshot_name = case["snapshot"].as_str().expect("case snapshot name");
        let name = case["name"].as_str().expect("case collection name");
        let offset = case["offset"].as_u64().expect("case offset") as usize;
        let limit = case["limit"].as_u64().expect("case limit") as usize;
        let snapshot = snapshots
            .get(snapshot_name)
            .unwrap_or_else(|| panic!("unknown snapshot in case: {snapshot_name}"));
        let state_digest = &state_sha256[snapshot_name];
        assert_eq!(
            snapshot
                .page_at_with_digests(name, Vec::new(), offset, limit, &plan_sha256, state_digest,)
                .unwrap(),
            case["expected"],
            "{snapshot_name}.{name} page at offset {offset}"
        );
    }

    let populated = &snapshots["populated"];
    let removed = &snapshots["removed"];
    for (name, offset) in [("flags", 0), ("flags", 2), ("values", 0), ("values", 2)] {
        assert_eq!(
            removed
                .page_at_with_digests(
                    name,
                    Vec::new(),
                    offset,
                    2,
                    &plan_sha256,
                    &state_sha256["removed"],
                )
                .unwrap(),
            populated
                .page_at_with_digests(
                    name,
                    Vec::new(),
                    offset,
                    2,
                    &plan_sha256,
                    &state_sha256["populated"],
                )
                .unwrap(),
            "removed snapshot changed {name} at offset {offset}"
        );
    }

    let empty = &snapshots["empty"];
    assert_eq!(
        empty.page_at_with_digests(
            "flags",
            Vec::new(),
            0,
            2,
            &tamper_digest(&plan_sha256),
            &state_sha256["empty"],
        ),
        Err(INVALID_ARGUMENT)
    );
    assert_eq!(
        empty.page_at_with_digests(
            "flags",
            Vec::new(),
            0,
            2,
            &plan_sha256,
            &tamper_digest(&state_sha256["empty"]),
        ),
        Err(INVALID_ARGUMENT)
    );
    Ok(())
}
