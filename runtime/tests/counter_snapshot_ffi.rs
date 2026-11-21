use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, artifacts, collection_ffi::noctium_ledger_counter_get, field_value, native_ffi, profile,
};
use onchain_runtime::state::{ChargedState, ContractState, StateValue};
use serde_json::{Value, json};
use serialize::tagged_serialize;
use storage::{arena::Sp, storage::HashMap};
use transient_crypto::curve::Fr;

struct Snapshot {
    plan: Vec<u8>,
    state: Vec<u8>,
}

impl Snapshot {
    fn new(kind: Value, state: StateValue<Db>) -> Self {
        let plan = serde_json::to_vec(&json!({
            "schemaVersion": 1,
            "target": profile::NAME,
            "targetProfile": profile::target_json(),
            "state": [{"name":"count", "kind":kind}],
        }))
        .unwrap();
        let mut contract = ContractState::<Db>::default();
        contract.data = ChargedState::new(StateValue::Array(vec![state].into()));
        let mut state_bytes = Vec::new();
        tagged_serialize(&contract, &mut state_bytes).unwrap();
        Self {
            plan,
            state: state_bytes,
        }
    }

    fn request(
        &self,
        name: &str,
        keys: Vec<Value>,
        plan_sha256: &str,
        state_sha256: &str,
    ) -> Vec<u8> {
        serde_json::to_vec(&json!({
            "abiVersion": 1,
            "planSha256": plan_sha256,
            "stateSha256": state_sha256,
            "name": name,
            "keys": keys,
        }))
        .unwrap()
    }

    fn call(&self, name: &str, keys: Vec<Value>) -> Result<Value, i32> {
        self.call_with_digests(
            name,
            keys,
            &artifacts::digest(&self.plan),
            &artifacts::digest(&self.state),
        )
    }

    fn call_with_digests(
        &self,
        name: &str,
        keys: Vec<Value>,
        plan_sha256: &str,
        state_sha256: &str,
    ) -> Result<Value, i32> {
        let request = self.request(name, keys, plan_sha256, state_sha256);
        let mut token = u64::MAX;
        let status = unsafe {
            noctium_ledger_counter_get(
                request.as_ptr(),
                request.len(),
                self.plan.as_ptr(),
                self.plan.len(),
                self.state.as_ptr(),
                self.state.len(),
                &mut token,
            )
        };
        if status != native_ffi::OK {
            assert_eq!(token, 0);
            return Err(status);
        }

        let mut length = 0;
        assert_eq!(
            unsafe { native_ffi::noctium_native_result_length(token, &mut length) },
            native_ffi::OK
        );
        let mut output = vec![0; length];
        let mut written = 0;
        assert_eq!(
            unsafe {
                native_ffi::noctium_native_result_copy(
                    token,
                    output.as_mut_ptr(),
                    output.len(),
                    &mut written,
                )
            },
            native_ffi::OK
        );
        assert_eq!(written, output.len());
        assert_eq!(
            native_ffi::noctium_native_result_free(token),
            native_ffi::OK
        );
        Ok(serde_json::from_slice(&output).unwrap())
    }
}

fn counter(value: u64) -> StateValue<Db> {
    StateValue::Cell(Sp::new(AlignedValue::from(value)))
}

fn counter_schema() -> Value {
    json!({"tree":{"counter":true}})
}

fn bytes32_key(value: u8) -> Value {
    json!({"type":"Bytes<32>","value":{"kind":"bytes","values":vec![value;32]}})
}

#[test]
fn reads_root_and_nested_counters_as_decimal_strings() {
    for value in [9_007_199_254_740_993, u64::MAX] {
        let snapshot = Snapshot::new(counter_schema(), counter(value));
        assert_eq!(
            snapshot.call("count", vec![]).unwrap(),
            json!({"abiVersion":1,"kind":"counter","value":value.to_string()})
        );
    }

    let key: AlignedValue = [7; 32].into();
    let nested = HashMap::new().insert(key, counter(9_007_199_254_740_993));
    let snapshot = Snapshot::new(
        json!({"tree":{"map":["Bytes<32>",{"counter":true}]}}),
        StateValue::Map(nested),
    );
    assert_eq!(
        snapshot.call("count", vec![bytes32_key(7)]).unwrap(),
        json!({"abiVersion":1,"kind":"counter","value":"9007199254740993"})
    );
}

#[test]
fn rejects_unpinned_wrong_type_missing_and_misaligned_counters() {
    let snapshot = Snapshot::new(counter_schema(), counter(1));
    assert_eq!(
        snapshot.call("absent", vec![]),
        Err(native_ffi::INVALID_ARGUMENT)
    );
    assert_eq!(
        snapshot.call_with_digests(
            "count",
            vec![],
            &artifacts::digest(&snapshot.plan),
            &"0".repeat(64),
        ),
        Err(native_ffi::INVALID_ARGUMENT)
    );

    let scalar = Snapshot::new(
        json!({"scalar":"UIntRange<18446744073709551616>"}),
        counter(1),
    );
    assert_eq!(
        scalar.call("count", vec![]),
        Err(native_ffi::INVALID_ARGUMENT)
    );

    let misaligned = Snapshot::new(
        counter_schema(),
        StateValue::Cell(Sp::new(field_value(Fr::from(1u64)))),
    );
    assert_eq!(
        misaligned.call("count", vec![]),
        Err(native_ffi::INVALID_ARGUMENT)
    );

    let nested = Snapshot::new(
        json!({"tree":{"map":["Bytes<32>",{"counter":true}]}}),
        StateValue::Map(HashMap::new()),
    );
    assert_eq!(
        nested.call("count", vec![bytes32_key(7)]),
        Err(native_ffi::INVALID_ARGUMENT)
    );
    assert_eq!(
        nested.call("count", vec![json!({"type":"Native","value":"7"})]),
        Err(native_ffi::INVALID_ARGUMENT)
    );
}
