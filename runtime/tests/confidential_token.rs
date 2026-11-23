#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Plan, check, construct_state,
    constructor::decode_opaque_string,
    control::{InvocationTarget, Session, TypedResponse},
    field_decimal, field_value,
    host::{self, Capability, Context, Limits, Operation, Provider},
    prepare,
    witness::{Parameter, WitnessSignature},
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use transient_crypto::{
    curve::{EmbeddedFr, EmbeddedGroupAffine, Fr},
    fab::AlignedValueExt,
};

fn artifacts(entry: &str) -> (&'static str, &'static str, &'static [u8]) {
    match entry {
        "registerWithKey" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.registerWithKey.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.registerWithKey.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.registerWithKey.zkir"
            ),
        ),
        "mint" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.mint.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.mint.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.mint.zkir"
            ),
        ),
        "sweep" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.sweep.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.sweep.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.sweep.zkir"
            ),
        ),
        "transfer" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.transfer.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.transfer.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.transfer.zkir"
            ),
        ),
        "burn" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.burn.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.burn.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.burn.zkir"
            ),
        ),
        "clearMemos" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.clearMemos.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.clearMemos.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.clearMemos.zkir"
            ),
        ),
        "_move" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken._move.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken._move.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken._move.zkir"
            ),
        ),
        "approve" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.approve.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.approve.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.approve.zkir"
            ),
        ),
        "transferFrom" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.transferFrom.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.transferFrom.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.transferFrom.zkir"
            ),
        ),
        "burnFrom" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.burnFrom.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.burnFrom.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.burnFrom.zkir"
            ),
        ),
        _ => panic!("unknown confidential-token entrypoint {entry}"),
    }
}

fn view_artifacts(entry: &str) -> (&'static str, &'static [u8]) {
    match entry {
        "totalSupply" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.totalSupply.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.totalSupply.zkir"
            ),
        ),
        "isRegistered" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.isRegistered.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.isRegistered.zkir"
            ),
        ),
        "balanceOf" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.balanceOf.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.balanceOf.zkir"
            ),
        ),
        "pendingOf" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.pendingOf.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.pendingOf.zkir"
            ),
        ),
        "computeAccountId" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.computeAccountId.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.computeAccountId.zkir"
            ),
        ),
        "allowance" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.allowance.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.allowance.zkir"
            ),
        ),
        _ => panic!("unknown confidential-token view {entry}"),
    }
}

fn signatures(plan: &Json) -> Vec<WitnessSignature> {
    plan["witnesses"]
        .as_array()
        .unwrap()
        .iter()
        .map(|value| WitnessSignature {
            name: value["name"].as_str().unwrap().to_owned(),
            operation: value["operation"].as_str().unwrap().to_owned(),
            capability: value["capability"].as_str().unwrap().to_owned(),
            parameters: value["parameters"]
                .as_array()
                .unwrap()
                .iter()
                .map(|parameter| Parameter {
                    name: parameter["name"].as_str().unwrap().to_owned(),
                    type_token: parameter["type"].as_str().unwrap().to_owned(),
                })
                .collect(),
            result_type: value["resultType"].as_str().unwrap().to_owned(),
            private_key: value["privateKey"].as_str().map(str::to_owned),
        })
        .collect()
}

fn context(plan: &Json, attempt_id: &str) -> Context {
    let mut operations = BTreeMap::<String, Operation>::new();
    let mut providers = Vec::new();
    let mut capabilities = BTreeMap::<String, (String, BTreeSet<String>)>::new();
    for signature in signatures(plan) {
        let mut argument_schema: BTreeMap<_, _> = signature
            .parameters
            .iter()
            .map(|parameter| (parameter.name.clone(), parameter.type_token.clone()))
            .collect();
        if signature.operation == host::READ {
            argument_schema.insert("key".into(), "Key".into());
        }
        let operation = Operation {
            operation: signature.operation.clone(),
            argument_schema,
            result_schema: signature.result_type.clone(),
        };
        if let Some(previous) = operations.insert(signature.operation.clone(), operation) {
            assert_eq!(
                previous.argument_schema,
                operations[&signature.operation].argument_schema
            );
            assert_eq!(previous.result_schema, signature.result_type);
        }
        let prefix = signature
            .private_key
            .as_deref()
            .and_then(|key| key.rsplit_once('/').map(|(root, _)| format!("{root}/")))
            .unwrap_or_else(|| "lookup/".into());
        let entry = capabilities
            .entry(signature.capability.clone())
            .or_insert_with(|| (prefix.clone(), BTreeSet::new()));
        assert_eq!(entry.0, prefix);
        entry.1.insert(signature.operation.clone());
        providers.push(Provider {
            input: signature.name,
            operation: signature.operation,
            capability: signature.capability,
            arguments: signature
                .private_key
                .map(|key| BTreeMap::from([("key".into(), json!(key))]))
                .unwrap_or_default(),
        });
    }
    let commit_prefix = "noctium/OpenZeppelinPort.Wallet/";
    let mut capability_list = capabilities
        .into_iter()
        .map(|(id, (key_prefix, operations))| Capability {
            id,
            namespace: "noctium".into(),
            key_prefix,
            operations: operations.into_iter().collect(),
        })
        .collect::<Vec<_>>();
    capability_list.push(Capability {
        id: "commit".into(),
        namespace: "noctium".into(),
        key_prefix: commit_prefix.into(),
        operations: vec![host::CAS.into()],
    });
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "genesis-r0".into(),
        attempt_id: attempt_id.into(),
        capabilities: capability_list,
        operations: operations.into_values().collect(),
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn bytes(value: &[u8; 32]) -> Json {
    json!({"kind":"bytes", "values":value.as_slice()})
}

fn point_json(point: EmbeddedGroupAffine) -> Json {
    json!({
        "kind":"jubjubPoint",
        "x":field_decimal(point.x().unwrap()),
        "y":field_decimal(point.y().unwrap())
    })
}

fn point_json_from_coordinates(coordinates: [Fr; 2]) -> Json {
    json!({
        "kind":"jubjubPoint",
        "x":field_decimal(coordinates[0]),
        "y":field_decimal(coordinates[1])
    })
}

fn reply(request: &Json, attempt_id: &str, value: Json) -> TypedResponse {
    serde_json::from_value(json!({
        "protocolVersion":2,
        "requestId":request["requestId"],
        "attemptId":attempt_id,
        "outcome":"value",
        "operation":request["operation"],
        "capability":request["capability"],
        "schema":request["schema"],
        "value":value
    }))
    .unwrap()
}

fn source_inputs(plan: &Json, values: BTreeMap<String, Json>) -> BTreeMap<String, Json> {
    let declared: BTreeSet<_> = plan["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|input| input["name"].as_str().unwrap().to_owned())
        .collect();
    assert_eq!(declared, values.keys().cloned().collect());
    values
}

fn wallet_values(
    plan: &Json,
    account_secret: &[u8; 32],
    encryption_secret: &[u8; 32],
) -> BTreeMap<String, Json> {
    signatures(plan)
        .into_iter()
        .filter_map(|signature| {
            let key = signature.private_key?;
            let value = if key.ends_with("/accountSecret") {
                bytes(account_secret)
            } else if key.ends_with("/encryptionSecret") {
                bytes(encryption_secret)
            } else {
                panic!("unexpected wallet key {key}")
            };
            Some((key, value))
        })
        .collect()
}

#[derive(Clone, Copy)]
struct Ciphertext {
    c1: EmbeddedGroupAffine,
    c2: EmbeddedGroupAffine,
}

#[derive(Clone, Copy)]
struct Memo {
    ephemeral: EmbeddedGroupAffine,
    amount: Fr,
}

fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update(part);
    }
    digest.finalize().into()
}

fn tag(text: &str) -> [u8; 32] {
    assert!(text.len() <= 32);
    let mut result = [0; 32];
    result[..text.len()].copy_from_slice(text.as_bytes());
    result
}

fn scalar(parts: &[&[u8]]) -> EmbeddedFr {
    EmbeddedFr::from_le_bytes(&hash(parts)[..31]).unwrap()
}

fn encryption_scalar(secret: &[u8; 32]) -> EmbeddedFr {
    scalar(&[&tag("ElGamal:secretToScalar"), secret])
}

fn account_id(secret: &[u8; 32]) -> [u8; 32] {
    hash(&[secret])
}

fn epoch_hash(epoch: u64) -> [u8; 32] {
    let encoded = Fr::from(epoch).as_le_bytes();
    hash(&[&encoded])
}

fn coordinates(point: EmbeddedGroupAffine) -> [Fr; 2] {
    [point.x().unwrap(), point.y().unwrap()]
}

fn point_from_coordinates(x: Fr, y: Fr) -> EmbeddedGroupAffine {
    EmbeddedGroupAffine::new(x, y).expect("state coordinates form a Jubjub point")
}

fn expected_credit(
    seed: &[u8; 32],
    recipient: &[u8; 32],
    recipient_key: EmbeddedGroupAffine,
    epoch: u64,
    amount: u64,
) -> (Ciphertext, Memo) {
    let generator = EmbeddedGroupAffine::generator();
    let count_hash = epoch_hash(epoch);
    let balance_randomizer = scalar(&[seed, &tag("credit_balance"), recipient, &count_hash]);
    let memo_randomizer = scalar(&[seed, &tag("credit_memo"), recipient, &count_hash]);
    let ciphertext = Ciphertext {
        c1: generator * balance_randomizer,
        c2: generator * EmbeddedFr::from(amount) + recipient_key * balance_randomizer,
    };
    let ephemeral = generator * memo_randomizer;
    let shared = recipient_key * memo_randomizer;
    let shared_digest = hash(&[
        &shared.x().unwrap().as_le_bytes(),
        &shared.y().unwrap().as_le_bytes(),
    ]);
    let mask_digest = hash(&[&shared_digest, &tag("OZ_CFT_ecdh_memo_v1")]);
    let mask = Fr::from_le_bytes(&mask_digest[..31]).unwrap();
    (
        ciphertext,
        Memo {
            ephemeral,
            amount: Fr::from(amount) + mask,
        },
    )
}

fn expected_debit(
    seed: &[u8; 32],
    owner: Ciphertext,
    owner_key: EmbeddedGroupAffine,
    amount: u64,
) -> Ciphertext {
    expected_debit_with_domain(seed, owner, owner_key, amount, "debit_balance")
}

fn expected_debit_with_domain(
    seed: &[u8; 32],
    owner: Ciphertext,
    owner_key: EmbeddedGroupAffine,
    amount: u64,
    domain: &str,
) -> Ciphertext {
    expected_debit_with_randomizer(owner, owner_key, amount, scalar(&[seed, &tag(domain)]))
}

fn expected_debit_with_randomizer(
    owner: Ciphertext,
    owner_key: EmbeddedGroupAffine,
    amount: u64,
    randomizer: EmbeddedFr,
) -> Ciphertext {
    let generator = EmbeddedGroupAffine::generator();
    let negative_randomizer = EmbeddedFr::from(0u64) - randomizer;
    let negative_one = EmbeddedFr::from(0u64) - EmbeddedFr::from(1u64);
    let value_point = generator * EmbeddedFr::from(amount);
    Ciphertext {
        c1: owner.c1 + generator * negative_randomizer,
        c2: owner.c2 + (value_point + owner_key * randomizer) * negative_one,
    }
}

fn expected_encryption(
    seed: &[u8; 32],
    domain: &str,
    recipient_key: EmbeddedGroupAffine,
    amount: u64,
) -> Ciphertext {
    let generator = EmbeddedGroupAffine::generator();
    let randomizer = scalar(&[seed, &tag(domain)]);
    Ciphertext {
        c1: generator * randomizer,
        c2: generator * EmbeddedFr::from(amount) + recipient_key * randomizer,
    }
}

fn expected_owner_memo(seed: &[u8; 32], owner_key: EmbeddedGroupAffine, amount: u64) -> Memo {
    expected_owner_memo_with_randomizer(
        owner_key,
        amount,
        scalar(&[seed, &tag("approve_owner_memo")]),
    )
}

fn expected_owner_memo_with_randomizer(
    owner_key: EmbeddedGroupAffine,
    amount: u64,
    randomizer: EmbeddedFr,
) -> Memo {
    let generator = EmbeddedGroupAffine::generator();
    let ephemeral = generator * randomizer;
    let shared = owner_key * randomizer;
    let shared_digest = hash(&[
        &shared.x().unwrap().as_le_bytes(),
        &shared.y().unwrap().as_le_bytes(),
    ]);
    let mask_digest = hash(&[&shared_digest, &tag("OZ_CFT_escrow_owner_v1")]);
    let mask = Fr::from_le_bytes(&mask_digest[..31]).unwrap();
    Memo {
        ephemeral,
        amount: Fr::from(amount) + mask,
    }
}

fn spend_randomizer(
    seed: &[u8; 32],
    domain: &str,
    owner: &[u8; 32],
    spender: &[u8; 32],
    epoch: u64,
) -> EmbeddedFr {
    let epoch_bytes = Fr::from(epoch).as_le_bytes();
    scalar(&[seed, &tag(domain), owner, spender, &epoch_bytes])
}

fn expected_escrow_spend(
    seed: &[u8; 32],
    owner: &[u8; 32],
    spender: &[u8; 32],
    epoch: u64,
    amount: u64,
    remaining_amount: u64,
    spender_ciphertext: Ciphertext,
    owner_ciphertext: Ciphertext,
    spender_key: EmbeddedGroupAffine,
    owner_key: EmbeddedGroupAffine,
) -> (Ciphertext, Ciphertext, Memo) {
    let next_spender = expected_debit_with_randomizer(
        spender_ciphertext,
        spender_key,
        amount,
        spend_randomizer(seed, "spend_escrow_spender", owner, spender, epoch),
    );
    let next_owner = expected_debit_with_randomizer(
        owner_ciphertext,
        owner_key,
        amount,
        spend_randomizer(seed, "spend_escrow_owner", owner, spender, epoch),
    );
    let owner_memo = expected_owner_memo_with_randomizer(
        owner_key,
        remaining_amount,
        spend_randomizer(seed, "spend_owner_memo", owner, spender, epoch),
    );
    (next_spender, next_owner, owner_memo)
}

fn decrypt_owner_memo(memo: Memo, owner_secret: EmbeddedFr, maximum: u64) -> u64 {
    let shared = memo.ephemeral * owner_secret;
    let shared_digest = hash(&[
        &shared.x().unwrap().as_le_bytes(),
        &shared.y().unwrap().as_le_bytes(),
    ]);
    let mask_digest = hash(&[&shared_digest, &tag("OZ_CFT_escrow_owner_v1")]);
    let mask = Fr::from_le_bytes(&mask_digest[..31]).unwrap();
    let plaintext = memo.amount - mask;
    (0..=maximum)
        .find(|candidate| Fr::from(*candidate) == plaintext)
        .expect("test escrow memo stays in the bounded search range")
}

fn decrypt_small(ciphertext: Ciphertext, secret: EmbeddedFr, maximum: u64) -> u64 {
    let negative_secret = EmbeddedFr::from(0u64) - secret;
    let message = ciphertext.c2 + ciphertext.c1 * negative_secret;
    let generator = EmbeddedGroupAffine::generator();
    (0..=maximum)
        .find(|candidate| generator * EmbeddedFr::from(*candidate) == message)
        .expect("test balance stays in the bounded discrete-log search range")
}

fn state_slot<'a>(plan: &Plan, state: &'a ChargedState<Db>, name: &str) -> &'a StateValue<Db> {
    let index = plan
        .state
        .iter()
        .position(|field| field.name == name)
        .unwrap();
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected root state array")
    };
    root.get(index).unwrap()
}

fn state_cell<'a>(plan: &Plan, state: &'a ChargedState<Db>, name: &str) -> &'a AlignedValue {
    let StateValue::Cell(cell) = state_slot(plan, state, name) else {
        panic!("expected {name} cell")
    };
    cell
}

fn assert_token_metadata(plan: &Plan, state: &ChargedState<Db>) {
    assert_eq!(
        decode_opaque_string(state_cell(plan, state, "name")).unwrap(),
        "Noctium Token"
    );
    assert_eq!(
        decode_opaque_string(state_cell(plan, state, "symbol")).unwrap(),
        "NOC"
    );
    assert_eq!(
        state_cell(plan, state, "decimals"),
        &field_value(Fr::from(6u64))
    );
}

fn map_record(plan: &Plan, state: &ChargedState<Db>, name: &str, key: &[u8; 32]) -> Vec<Fr> {
    let StateValue::Map(map) = state_slot(plan, state, name) else {
        panic!("expected {name} map")
    };
    let key: AlignedValue = (*key).into();
    let value = map.get(&key).expect("account map entry");
    let StateValue::Cell(cell) = &*value else {
        panic!("expected {name} record cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    fields
}

fn escrow_record(
    plan: &Plan,
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
) -> Vec<Fr> {
    let StateValue::Map(owners) = state_slot(plan, state, "escrow") else {
        panic!("expected escrow owner map")
    };
    let owner: AlignedValue = (*owner).into();
    let StateValue::Map(spenders) = &*owners.get(&owner).expect("escrow owner map entry") else {
        panic!("expected escrow spender map")
    };
    let spender: AlignedValue = (*spender).into();
    let StateValue::Cell(record) = &*spenders.get(&spender).expect("escrow spender entry") else {
        panic!("expected escrow record cell")
    };
    let mut fields = Vec::new();
    record.value_only_field_repr(&mut fields);
    fields
}

fn escrow_spend_epoch_record(
    plan: &Plan,
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
) -> Vec<Fr> {
    let StateValue::Map(owners) = state_slot(plan, state, "escrowSpendEpochs") else {
        panic!("expected escrow-spend epoch owner map")
    };
    let owner: AlignedValue = (*owner).into();
    let StateValue::Map(spenders) = &*owners.get(&owner).expect("spend epoch owner entry") else {
        panic!("expected escrow-spend epoch spender map")
    };
    let spender: AlignedValue = (*spender).into();
    let StateValue::Cell(epoch) = &*spenders.get(&spender).expect("spend epoch spender entry")
    else {
        panic!("expected spend epoch cell")
    };
    let mut fields = Vec::new();
    epoch.value_only_field_repr(&mut fields);
    fields
}

fn escrow_ciphertexts(fields: &[Fr]) -> (Ciphertext, Ciphertext, Memo) {
    (
        ciphertext_from_fields(fields, 0),
        ciphertext_from_fields(fields, 4),
        Memo {
            ephemeral: point_from_coordinates(fields[8], fields[9]),
            amount: fields[10],
        },
    )
}

fn ciphertext_from_fields(fields: &[Fr], offset: usize) -> Ciphertext {
    Ciphertext {
        c1: point_from_coordinates(fields[offset], fields[offset + 1]),
        c2: point_from_coordinates(fields[offset + 2], fields[offset + 3]),
    }
}

fn add_ciphertexts(left: Ciphertext, right: Ciphertext) -> Ciphertext {
    Ciphertext {
        c1: left.c1 + right.c1,
        c2: left.c2 + right.c2,
    }
}

fn assert_ciphertext(
    plan: &Plan,
    state: &ChargedState<Db>,
    map: &str,
    key: &[u8; 32],
    expected: Ciphertext,
) {
    let mut fields = coordinates(expected.c1).to_vec();
    fields.extend(coordinates(expected.c2));
    assert_eq!(
        map_record(plan, state, map, key),
        fields,
        "{map} ciphertext"
    );
}

fn assert_escrow(
    plan: &Plan,
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
    spender_ciphertext: Ciphertext,
    owner_ciphertext: Ciphertext,
    owner_memo: Memo,
) {
    let mut expected = coordinates(spender_ciphertext.c1).to_vec();
    expected.extend(coordinates(spender_ciphertext.c2));
    expected.extend(coordinates(owner_ciphertext.c1));
    expected.extend(coordinates(owner_ciphertext.c2));
    expected.extend(coordinates(owner_memo.ephemeral));
    expected.push(owner_memo.amount);
    assert_eq!(escrow_record(plan, state, owner, spender), expected);
}

fn assert_record(
    plan: &Plan,
    state: &ChargedState<Db>,
    map: &str,
    key: &[u8; 32],
    expected: &[Fr],
) {
    assert_eq!(map_record(plan, state, map, key), expected, "{map} record");
}

fn memo_records(plan: &Plan, state: &ChargedState<Db>, key: &[u8; 32]) -> (usize, Vec<Vec<Fr>>) {
    fn walk(node: &StateValue<Db>, output: &mut Vec<Vec<Fr>>) -> usize {
        let StateValue::Array(parts) = node else {
            panic!("expected native List array")
        };
        let StateValue::Cell(length) = parts.get(2).unwrap() else {
            panic!("expected List length cell")
        };
        let mut length_fields = Vec::new();
        length.value_only_field_repr(&mut length_fields);
        let declared: usize = field_decimal(length_fields[0]).parse().unwrap();
        if matches!(parts.get(0), Some(StateValue::Null)) {
            assert!(matches!(parts.get(1), Some(StateValue::Null)));
            assert_eq!(declared, 0);
            return 0;
        }
        let StateValue::Cell(record) = parts.get(0).unwrap() else {
            panic!("expected memo record cell")
        };
        let mut fields = Vec::new();
        record.value_only_field_repr(&mut fields);
        output.push(fields);
        let tail = walk(parts.get(1).unwrap(), output);
        assert_eq!(declared, tail + 1);
        tail + 1
    }

    let StateValue::Map(map) = state_slot(plan, state, "memos") else {
        panic!("expected memos map")
    };
    let key: AlignedValue = (*key).into();
    let value = map.get(&key).expect("memo list map entry");
    let mut records = Vec::new();
    let length = walk(&value, &mut records);
    (length, records)
}

fn attempt(number: u64) -> String {
    format!("{number:064x}")
}

fn run_entry(
    entry: &str,
    values: BTreeMap<String, Json>,
    account_secret: &[u8; 32],
    encryption_secret: &[u8; 32],
    seeds: &[[u8; 32]],
    decrypt_balance: Option<Ciphertext>,
    attempt_number: u64,
    prior_state: &ChargedState<Db>,
) -> Result<(ChargedState<Db>, BTreeMap<String, Json>), String> {
    let (control_text, native_text, circuit_bytes) = artifacts(entry);
    let control_plan: Json = serde_json::from_str(control_text).unwrap();
    let native_plan: Plan = serde_json::from_str(native_text).unwrap();
    let circuit = IrSource::load(circuit_bytes).unwrap();
    let expected_caller = values
        .get("accountId")
        .or_else(|| values.get("spenderId"))
        .cloned();
    let native_inputs = collect_native_inputs(
        entry,
        &control_plan,
        values,
        account_secret,
        encryption_secret,
        seeds,
        decrypt_balance,
        attempt_number,
    );
    let execution = prepare(
        &native_plan,
        &native_inputs,
        prior_state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).map_err(|error| error.to_string())?;
    if matches!(
        entry,
        "registerWithKey"
            | "sweep"
            | "transfer"
            | "_move"
            | "burn"
            | "approve"
            | "transferFrom"
            | "burnFrom"
    ) {
        assert_eq!(
            execution.returns_json()["caller"],
            expected_caller.expect("caller return needs accountId")
        );
    }
    Ok((execution.after.state.clone(), native_inputs))
}

fn collect_native_inputs(
    entry: &str,
    control_plan: &Json,
    values: BTreeMap<String, Json>,
    account_secret: &[u8; 32],
    encryption_secret: &[u8; 32],
    seeds: &[[u8; 32]],
    decrypt_balance: Option<Ciphertext>,
    attempt_number: u64,
) -> BTreeMap<String, Json> {
    let source_inputs = source_inputs(control_plan, values);
    let attempt_id = attempt(attempt_number);
    let binding: Json = serde_json::from_str(control_plan["binding"].as_str().unwrap()).unwrap();
    let digest = hex::encode(Sha256::digest(
        control_plan["binding"].as_str().unwrap().as_bytes(),
    ));
    let wallet = wallet_values(control_plan, account_secret, encryption_secret);
    let mut session = Session::from_json_with_invocation_target(
        control_plan.clone(),
        source_inputs,
        context(control_plan, &attempt_id),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: entry.into(),
        }),
    )
    .unwrap_or_else(|error| panic!("{entry}: {error:#}"));
    let mut callbacks = BTreeSet::new();
    let mut reads = BTreeSet::new();
    let mut fresh_seeds = seeds.iter();
    loop {
        let status = session.advance().unwrap();
        if status["status"] != "need_host" {
            assert_eq!(status["status"], "completed", "{entry}: {status}");
            break;
        }
        let request = &status["request"];
        let private = session.private_request().unwrap();
        let value = if request["operation"] == host::READ {
            let key = private["arguments"]["key"].as_str().unwrap();
            reads.insert(key.to_owned());
            wallet
                .get(key)
                .unwrap_or_else(|| panic!("missing wallet value for {key}"))
                .clone()
        } else {
            let name = request["name"].as_str().unwrap();
            callbacks.insert(name.to_owned());
            match name {
                "OpenZeppelinPort.freshSeed" => bytes(
                    fresh_seeds
                        .next()
                        .expect("freshSeed callback needs a deterministic test seed"),
                ),
                "OpenZeppelinPort.plaintextBalance" => {
                    let expected =
                        decrypt_balance.expect("plaintext callback needs expected state balance");
                    assert_eq!(private["arguments"]["c1"], point_json(expected.c1));
                    assert_eq!(private["arguments"]["c2"], point_json(expected.c2));
                    let secret = encryption_scalar(encryption_secret);
                    json!(decrypt_small(expected, secret, 64).to_string())
                }
                other => panic!("unexpected witness callback {other}"),
            }
        };
        session
            .resume_typed(reply(request, &attempt_id, value))
            .unwrap_or_else(|error| panic!("{entry} response {:?}: {error}", request["name"]));
    }
    assert!(
        fresh_seeds.next().is_none(),
        "{entry} left deterministic seeds unused"
    );
    let expected_reads = if wallet.is_empty() {
        BTreeSet::new()
    } else {
        wallet.keys().cloned().collect()
    };
    assert_eq!(reads, expected_reads, "{entry} wallet reads");
    let expected_callbacks: BTreeSet<String> = match entry {
        "mint" => ["OpenZeppelinPort.freshSeed".into()].into(),
        "transfer" | "_move" | "burn" | "approve" | "transferFrom" | "burnFrom" => [
            "OpenZeppelinPort.freshSeed".into(),
            "OpenZeppelinPort.plaintextBalance".into(),
        ]
        .into(),
        _ => BTreeSet::new(),
    };
    assert_eq!(callbacks, expected_callbacks, "{entry} callbacks");
    let relation = binding["nativeRelation"].clone();
    let completion = session.private_completion(&relation).unwrap();
    serde_json::from_value(completion["inputs"].clone()).unwrap()
}

fn initial_state(plan: &Plan) -> ChargedState<Db> {
    construct_state(
        plan,
        &BTreeMap::from([
            ("name_".into(), json!("Noctium Token")),
            ("symbol_".into(), json!("NOC")),
            ("decimals_".into(), json!("6")),
        ]),
    )
    .unwrap()
}

#[test]
#[ignore = "requires fresh callee and caller plans in NOCTIUM_MINT_BINDING_ARTIFACTS"]
fn confidential_token_mint_binds_recipient_and_amount_across_calls() -> anyhow::Result<()> {
    use base_crypto::hash::HashOutput;
    use coin_structure::contract::ContractAddress;
    use ledger::structure::INITIAL_PARAMETERS;
    use noctium_runtime::{
        Execution,
        assembly::{CheckedNativeCall, assemble_checked_calls},
        create_state,
    };
    use onchain_runtime::{context::QueryContext, state::EntryPointBuf};
    use rand::rngs::OsRng;
    use std::{fs::File, path::PathBuf};

    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_MINT_BINDING_ARTIFACTS")
            .expect("set the directory containing fresh callee and caller artifacts"),
    );
    let mint = directory.join("callee/OpenZeppelinPort.ConfidentialToken.mint");
    let claim = directory.join("caller/OpenZeppelinPort.TokenMinter.claimMint");
    let artifact = |stem: &std::path::Path, extension: &str| {
        let mut name = stem.as_os_str().to_owned();
        name.push(extension);
        File::open(name)
    };
    let mint_control: Json = serde_json::from_reader(artifact(&mint, ".witness.control.json")?)?;
    let mint_plan: Plan = serde_json::from_reader(artifact(&mint, ".impact.json")?)?;
    let mint_circuit = IrSource::load(artifact(&mint, ".zkir")?)?;
    let caller_plan: Plan = serde_json::from_reader(artifact(&claim, ".impact.json")?)?;
    let caller_circuit = IrSource::load(artifact(&claim, ".zkir")?)?;

    let account_secret = [17; 32];
    let encryption_secret = [7; 32];
    let recipient = account_id(&account_secret);
    let recipient_key = EmbeddedGroupAffine::generator() * encryption_scalar(&encryption_secret);
    let register_plan = serde_json::from_str(artifacts("registerWithKey").1)?;
    let (mint_initial, _) = run_entry(
        "registerWithKey",
        BTreeMap::from([
            ("accountId".into(), bytes(&recipient)),
            ("pk".into(), point_json(recipient_key)),
        ]),
        &account_secret,
        &encryption_secret,
        &[],
        None,
        1,
        &initial_state(&register_plan),
    )
    .map_err(anyhow::Error::msg)?;

    let callee = ContractAddress(HashOutput([0xaa; 32]));
    let caller = ContractAddress(HashOutput([0xc2; 32]));
    let seed = [0x31; 32];
    let amount = 12u64;
    let opening = Fr::from(113u64);
    let mut mint_inputs = BTreeMap::from([
        ("recipient".into(), bytes(&recipient)),
        ("value".into(), json!(amount.to_string())),
        ("recipientPk".into(), point_json(recipient_key)),
        ("epoch".into(), json!("1")),
    ]);
    for (name, field) in ["previousC1X", "previousC1Y", "previousC2X", "previousC2Y"]
        .into_iter()
        .zip(map_record(&mint_plan, &mint_initial, "pending", &recipient))
    {
        mint_inputs.insert(name.into(), json!(field_decimal(field)));
    }
    let native_mint_inputs = collect_native_inputs(
        "mint",
        &mint_control,
        mint_inputs,
        &account_secret,
        &encryption_secret,
        &[seed],
        None,
        2,
    );
    let mint_execution = prepare(
        &mint_plan,
        &native_mint_inputs,
        &mint_initial,
        &INITIAL_PARAMETERS,
        callee,
    )?;
    check(&mint_execution, &mint_circuit)?;
    let after = &mint_execution.after.state;
    assert_eq!(
        state_cell(&mint_plan, after, "totalSupply"),
        &field_value(Fr::from(amount))
    );
    assert_eq!(
        map_record(&mint_plan, after, "creditEpochs", &recipient),
        vec![Fr::from(1u64)]
    );
    let (pending, memo) = expected_credit(&seed, &recipient, recipient_key, 1, amount);
    assert_ciphertext(&mint_plan, after, "pending", &recipient, pending);
    assert_eq!(
        memo_records(&mint_plan, after, &recipient),
        (
            1,
            vec![vec![
                memo.ephemeral.x().unwrap(),
                memo.ephemeral.y().unwrap(),
                memo.amount
            ]]
        )
    );

    let caller_initial = create_state(
        &caller_plan,
        &BTreeMap::from([
            ("route".into(), bytes(&callee.0.0)),
            ("issuanceCount".into(), json!("0")),
        ]),
    )?;
    let prepare_caller = |recipient: &[u8; 32], amount: u64| -> anyhow::Result<Execution> {
        let execution = prepare(
            &caller_plan,
            &BTreeMap::from([
                ("opening".into(), json!(field_decimal(opening))),
                ("recipient".into(), bytes(recipient)),
                ("value".into(), json!(amount.to_string())),
            ]),
            &caller_initial,
            &INITIAL_PARAMETERS,
            caller,
        )?;
        check(&execution, &caller_circuit)?;
        assert_eq!(
            state_cell(&caller_plan, &execution.after.state, "issuanceCount"),
            &AlignedValue::from(1u64)
        );
        Ok(execution)
    };
    let assemble = |execution: &Execution| {
        assemble_checked_calls(
            &[
                CheckedNativeCall {
                    execution,
                    circuit: &caller_circuit,
                    initial_context: QueryContext::new(caller_initial.clone(), caller),
                    entry_point: EntryPointBuf(b"claimMint".to_vec()),
                    communication_commitment_rand: Fr::from(53u64),
                },
                CheckedNativeCall {
                    execution: &mint_execution,
                    circuit: &mint_circuit,
                    initial_context: QueryContext::new(mint_initial.clone(), callee),
                    entry_point: EntryPointBuf(b"mint".to_vec()),
                    communication_commitment_rand: opening,
                },
            ],
            &INITIAL_PARAMETERS,
            1_800_000_000,
            &mut OsRng,
        )
    };
    let matched = assemble(&prepare_caller(&recipient, amount)?)?;
    let mut calls = matched.calls();
    let caller_call = calls.next().expect("checked caller");
    let mint_call = calls.next().expect("checked mint");
    assert!(caller_call.calls(mint_call));
    assert!(calls.next().is_none());

    let other_recipient = account_id(&[18; 32]);
    for (changed_recipient, changed_amount) in
        [(&recipient, amount + 1), (&other_recipient, amount)]
    {
        let independently_checked = prepare_caller(changed_recipient, changed_amount)?;
        let error = match assemble(&independently_checked) {
            Err(error) => error,
            Ok(_) => panic!("changed mint commitment passed checked intent assembly"),
        };
        assert!(
            matches!(
                error.to_string().as_str(),
                "official native call forest partition failed"
                    | "contract claim has no matching later call in this intent"
            ),
            "{error:#}"
        );
    }
    Ok(())
}

#[cfg(feature = "localnet")]
#[test]
#[ignore = "uses the pinned mint bundles, isolated localnet and two proof-owner processes"]
fn confidential_token_funded_mint_finalizes_registered_key_and_checked_pair() -> anyhow::Result<()>
{
    use base_crypto::time::Timestamp;
    use futures::executor::block_on;
    use ledger::structure::ContractDeploy;
    use noctium_runtime::{
        artifacts::{self, Role, VerifiedBundle},
        assembly::{CheckedNativeCall, CompositionOffer, NativeIntent},
        client::{BoundTransaction, ChainAdapter, NetworkPolicy, Submission},
        create_state,
        funding::{CONTRACT_SEGMENT, FeePolicy, UnsealedTransaction},
        localnet::{DevelopmentFunding, ExplicitSeal, Node, ProofCache},
        proof::{
            CompositionDraft, CompositionMaterial, Error as CompositionError,
            IndependentComposition, TrustedParameters,
        },
        zkir::IrSource,
    };
    use onchain_runtime::{
        context::QueryContext,
        state::{ContractOperation, ContractState, EntryPointBuf},
    };
    use rand::{SeedableRng, rngs::StdRng};
    use serialize::tagged_deserialize;
    use std::{
        env, fs,
        io::{BufRead, BufReader, Write},
        path::Path,
        process::{Child, ChildStdin, ChildStdout, Command, Stdio},
        time::{Duration, Instant},
    };
    use transient_crypto::{
        curve::Fr,
        proofs::{VerifierKey, Zkir},
    };

    const OWNER_ROLE: &str = "NOCTIUM_CONFIDENTIAL_MINT_OWNER_ROLE";
    // Shared at owner startup only, outside the public offer, draft and proof frames.
    const OWNER_OPENING_FIXTURE: &str = "NOCTIUM_CONFIDENTIAL_MINT_OPENING_FIXTURE";
    const OWNER_REPLY: &str = "NOCTIUM_CONFIDENTIAL_MINT_OWNER ";
    const TEST_OPENING: &str = "113";

    struct Material {
        bundle: VerifiedBundle,
        plan: Plan,
        control: Option<Json>,
        circuit: IrSource,
        parameters: TrustedParameters,
    }

    fn load_bundle(root: &Path, role: &str) -> anyhow::Result<VerifiedBundle> {
        let upper = role.to_ascii_uppercase();
        let path = root.join(format!("{role}-bundle"));
        let pin = env::var(format!("NOCTIUM_CONFIDENTIAL_MINT_{upper}_SHA256"))?;
        Ok(artifacts::verify(&path, Some(&pin))?)
    }

    fn load_material(root: &Path, srs_dir: &Path, role: &str) -> anyhow::Result<Material> {
        let bundle = load_bundle(root, role)?;
        let plan: Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
        let control = bundle
            .file(Role::WitnessControl)
            .ok()
            .map(serde_json::from_slice)
            .transpose()?;
        anyhow::ensure!(
            role == "caller" || control.is_some(),
            "{role} bundle has no witness control"
        );
        let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
        let upper = role.to_ascii_uppercase();
        let parameters = TrustedParameters::from_bytes(
            &fs::read(srs_dir.join(format!("bls_midnight_2p{}", circuit.k())))?,
            circuit.k(),
            &env::var(format!("NOCTIUM_CONFIDENTIAL_MINT_{upper}_SRS_SHA256"))?,
        )?;
        Ok(Material {
            bundle,
            plan,
            control,
            circuit,
            parameters,
        })
    }

    fn deployment(
        data: ChargedState<Db>,
        operations: &[(&str, &VerifiedBundle)],
    ) -> anyhow::Result<ContractDeploy<Db>> {
        let mut contract = ContractState::<Db>::default();
        contract.data = data;
        for (name, bundle) in operations {
            let mut key_bytes = bundle.file(Role::VerifierKey)?;
            let verifier: VerifierKey = tagged_deserialize(&mut key_bytes)?;
            anyhow::ensure!(key_bytes.is_empty(), "verifier key has trailing bytes");
            contract.operations = contract.operations.insert(
                EntryPointBuf(name.as_bytes().to_vec()),
                ContractOperation::new(Some(verifier), None),
            );
        }
        Ok(ContractDeploy::new(&mut StdRng::from_entropy(), contract))
    }

    fn contract_state(bytes: &[u8]) -> anyhow::Result<ContractState<Db>> {
        let mut reader = bytes;
        let state = tagged_deserialize(&mut reader)?;
        anyhow::ensure!(reader.is_empty(), "receipt state has trailing bytes");
        Ok(state)
    }

    fn expected_contract_state(
        initial: &ContractState<Db>,
        expected_data: &ChargedState<Db>,
    ) -> anyhow::Result<Vec<u8>> {
        let mut expected = initial.clone();
        expected.data = expected_data.clone();
        let mut bytes = Vec::new();
        serialize::tagged_serialize(&expected, &mut bytes)?;
        Ok(bytes)
    }

    fn receive_owner_message(reader: &mut impl BufRead) -> anyhow::Result<Json> {
        loop {
            let mut line = String::new();
            anyhow::ensure!(
                reader.read_line(&mut line)? != 0,
                "confidential-mint proof owner stopped before replying"
            );
            anyhow::ensure!(line.len() <= 34 * 1024 * 1024, "owner frame exceeds limit");
            if let Some((_, message)) = line.split_once(OWNER_REPLY) {
                return Ok(serde_json::from_str(message)?);
            }
        }
    }

    fn send_owner_message(writer: &mut impl Write, message: &Json) -> anyhow::Result<()> {
        writeln!(writer, "{OWNER_REPLY}{message}")?;
        writer.flush()?;
        Ok(())
    }

    fn owner_payload(message: &Json, field: &str) -> anyhow::Result<Vec<u8>> {
        Ok(hex::decode(message[field].as_str().ok_or_else(|| {
            anyhow::anyhow!("owner omitted {field}")
        })?)?)
    }

    fn owner_address(
        message: &Json,
        field: &str,
    ) -> anyhow::Result<coin_structure::contract::ContractAddress> {
        let bytes: [u8; 32] = owner_payload(message, field)?
            .try_into()
            .map_err(|_| anyhow::anyhow!("owner address has the wrong length"))?;
        Ok(coin_structure::contract::ContractAddress(
            base_crypto::hash::HashOutput(bytes),
        ))
    }

    struct OwnerProcess {
        child: Child,
        input: ChildStdin,
        output: BufReader<ChildStdout>,
    }

    impl OwnerProcess {
        fn spawn(role: &str) -> anyhow::Result<Self> {
            let mut child = Command::new(env::current_exe()?)
                .args([
                    "--exact",
                    "confidential_token_funded_mint_finalizes_registered_key_and_checked_pair",
                    "--ignored",
                    "--nocapture",
                ])
                .env(OWNER_ROLE, role)
                .env(OWNER_OPENING_FIXTURE, TEST_OPENING)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()?;
            Ok(Self {
                input: child
                    .stdin
                    .take()
                    .ok_or_else(|| anyhow::anyhow!("owner stdin unavailable"))?,
                output: BufReader::new(
                    child
                        .stdout
                        .take()
                        .ok_or_else(|| anyhow::anyhow!("owner stdout unavailable"))?,
                ),
                child,
            })
        }

        fn send(&mut self, message: &Json) -> anyhow::Result<()> {
            send_owner_message(&mut self.input, message)
        }

        fn receive(&mut self) -> anyhow::Result<Json> {
            receive_owner_message(&mut self.output)
        }

        fn finish(&mut self) -> anyhow::Result<()> {
            anyhow::ensure!(self.child.wait()?.success(), "proof owner process failed");
            Ok(())
        }
    }

    impl Drop for OwnerProcess {
        fn drop(&mut self) {
            if self.child.try_wait().ok().flatten().is_none() {
                let _ = self.child.kill();
                let _ = self.child.wait();
            }
        }
    }

    async fn prove_deployment(
        deployment: &ContractDeploy<Db>,
        ttl: u64,
        node: &Node,
        dust: &noctium_runtime::funding::DustMaterial,
        dust_parameters: &TrustedParameters,
    ) -> anyhow::Result<noctium_runtime::proof::ProvedNativeIntent> {
        let snapshot = node.sync()?;
        let intent = NativeIntent::empty(&mut StdRng::from_entropy(), Timestamp::from_secs(ttl))
            .add_deploy(deployment.clone());
        let provider = builtin_zkir::LocalProvingProvider {
            rng: StdRng::from_entropy(),
            resolver: dust,
            params: dust_parameters,
        };
        let (_, proved) = intent
            .prove(
                CONTRACT_SEGMENT,
                provider,
                &snapshot.state.parameters.cost_model.runtime_cost_model,
            )
            .await?;
        Ok(proved)
    }

    async fn finalize(
        node: &Node,
        policy: &NetworkPolicy,
        dust: &noctium_runtime::funding::DustMaterial,
        dust_parameters: &TrustedParameters,
        intent: &noctium_runtime::proof::ProvedNativeIntent,
    ) -> anyhow::Result<noctium_runtime::client::FinalizedReceipt> {
        let funding = DevelopmentFunding::new(
            node,
            dust,
            dust_parameters,
            FeePolicy {
                max_dust: policy.max_dust,
                margin_blocks: 3,
                max_spends: 8,
            },
            StdRng::from_entropy(),
        );
        let signer = ExplicitSeal::new(
            |_: &UnsealedTransaction, candidate: &NetworkPolicy| candidate == policy,
            StdRng::from_entropy(),
        );
        let bound =
            BoundTransaction::prepare(intent, policy.clone(), node, &funding, &signer).await?;
        anyhow::ensure!(
            node.submit(&bound)
                .await
                .map_err(|_| anyhow::anyhow!("localnet submit failed"))?
                != Submission::Rejected,
            "localnet rejected the funded confidential-token transaction"
        );
        let deadline = Instant::now() + Duration::from_secs(120);
        loop {
            if let Some(receipt) = node.finalized_receipt(&bound)? {
                bound.check_receipt(&receipt)?;
                return Ok(receipt);
            }
            anyhow::ensure!(
                Instant::now() < deadline,
                "localnet receipt did not finalize"
            );
            std::thread::sleep(Duration::from_secs(1));
        }
    }

    async fn owner_worker() -> anyhow::Result<()> {
        use transient_crypto::curve::EmbeddedGroupAffine;

        let role = env::var(OWNER_ROLE)?;
        let bundles_root = Path::new(&env::var("NOCTIUM_CONFIDENTIAL_MINT_BUNDLES")?).to_path_buf();
        let srs_dir = Path::new(&env::var("NOCTIUM_CONFIDENTIAL_MINT_SRS")?).to_path_buf();
        let endpoint = env::var("NOCTIUM_CONFIDENTIAL_MINT_NODE")?;
        anyhow::ensure!(
            endpoint == "http://127.0.0.1:19944",
            "proof owner only permits the isolated development localnet"
        );
        let opening = Fr::from(env::var(OWNER_OPENING_FIXTURE)?.parse::<u64>()?);
        let policy = NetworkPolicy {
            network_id: "undeployed".into(),
            genesis: "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d".into(),
            spec_version: 2_001_100,
            transaction_version: 4,
            profile: noctium_runtime::profile::NAME.into(),
            max_dust: 10u128.pow(22),
        };
        let node = Node::connect(
            &endpoint,
            policy,
            Duration::from_secs(30),
            64 * 1024 * 1024,
            100_000,
        )?;
        let mut input = BufReader::new(std::io::stdin());
        let mut output = std::io::stdout();

        match role.as_str() {
            "caller" => {
                let caller = load_material(&bundles_root, &srs_dir, "caller")?;
                anyhow::ensure!(
                    caller.control.is_none(),
                    "caller must use an ordinary circuit"
                );
                anyhow::ensure!(
                    caller.plan.entrypoint == "claimMint",
                    "unexpected caller entrypoint"
                );
                let request = receive_owner_message(&mut input)?;
                anyhow::ensure!(request["kind"] == "mint", "caller expected mint request");
                let address = owner_address(&request, "address")?;
                let recipient: [u8; 32] = hex::decode(
                    request["recipient"]
                        .as_str()
                        .ok_or_else(|| anyhow::anyhow!("caller request omitted recipient"))?,
                )?
                .try_into()
                .map_err(|_| anyhow::anyhow!("caller recipient has the wrong length"))?;
                let amount = 12u64;
                let ttl = request["ttl"]
                    .as_u64()
                    .ok_or_else(|| anyhow::anyhow!("caller request omitted TTL"))?;
                let snapshot = node.sync()?;
                let initial = snapshot
                    .state
                    .contract
                    .get(&address)
                    .ok_or_else(|| anyhow::anyhow!("caller contract missing from owner snapshot"))?
                    .clone();
                let execution = prepare(
                    &caller.plan,
                    &BTreeMap::from([
                        ("opening".into(), json!(field_decimal(opening))),
                        ("recipient".into(), bytes(&recipient)),
                        ("value".into(), json!(amount.to_string())),
                    ]),
                    &initial.data,
                    &snapshot.state.parameters,
                    address,
                )?;
                check(&execution, &caller.circuit)?;
                anyhow::ensure!(
                    state_cell(&caller.plan, &execution.after.state, "issuanceCount")
                        == &AlignedValue::from(1u64),
                    "caller source transition did not increment issuanceCount"
                );
                let call = CheckedNativeCall {
                    execution: &execution,
                    circuit: &caller.circuit,
                    initial_context: QueryContext::new(initial.data.clone(), address),
                    entry_point: EntryPointBuf(b"claimMint".to_vec()),
                    communication_commitment_rand: Fr::from(53u64),
                };
                let offer = call.composition_offer(&snapshot.state.parameters)?;
                let expected_state = expected_contract_state(&initial, &execution.after.state)?;
                send_owner_message(
                    &mut output,
                    &json!({
                        "kind":"offer",
                        "offer":hex::encode(offer.public_bytes()?),
                        "expectedState":hex::encode(expected_state),
                    }),
                )?;
                let request = receive_owner_message(&mut input)?;
                anyhow::ensure!(
                    request["kind"] == "draft",
                    "caller expected composition draft"
                );
                let draft = CompositionDraft::from_public_bytes(
                    &owner_payload(&request, "draft")?,
                    &snapshot.state,
                )?;
                anyhow::ensure!(draft.ttl() == ttl, "caller draft TTL changed");
                let proof = draft
                    .prove_call(
                        0,
                        &call,
                        &snapshot.state,
                        &CompositionMaterial {
                            bundle: &caller.bundle,
                            parameters: &caller.parameters,
                        },
                        rand::rngs::OsRng,
                    )
                    .await?;
                send_owner_message(
                    &mut output,
                    &json!({"kind":"proof", "proof":hex::encode(proof)}),
                )?;
            }
            "callee" => {
                let register = load_material(&bundles_root, &srs_dir, "register")?;
                let mint = load_material(&bundles_root, &srs_dir, "mint")?;
                anyhow::ensure!(
                    register.plan.entrypoint == "registerWithKey" && mint.plan.entrypoint == "mint",
                    "unexpected callee entrypoint"
                );
                let account_secret = [17; 32];
                let encryption_secret = [7; 32];
                let recipient = account_id(&account_secret);
                let recipient_key =
                    EmbeddedGroupAffine::generator() * encryption_scalar(&encryption_secret);
                let seed = [0x31; 32];

                let request = receive_owner_message(&mut input)?;
                anyhow::ensure!(
                    request["kind"] == "register",
                    "callee expected registration setup"
                );
                let address = owner_address(&request, "address")?;
                let ttl = request["ttl"]
                    .as_u64()
                    .ok_or_else(|| anyhow::anyhow!("registration request omitted TTL"))?;
                let snapshot = node.sync()?;
                let initial = snapshot
                    .state
                    .contract
                    .get(&address)
                    .ok_or_else(|| anyhow::anyhow!("token contract missing from owner snapshot"))?
                    .clone();
                let registration_inputs = collect_native_inputs(
                    "registerWithKey",
                    register.control.as_ref().ok_or_else(|| {
                        anyhow::anyhow!("registration bundle has no witness control")
                    })?,
                    BTreeMap::from([
                        ("accountId".into(), bytes(&recipient)),
                        ("pk".into(), point_json(recipient_key)),
                    ]),
                    &account_secret,
                    &encryption_secret,
                    &[],
                    None,
                    1,
                );
                let execution = prepare(
                    &register.plan,
                    &registration_inputs,
                    &initial.data,
                    &snapshot.state.parameters,
                    address,
                )?;
                check(&execution, &register.circuit)?;
                assert_record(
                    &register.plan,
                    &execution.after.state,
                    "encryptionKeys",
                    &recipient,
                    &coordinates(recipient_key),
                );
                let call = CheckedNativeCall {
                    execution: &execution,
                    circuit: &register.circuit,
                    initial_context: QueryContext::new(initial.data.clone(), address),
                    entry_point: EntryPointBuf(b"registerWithKey".to_vec()),
                    communication_commitment_rand: Fr::from(41u64),
                };
                let offer = call.composition_offer(&snapshot.state.parameters)?;
                let expected_state = expected_contract_state(&initial, &execution.after.state)?;
                send_owner_message(
                    &mut output,
                    &json!({
                        "kind":"registration-offer",
                        "offer":hex::encode(offer.public_bytes()?),
                        "recipient":hex::encode(recipient),
                        "recipientKey":point_json(recipient_key),
                        "expectedState":hex::encode(expected_state),
                    }),
                )?;
                let request = receive_owner_message(&mut input)?;
                anyhow::ensure!(
                    request["kind"] == "draft",
                    "callee expected registration draft"
                );
                let draft = CompositionDraft::from_public_bytes(
                    &owner_payload(&request, "draft")?,
                    &snapshot.state,
                )?;
                anyhow::ensure!(draft.ttl() == ttl, "registration draft TTL changed");
                let proof = draft
                    .prove_call(
                        0,
                        &call,
                        &snapshot.state,
                        &CompositionMaterial {
                            bundle: &register.bundle,
                            parameters: &register.parameters,
                        },
                        rand::rngs::OsRng,
                    )
                    .await?;
                send_owner_message(
                    &mut output,
                    &json!({"kind":"registration-proof", "proof":hex::encode(proof)}),
                )?;

                let request = receive_owner_message(&mut input)?;
                anyhow::ensure!(request["kind"] == "mint", "callee expected mint request");
                anyhow::ensure!(
                    request["recipient"] == hex::encode(recipient),
                    "callee mint request changed the registered recipient"
                );
                let amount = 12u64;
                let mint_ttl = request["ttl"]
                    .as_u64()
                    .ok_or_else(|| anyhow::anyhow!("mint request omitted TTL"))?;
                let snapshot = node.sync()?;
                let initial = snapshot
                    .state
                    .contract
                    .get(&address)
                    .ok_or_else(|| anyhow::anyhow!("registered token missing from owner snapshot"))?
                    .clone();
                let mut mint_values = BTreeMap::from([
                    ("recipient".into(), bytes(&recipient)),
                    ("value".into(), json!(amount.to_string())),
                    ("recipientPk".into(), point_json(recipient_key)),
                    ("epoch".into(), json!("1")),
                ]);
                for (name, field) in ["previousC1X", "previousC1Y", "previousC2X", "previousC2Y"]
                    .into_iter()
                    .zip(map_record(&mint.plan, &initial.data, "pending", &recipient))
                {
                    mint_values.insert(name.into(), json!(field_decimal(field)));
                }
                let mint_inputs = collect_native_inputs(
                    "mint",
                    mint.control
                        .as_ref()
                        .ok_or_else(|| anyhow::anyhow!("mint bundle has no witness control"))?,
                    mint_values,
                    &account_secret,
                    &encryption_secret,
                    &[seed],
                    None,
                    3,
                );
                let execution = prepare(
                    &mint.plan,
                    &mint_inputs,
                    &initial.data,
                    &snapshot.state.parameters,
                    address,
                )?;
                check(&execution, &mint.circuit)?;
                anyhow::ensure!(
                    state_cell(&mint.plan, &execution.after.state, "totalSupply")
                        == &field_value(Fr::from(amount)),
                    "mint did not update totalSupply"
                );
                anyhow::ensure!(
                    map_record(
                        &mint.plan,
                        &execution.after.state,
                        "creditEpochs",
                        &recipient
                    ) == vec![Fr::from(1u64)],
                    "mint did not set recipient credit epoch"
                );
                let (pending_ciphertext, memo) =
                    expected_credit(&seed, &recipient, recipient_key, 1, amount);
                assert_ciphertext(
                    &mint.plan,
                    &execution.after.state,
                    "pending",
                    &recipient,
                    pending_ciphertext,
                );
                anyhow::ensure!(
                    memo_records(&mint.plan, &execution.after.state, &recipient)
                        == (
                            1,
                            vec![vec![
                                memo.ephemeral.x().unwrap(),
                                memo.ephemeral.y().unwrap(),
                                memo.amount,
                            ]],
                        ),
                    "mint did not store the expected memo"
                );
                let call = CheckedNativeCall {
                    execution: &execution,
                    circuit: &mint.circuit,
                    initial_context: QueryContext::new(initial.data.clone(), address),
                    entry_point: EntryPointBuf(b"mint".to_vec()),
                    communication_commitment_rand: opening,
                };
                let offer = call.composition_offer(&snapshot.state.parameters)?;
                let expected_state = expected_contract_state(&initial, &execution.after.state)?;
                send_owner_message(
                    &mut output,
                    &json!({
                        "kind":"offer",
                        "offer":hex::encode(offer.public_bytes()?),
                        "expectedState":hex::encode(expected_state),
                    }),
                )?;
                let request = receive_owner_message(&mut input)?;
                anyhow::ensure!(
                    request["kind"] == "draft",
                    "callee expected composition draft"
                );
                let draft = CompositionDraft::from_public_bytes(
                    &owner_payload(&request, "draft")?,
                    &snapshot.state,
                )?;
                anyhow::ensure!(draft.ttl() == mint_ttl, "mint draft TTL changed");
                let proof = draft
                    .prove_call(
                        1,
                        &call,
                        &snapshot.state,
                        &CompositionMaterial {
                            bundle: &mint.bundle,
                            parameters: &mint.parameters,
                        },
                        rand::rngs::OsRng,
                    )
                    .await?;
                send_owner_message(
                    &mut output,
                    &json!({"kind":"proof", "proof":hex::encode(proof)}),
                )?;
            }
            other => anyhow::bail!("unknown confidential-mint owner role {other}"),
        }
        Ok(())
    }

    block_on(async {
        if env::var_os(OWNER_ROLE).is_some() {
            return owner_worker().await;
        }
        let setting = |name: &str| env::var(name).map_err(anyhow::Error::from);
        let endpoint = setting("NOCTIUM_CONFIDENTIAL_MINT_NODE")?;
        anyhow::ensure!(
            endpoint == "http://127.0.0.1:19944",
            "funded confidential-mint test only permits http://127.0.0.1:19944"
        );
        let bundles_root = Path::new(&setting("NOCTIUM_CONFIDENTIAL_MINT_BUNDLES")?).to_path_buf();
        let srs_dir = Path::new(&setting("NOCTIUM_CONFIDENTIAL_MINT_SRS")?).to_path_buf();
        let policy = NetworkPolicy {
            network_id: "undeployed".into(),
            genesis: "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d".into(),
            spec_version: 2_001_100,
            transaction_version: 4,
            profile: noctium_runtime::profile::NAME.into(),
            max_dust: 10u128.pow(22),
        };
        let node = Node::connect(
            &endpoint,
            policy.clone(),
            Duration::from_secs(30),
            64 * 1024 * 1024,
            100_000,
        )?;
        let mut development_seed = [0; 32];
        development_seed[31] = 1;
        node.attach_dust_seed(&development_seed)?;
        let cache = ProofCache::new(srs_dir.clone(), "https://srs.midnight.network/".parse()?)?;
        let dust = cache.dust().await?;
        let dust_parameters = cache.parameters(dust.k()).await?;

        let caller = load_material(&bundles_root, &srs_dir, "caller")?;
        let register = load_material(&bundles_root, &srs_dir, "register")?;
        let mint = load_material(&bundles_root, &srs_dir, "mint")?;
        anyhow::ensure!(
            caller.control.is_none(),
            "caller bundle should be an ordinary circuit"
        );
        anyhow::ensure!(
            caller.plan.entrypoint == "claimMint"
                && register.plan.entrypoint == "registerWithKey"
                && mint.plan.entrypoint == "mint",
            "pinned confidential-mint bundles have unexpected entrypoints"
        );

        let ttl = node.sync()?.block.tblock.to_secs() + 1800;
        let callee_deploy = deployment(
            initial_state(&register.plan),
            &[
                ("registerWithKey", &register.bundle),
                ("mint", &mint.bundle),
            ],
        )?;
        let callee = callee_deploy.address();
        let caller_initial_data = create_state(
            &caller.plan,
            &BTreeMap::from([
                ("route".into(), bytes(&callee.0.0)),
                ("issuanceCount".into(), json!("0")),
            ]),
        )?;
        let caller_deploy = deployment(caller_initial_data, &[("claimMint", &caller.bundle)])?;
        let caller_address = caller_deploy.address();

        let callee_deploy =
            prove_deployment(&callee_deploy, ttl, &node, &dust, &dust_parameters).await?;
        let callee_deploy_receipt =
            finalize(&node, &policy, &dust, &dust_parameters, &callee_deploy).await?;
        anyhow::ensure!(
            callee_deploy_receipt.contract_address == hex::encode(callee.0.0),
            "callee deployment finalized at another address"
        );
        let caller_deploy =
            prove_deployment(&caller_deploy, ttl, &node, &dust, &dust_parameters).await?;
        let caller_deploy_receipt =
            finalize(&node, &policy, &dust, &dust_parameters, &caller_deploy).await?;
        anyhow::ensure!(
            caller_deploy_receipt.contract_address == hex::encode(caller_address.0.0),
            "caller deployment finalized at another address"
        );
        let token_initial = contract_state(&callee_deploy_receipt.contract_state)?;
        anyhow::ensure!(
            token_initial.data == initial_state(&register.plan),
            "token deployment finalized with an unexpected initial state"
        );
        let caller_initial = contract_state(&caller_deploy_receipt.contract_state)?;
        let expected_caller_initial = create_state(
            &caller.plan,
            &BTreeMap::from([
                ("route".into(), bytes(&callee.0.0)),
                ("issuanceCount".into(), json!("0")),
            ]),
        )?;
        anyhow::ensure!(
            caller_initial.data == expected_caller_initial,
            "minter deployment finalized with an unexpected initial state"
        );

        let mut callee_owner = OwnerProcess::spawn("callee")?;
        let registration_snapshot = node.sync()?;
        let registration_ttl = registration_snapshot.block.tblock.to_secs() + 1800;
        callee_owner.send(&json!({
            "kind":"register",
            "address":hex::encode(callee.0.0),
            "ttl":registration_ttl,
        }))?;
        let registration_message = callee_owner.receive()?;
        anyhow::ensure!(
            registration_message["kind"] == "registration-offer",
            "callee owner returned no registration offer"
        );
        let recipient: [u8; 32] = hex::decode(
            registration_message["recipient"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("registration offer omitted recipient"))?,
        )?
        .try_into()
        .map_err(|_| anyhow::anyhow!("registration recipient has the wrong length"))?;
        let registration_expected_state = owner_payload(&registration_message, "expectedState")?;
        let registration_offer =
            CompositionOffer::from_public_bytes(&owner_payload(&registration_message, "offer")?)?;
        let registration_material = [CompositionMaterial {
            bundle: &register.bundle,
            parameters: &register.parameters,
        }];
        let registration_coordinator = IndependentComposition::freeze(
            &[registration_offer],
            &registration_snapshot.state,
            registration_ttl,
            &mut StdRng::from_entropy(),
        )?;
        let registration_draft = registration_coordinator.draft().public_bytes()?;
        callee_owner.send(&json!({
            "kind":"draft",
            "draft":hex::encode(registration_draft),
        }))?;
        let registration_proof_message = callee_owner.receive()?;
        anyhow::ensure!(
            registration_proof_message["kind"] == "registration-proof",
            "callee owner returned no registration proof"
        );
        let registration_proof = owner_payload(&registration_proof_message, "proof")?;
        let registration_proved = registration_coordinator.attach(
            &[registration_proof],
            &registration_snapshot.state,
            &registration_material,
        )?;
        let registration_receipt = finalize(
            &node,
            &policy,
            &dust,
            &dust_parameters,
            registration_proved.native(),
        )
        .await?;
        anyhow::ensure!(
            registration_receipt.contract_address == hex::encode(callee.0.0),
            "registration finalized at another contract address"
        );
        let registration_final = contract_state(&registration_receipt.contract_state)?;
        anyhow::ensure!(
            registration_expected_state == registration_receipt.contract_state,
            "registered key state differs from the callee owner's checked transition"
        );
        let actual_key = map_record(
            &register.plan,
            &registration_final.data,
            "encryptionKeys",
            &recipient,
        );
        anyhow::ensure!(
            actual_key.len() == 2,
            "registered encryption key has the wrong shape"
        );
        anyhow::ensure!(
            point_json_from_coordinates([actual_key[0], actual_key[1]])
                == registration_message["recipientKey"],
            "registered key differs from the callee owner's public key"
        );

        let amount = 12u64;
        let mut caller_owner = OwnerProcess::spawn("caller")?;
        anyhow::ensure!(
            caller_owner.child.id() != callee_owner.child.id(),
            "caller and callee proofs must come from distinct processes"
        );
        let snapshot = node.sync()?;
        let mint_ttl = snapshot.block.tblock.to_secs() + 1800;
        caller_owner.send(&json!({
            "kind":"mint",
            "address":hex::encode(caller_address.0.0),
            "recipient":hex::encode(recipient),
            "ttl":mint_ttl,
        }))?;
        callee_owner.send(&json!({
            "kind":"mint",
            "recipient":hex::encode(recipient),
            "ttl":mint_ttl,
        }))?;
        let caller_message = caller_owner.receive()?;
        let mint_message = callee_owner.receive()?;
        anyhow::ensure!(
            caller_message["kind"] == "offer",
            "caller owner returned no offer"
        );
        anyhow::ensure!(
            mint_message["kind"] == "offer",
            "callee owner returned no offer"
        );
        let caller_expected_state = owner_payload(&caller_message, "expectedState")?;
        let mint_expected_state = owner_payload(&mint_message, "expectedState")?;
        let caller_offer =
            CompositionOffer::from_public_bytes(&owner_payload(&caller_message, "offer")?)?;
        let mint_offer =
            CompositionOffer::from_public_bytes(&owner_payload(&mint_message, "offer")?)?;
        let offers = [caller_offer, mint_offer];
        let coordinator = IndependentComposition::freeze(
            &offers,
            &snapshot.state,
            mint_ttl,
            &mut StdRng::from_entropy(),
        )?;
        let draft = coordinator.draft().public_bytes()?;
        let draft_request = json!({"kind":"draft", "draft":hex::encode(draft)});
        caller_owner.send(&draft_request)?;
        callee_owner.send(&draft_request)?;
        let caller_proof_message = caller_owner.receive()?;
        let mint_proof_message = callee_owner.receive()?;
        anyhow::ensure!(
            caller_proof_message["kind"] == "proof",
            "caller owner returned no proof"
        );
        anyhow::ensure!(
            mint_proof_message["kind"] == "proof",
            "callee owner returned no proof"
        );
        let caller_proof = owner_payload(&caller_proof_message, "proof")?;
        let mint_proof = owner_payload(&mint_proof_message, "proof")?;
        let materials = [
            CompositionMaterial {
                bundle: &caller.bundle,
                parameters: &caller.parameters,
            },
            CompositionMaterial {
                bundle: &mint.bundle,
                parameters: &mint.parameters,
            },
        ];
        anyhow::ensure!(
            matches!(
                coordinator.attach(
                    &[mint_proof.clone(), caller_proof.clone()],
                    &snapshot.state,
                    &materials,
                ),
                Err(CompositionError::InvalidProof)
            ),
            "crossed caller and mint proof slots were accepted"
        );
        let proved =
            coordinator.attach(&[caller_proof, mint_proof], &snapshot.state, &materials)?;
        caller_owner.finish()?;
        callee_owner.finish()?;
        let receipt = finalize(&node, &policy, &dust, &dust_parameters, proved.native()).await?;
        anyhow::ensure!(
            receipt.contract_address == hex::encode(caller_address.0.0),
            "checked pair finalized at another contract address"
        );
        anyhow::ensure!(
            receipt.chain.genesis == policy.genesis,
            "checked pair finalized on another genesis"
        );
        anyhow::ensure!(
            receipt.secondary_states.len() == 1,
            "checked pair receipt has unexpected secondary states"
        );
        let finalized_caller = contract_state(&receipt.contract_state)?;
        anyhow::ensure!(
            caller_expected_state == receipt.contract_state,
            "finalized caller state differs from its owner's checked transition"
        );
        anyhow::ensure!(
            state_cell(&caller.plan, &finalized_caller.data, "issuanceCount")
                == &AlignedValue::from(1u64),
            "finalized caller state has the wrong issuanceCount"
        );
        let callee_key = hex::encode(callee.0.0);
        let callee_bytes = receipt
            .secondary_states
            .get(&callee_key)
            .ok_or_else(|| anyhow::anyhow!("checked pair receipt omitted the token post-state"))?;
        let finalized_callee = contract_state(callee_bytes)?;
        anyhow::ensure!(
            mint_expected_state == *callee_bytes,
            "finalized token state differs from its owner's checked transition"
        );
        anyhow::ensure!(
            state_cell(&mint.plan, &finalized_callee.data, "totalSupply")
                == &field_value(Fr::from(amount)),
            "finalized token state has the wrong totalSupply"
        );
        assert_eq!(
            map_record(
                &mint.plan,
                &finalized_callee.data,
                "creditEpochs",
                &recipient
            ),
            vec![Fr::from(1u64)]
        );
        anyhow::ensure!(
            memo_records(&mint.plan, &finalized_callee.data, &recipient).0 == 1,
            "finalized token state has the wrong memo count"
        );

        eprintln!(
            "funded confidential mint finalized at {} with caller {} and token {}",
            receipt.finalized_hash, receipt.contract_address, callee_key
        );
        Ok(())
    })
}

fn approve_inputs(
    plan: &Plan,
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
    spender_key: EmbeddedGroupAffine,
    amount: u64,
    previous_present: bool,
) -> BTreeMap<String, Json> {
    let mut inputs = BTreeMap::from([
        ("accountId".into(), bytes(owner)),
        ("spender".into(), bytes(spender)),
        ("value".into(), json!(amount.to_string())),
        ("spenderPk".into(), point_json(spender_key)),
    ]);
    let balance = map_record(plan, state, "balances", owner);
    inputs.insert(
        "balanceC1".into(),
        point_json_from_coordinates([balance[0], balance[1]]),
    );
    inputs.insert(
        "balanceC2".into(),
        point_json_from_coordinates([balance[2], balance[3]]),
    );
    let previous_owner = if previous_present {
        let previous = escrow_record(plan, state, owner, spender);
        [[previous[4], previous[5]], [previous[6], previous[7]]]
    } else {
        let identity = EmbeddedGroupAffine::generator() * EmbeddedFr::from(0u64);
        let point = coordinates(identity);
        [point, point]
    };
    inputs.insert(
        "previousOwnerC1".into(),
        point_json_from_coordinates(previous_owner[0]),
    );
    inputs.insert(
        "previousOwnerC2".into(),
        point_json_from_coordinates(previous_owner[1]),
    );
    inputs
}

fn escrow_spend_inputs(
    plan: &Plan,
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
    owner_key: EmbeddedGroupAffine,
    amount: u64,
    spend_epoch: u64,
) -> BTreeMap<String, Json> {
    let escrow = escrow_record(plan, state, owner, spender);
    BTreeMap::from([
        ("fromAddress".into(), bytes(owner)),
        ("spenderId".into(), bytes(spender)),
        ("value".into(), json!(amount.to_string())),
        ("ownerPk".into(), point_json(owner_key)),
        (
            "spenderC1".into(),
            point_json_from_coordinates([escrow[0], escrow[1]]),
        ),
        (
            "spenderC2".into(),
            point_json_from_coordinates([escrow[2], escrow[3]]),
        ),
        (
            "ownerC1".into(),
            point_json_from_coordinates([escrow[4], escrow[5]]),
        ),
        (
            "ownerC2".into(),
            point_json_from_coordinates([escrow[6], escrow[7]]),
        ),
        ("spendEpoch".into(), json!(spend_epoch.to_string())),
    ])
}

fn transfer_from_inputs(
    plan: &Plan,
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
    recipient: &[u8; 32],
    owner_key: EmbeddedGroupAffine,
    recipient_key: EmbeddedGroupAffine,
    amount: u64,
    spend_epoch: u64,
    credit_epoch: u64,
) -> BTreeMap<String, Json> {
    let pending = map_record(plan, state, "pending", recipient);
    let mut inputs =
        escrow_spend_inputs(plan, state, owner, spender, owner_key, amount, spend_epoch);
    inputs.insert("to".into(), bytes(recipient));
    inputs.insert("recipientPk".into(), point_json(recipient_key));
    inputs.insert(
        "pendingC1".into(),
        point_json_from_coordinates([pending[0], pending[1]]),
    );
    inputs.insert(
        "pendingC2".into(),
        point_json_from_coordinates([pending[2], pending[3]]),
    );
    inputs.insert("creditEpoch".into(), json!(credit_epoch.to_string()));
    inputs
}

fn view(
    entry: &str,
    account: Option<&[u8; 32]>,
    state: &ChargedState<Db>,
) -> BTreeMap<String, Json> {
    let (plan_text, circuit_bytes) = view_artifacts(entry);
    let plan: Plan = serde_json::from_str(plan_text).unwrap();
    let circuit = IrSource::load(circuit_bytes).unwrap();
    let inputs = match entry {
        "totalSupply" => BTreeMap::new(),
        "computeAccountId" => BTreeMap::from([(
            "secret".into(),
            bytes(account.expect("computeAccountId needs a secret")),
        )]),
        _ => BTreeMap::from([(
            "account".into(),
            bytes(account.expect("account view needs an account")),
        )]),
    };
    let execution = prepare(
        &plan,
        &inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();
    execution.returns_json()
}

fn allowance_view(
    owner: &[u8; 32],
    spender: &[u8; 32],
    state: &ChargedState<Db>,
) -> BTreeMap<String, Json> {
    let (plan_text, circuit_bytes) = view_artifacts("allowance");
    let plan: Plan = serde_json::from_str(plan_text).unwrap();
    let circuit = IrSource::load(circuit_bytes).unwrap();
    let inputs = BTreeMap::from([
        ("owner".into(), bytes(owner)),
        ("spender".into(), bytes(spender)),
    ]);
    let execution = prepare(
        &plan,
        &inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();
    execution.returns_json()
}

fn assert_empty_allowance(allowance: &BTreeMap<String, Json>, identity: EmbeddedGroupAffine) {
    for name in [
        "spenderC1",
        "spenderC2",
        "ownerC1",
        "ownerC2",
        "ownerMemoEphemeral",
    ] {
        assert_eq!(allowance[name], point_json(identity), "{name} default");
    }
    assert_eq!(allowance["ownerMemoAmount"], "0");
}

fn assert_rejects_candidate_mismatch(
    plan: &Plan,
    circuit: &IrSource,
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
    actual: Ciphertext,
    owner_key: EmbeddedGroupAffine,
) {
    let mut changed = inputs.clone();
    // Rerandomize to valid subgroup points with the same plaintext, but a different ledger record.
    let alternate = Ciphertext {
        c1: actual.c1 + EmbeddedGroupAffine::generator(),
        c2: actual.c2 + owner_key,
    };
    for (name, value) in ["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"]
        .into_iter()
        .zip([
            alternate.c1.x().unwrap(),
            alternate.c1.y().unwrap(),
            alternate.c2.x().unwrap(),
            alternate.c2.y().unwrap(),
        ])
    {
        changed.insert(name.into(), json!(field_decimal(value)));
    }
    let execution = prepare(
        plan,
        &changed,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .expect("valid alternate ciphertext should prepare before ledger binding is checked");
    assert!(
        check(&execution, circuit).is_err(),
        "candidate ciphertext mismatch passed native relation"
    );
}

fn assert_rejects_previous_owner_mismatch(
    plan: &Plan,
    circuit: &IrSource,
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
    actual: Ciphertext,
    owner_key: EmbeddedGroupAffine,
) {
    let mut changed = inputs.clone();
    let alternate = Ciphertext {
        c1: actual.c1 + EmbeddedGroupAffine::generator(),
        c2: actual.c2 + owner_key,
    };
    changed.insert("previousOwnerC1".into(), point_json(alternate.c1));
    changed.insert("previousOwnerC2".into(), point_json(alternate.c2));
    let execution = prepare(
        plan,
        &changed,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .expect("valid alternate owner ciphertext should prepare before ledger binding is checked");
    assert!(
        check(&execution, circuit).is_err(),
        "forged previous owner ciphertext passed native relation"
    );
}

fn assert_rejects_spend_overspend(
    plan: &Plan,
    circuit: &IrSource,
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
    amount: u64,
) {
    let mut changed = inputs.clone();
    changed.insert("value".into(), json!(amount.to_string()));
    match prepare(
        plan,
        &changed,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    ) {
        Err(error) => assert!(
            error.to_string().contains("unsigned subtraction underflow"),
            "overspend failed for an unrelated reason: {error}"
        ),
        Ok(execution) => assert!(
            check(&execution, circuit).is_err(),
            "overspending the escrow passed the native relation"
        ),
    }
}

#[test]
fn confidential_token_registration_pending_sweep_and_transfer_use_native_relations() {
    // These deterministic seeds and keys exercise test plumbing only. They do not establish
    // production seed freshness or production confidentiality.
    let alice_account_secret = [17u8; 32];
    let alice_encryption_secret = [7u8; 32];
    let bob_account_secret = [18u8; 32];
    let bob_encryption_secret = [8u8; 32];
    let alice = account_id(&alice_account_secret);
    let bob = account_id(&bob_account_secret);
    let missing_account_secret = [19u8; 32];
    let missing = account_id(&missing_account_secret);
    let alice_key_scalar = encryption_scalar(&alice_encryption_secret);
    let bob_key_scalar = encryption_scalar(&bob_encryption_secret);
    let generator = EmbeddedGroupAffine::generator();
    let alice_key = generator * alice_key_scalar;
    let bob_key = generator * bob_key_scalar;
    let identity = generator * EmbeddedFr::from(0u64);

    let (_, register_text, _) = artifacts("registerWithKey");
    let register_plan: Plan = serde_json::from_str(register_text).unwrap();
    let mut state = initial_state(&register_plan);
    assert_token_metadata(&register_plan, &state);
    assert_eq!(
        state_slot(&register_plan, &state, "initialized"),
        &StateValue::Cell(storage::arena::Sp::new(field_value(Fr::from(1u64))))
    );
    assert_eq!(view("totalSupply", None, &state)["supply"], "0");

    for (sequence, account, account_secret, encryption_secret, public_key) in [
        (
            1,
            alice,
            &alice_account_secret,
            &alice_encryption_secret,
            alice_key,
        ),
        (2, bob, &bob_account_secret, &bob_encryption_secret, bob_key),
    ] {
        let values = BTreeMap::from([
            ("accountId".into(), bytes(&account)),
            ("pk".into(), point_json(public_key)),
        ]);
        state = run_entry(
            "registerWithKey",
            values,
            account_secret,
            encryption_secret,
            &[],
            None,
            sequence,
            &state,
        )
        .unwrap()
        .0;
        assert_record(
            &register_plan,
            &state,
            "encryptionKeys",
            &account,
            &coordinates(public_key),
        );
        assert_ciphertext(
            &register_plan,
            &state,
            "balances",
            &account,
            Ciphertext {
                c1: identity,
                c2: identity,
            },
        );
        assert_ciphertext(
            &register_plan,
            &state,
            "pending",
            &account,
            Ciphertext {
                c1: identity,
                c2: identity,
            },
        );
    }

    let (_, mint_text, _) = artifacts("mint");
    let mint_plan: Plan = serde_json::from_str(mint_text).unwrap();
    let pending_before = map_record(&mint_plan, &state, "pending", &alice);
    assert_eq!(pending_before.len(), 4);
    let mint_seed = [0x31u8; 32];
    let (pending_after_mint, mint_memo) = expected_credit(&mint_seed, &alice, alice_key, 1, 12);
    let mut mint_values = BTreeMap::from([
        ("recipient".into(), bytes(&alice)),
        ("value".into(), json!("12")),
        ("recipientPk".into(), point_json(alice_key)),
        ("epoch".into(), json!("1")),
    ]);
    for (name, value) in ["previousC1X", "previousC1Y", "previousC2X", "previousC2Y"]
        .into_iter()
        .zip(pending_before)
    {
        mint_values.insert(name.into(), json!(field_decimal(value)));
    }
    let mut stale_epoch_values = mint_values.clone();
    stale_epoch_values.insert("epoch".into(), json!("0"));
    let stale_epoch_error = match run_entry(
        "mint",
        stale_epoch_values,
        &alice_account_secret,
        &alice_encryption_secret,
        &[mint_seed],
        None,
        4,
        &state,
    ) {
        Err(error) => error,
        Ok(_) => panic!("stale expected epoch passed native mint relation"),
    };
    assert_eq!(
        stale_epoch_error, "native circuit assertion or preimage check failed",
        "stale epoch rejected for an unrelated reason"
    );
    state = run_entry(
        "mint",
        mint_values,
        &alice_account_secret,
        &alice_encryption_secret,
        &[mint_seed],
        None,
        3,
        &state,
    )
    .unwrap()
    .0;
    assert_ciphertext(
        &mint_plan,
        &state,
        "balances",
        &alice,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_ciphertext(&mint_plan, &state, "pending", &alice, pending_after_mint);
    assert_eq!(memo_records(&mint_plan, &state, &alice).0, 1);
    assert_eq!(
        memo_records(&mint_plan, &state, &alice).1[0],
        [
            mint_memo.ephemeral.x().unwrap(),
            mint_memo.ephemeral.y().unwrap(),
            mint_memo.amount,
        ]
    );
    assert_eq!(
        map_record(&mint_plan, &state, "creditEpochs", &alice),
        vec![Fr::from(1u64)]
    );
    assert_eq!(
        field_decimal({
            let StateValue::Cell(cell) = state_slot(&mint_plan, &state, "totalSupply") else {
                panic!("expected totalSupply cell")
            };
            let mut fields = Vec::new();
            cell.value_only_field_repr(&mut fields);
            fields[0]
        }),
        "12"
    );

    let (_, sweep_text, _) = artifacts("sweep");
    let sweep_plan: Plan = serde_json::from_str(sweep_text).unwrap();
    let balance_before = map_record(&sweep_plan, &state, "balances", &alice);
    let pending_before_sweep = map_record(&sweep_plan, &state, "pending", &alice);
    let mut sweep_values = BTreeMap::from([("accountId".into(), bytes(&alice))]);
    for (name, value) in ["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"]
        .into_iter()
        .zip(balance_before)
        .chain(
            ["pendingC1X", "pendingC1Y", "pendingC2X", "pendingC2Y"]
                .into_iter()
                .zip(pending_before_sweep),
        )
    {
        sweep_values.insert(name.into(), json!(field_decimal(value)));
    }
    state = run_entry(
        "sweep",
        sweep_values,
        &alice_account_secret,
        &alice_encryption_secret,
        &[],
        None,
        4,
        &state,
    )
    .unwrap()
    .0;
    let spendable = pending_after_mint;
    assert_ciphertext(&sweep_plan, &state, "balances", &alice, spendable);
    assert_ciphertext(
        &sweep_plan,
        &state,
        "pending",
        &alice,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_eq!(memo_records(&sweep_plan, &state, &alice).0, 1);

    let (_, transfer_text, transfer_bytes) = artifacts("transfer");
    let transfer_plan: Plan = serde_json::from_str(transfer_text).unwrap();
    let transfer_circuit = IrSource::load(transfer_bytes).unwrap();
    let state_before_transfer = state.clone();
    let balance_before_transfer = map_record(&transfer_plan, &state, "balances", &alice);
    let recipient_pending_before = map_record(&transfer_plan, &state, "pending", &bob);
    let transfer_seed = [0x32u8; 32];
    let owner_after = expected_debit(&transfer_seed, spendable, alice_key, 5);
    let (recipient_after, transfer_memo) = expected_credit(&transfer_seed, &bob, bob_key, 1, 5);
    let mut transfer_values = BTreeMap::from([
        ("accountId".into(), bytes(&alice)),
        ("recipient".into(), bytes(&bob)),
        ("value".into(), json!("5")),
        ("recipientPk".into(), point_json(bob_key)),
        ("epoch".into(), json!("1")),
    ]);
    for (name, value) in ["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"]
        .into_iter()
        .zip(balance_before_transfer)
        .chain(
            ["pendingC1X", "pendingC1Y", "pendingC2X", "pendingC2Y"]
                .into_iter()
                .zip(recipient_pending_before),
        )
    {
        transfer_values.insert(name.into(), json!(field_decimal(value)));
    }
    let (after_transfer, transfer_inputs) = run_entry(
        "transfer",
        transfer_values,
        &alice_account_secret,
        &alice_encryption_secret,
        &[transfer_seed],
        Some(spendable),
        5,
        &state,
    )
    .unwrap();
    assert_ciphertext(
        &transfer_plan,
        &after_transfer,
        "balances",
        &alice,
        owner_after,
    );
    assert_ciphertext(
        &transfer_plan,
        &after_transfer,
        "pending",
        &bob,
        recipient_after,
    );
    assert_ciphertext(
        &transfer_plan,
        &after_transfer,
        "balances",
        &bob,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_eq!(decrypt_small(owner_after, alice_key_scalar, 64), 7);
    assert_eq!(decrypt_small(recipient_after, bob_key_scalar, 64), 5);
    assert_eq!(
        decrypt_small(
            Ciphertext {
                c1: identity,
                c2: identity
            },
            bob_key_scalar,
            64
        ),
        0
    );
    assert_eq!(memo_records(&transfer_plan, &after_transfer, &alice).0, 1);
    assert_eq!(memo_records(&transfer_plan, &after_transfer, &bob).0, 1);
    assert_eq!(
        memo_records(&transfer_plan, &after_transfer, &bob).1[0],
        [
            transfer_memo.ephemeral.x().unwrap(),
            transfer_memo.ephemeral.y().unwrap(),
            transfer_memo.amount,
        ]
    );
    assert_eq!(
        map_record(&transfer_plan, &after_transfer, "creditEpochs", &bob),
        vec![Fr::from(1u64)]
    );
    assert_rejects_candidate_mismatch(
        &transfer_plan,
        &transfer_circuit,
        &transfer_inputs,
        &state_before_transfer,
        spendable,
        alice_key,
    );

    state = after_transfer.clone();
    let (_, burn_text, _) = artifacts("burn");
    let burn_plan: Plan = serde_json::from_str(burn_text).unwrap();
    let burn_seed = [0x33u8; 32];
    let balance_before_burn = map_record(&burn_plan, &state, "balances", &alice);
    let balance_after_burn = expected_debit(&burn_seed, owner_after, alice_key, 2);
    let mut burn_values = BTreeMap::from([
        ("accountId".into(), bytes(&alice)),
        ("value".into(), json!("2")),
    ]);
    for (name, value) in ["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"]
        .into_iter()
        .zip(balance_before_burn)
    {
        burn_values.insert(name.into(), json!(field_decimal(value)));
    }
    state = run_entry(
        "burn",
        burn_values,
        &alice_account_secret,
        &alice_encryption_secret,
        &[burn_seed],
        Some(owner_after),
        6,
        &state,
    )
    .unwrap()
    .0;
    assert_ciphertext(&burn_plan, &state, "balances", &alice, balance_after_burn);
    assert_eq!(decrypt_small(balance_after_burn, alice_key_scalar, 64), 5);
    assert_ciphertext(
        &burn_plan,
        &state,
        "pending",
        &alice,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_ciphertext(&burn_plan, &state, "pending", &bob, recipient_after);
    assert_ciphertext(
        &burn_plan,
        &state,
        "balances",
        &bob,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_eq!(
        memo_records(&burn_plan, &state, &alice),
        memo_records(&burn_plan, &after_transfer, &alice)
    );
    assert_eq!(
        memo_records(&burn_plan, &state, &bob),
        memo_records(&burn_plan, &after_transfer, &bob)
    );
    assert_eq!(
        map_record(&burn_plan, &state, "creditEpochs", &alice),
        vec![Fr::from(1u64)]
    );
    assert_eq!(
        map_record(&burn_plan, &state, "creditEpochs", &bob),
        vec![Fr::from(1u64)]
    );

    assert_eq!(view("totalSupply", None, &state)["supply"], "10");
    assert_eq!(view("isRegistered", Some(&alice), &state)["value"], true);
    assert_eq!(view("isRegistered", Some(&missing), &state)["value"], false);
    let alice_balance = view("balanceOf", Some(&alice), &state);
    assert_eq!(alice_balance["c1"], point_json(balance_after_burn.c1));
    assert_eq!(alice_balance["c2"], point_json(balance_after_burn.c2));
    assert_eq!(decrypt_small(balance_after_burn, alice_key_scalar, 64), 5);
    let bob_pending = view("pendingOf", Some(&bob), &state);
    assert_eq!(bob_pending["c1"], point_json(recipient_after.c1));
    assert_eq!(bob_pending["c2"], point_json(recipient_after.c2));
    assert_eq!(decrypt_small(recipient_after, bob_key_scalar, 64), 5);
    assert_eq!(
        view("balanceOf", Some(&missing), &state),
        BTreeMap::from([
            ("c1".into(), point_json(identity)),
            ("c2".into(), point_json(identity)),
        ])
    );
    assert_eq!(
        view("pendingOf", Some(&missing), &state),
        BTreeMap::from([
            ("c1".into(), point_json(identity)),
            ("c2".into(), point_json(identity)),
        ])
    );
    assert_eq!(
        view("computeAccountId", Some(&alice_account_secret), &state)["accountId"],
        bytes(&alice)
    );

    let (_, move_text, _) = artifacts("_move");
    let move_plan: Plan = serde_json::from_str(move_text).unwrap();
    let move_seed = [0x34u8; 32];
    let alice_balance_before_move = map_record(&move_plan, &state, "balances", &alice);
    let alice_pending_before_move = map_record(&move_plan, &state, "pending", &alice);
    let alice_memos_before_move = memo_records(&move_plan, &state, &alice).1;
    let alice_after_move = expected_debit(&move_seed, balance_after_burn, alice_key, 1);
    let (alice_pending_after_move, move_memo) =
        expected_credit(&move_seed, &alice, alice_key, 2, 1);
    let mut move_values = BTreeMap::from([
        ("accountId".into(), bytes(&alice)),
        ("recipient".into(), bytes(&alice)),
        ("value".into(), json!("1")),
        ("recipientPk".into(), point_json(alice_key)),
        ("epoch".into(), json!("2")),
    ]);
    for (name, value) in ["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"]
        .into_iter()
        .zip(alice_balance_before_move)
        .chain(
            ["pendingC1X", "pendingC1Y", "pendingC2X", "pendingC2Y"]
                .into_iter()
                .zip(alice_pending_before_move),
        )
    {
        move_values.insert(name.into(), json!(field_decimal(value)));
    }
    let (after_move, move_inputs) = run_entry(
        "_move",
        move_values,
        &alice_account_secret,
        &alice_encryption_secret,
        &[move_seed],
        Some(balance_after_burn),
        7,
        &state,
    )
    .unwrap();
    let self_transfer = prepare(
        &transfer_plan,
        &move_inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    assert!(
        check(&self_transfer, &transfer_circuit).is_err(),
        "transfer entry accepted a self-recipient"
    );
    state = after_move;
    assert_ciphertext(&move_plan, &state, "balances", &alice, alice_after_move);
    assert_ciphertext(
        &move_plan,
        &state,
        "pending",
        &alice,
        alice_pending_after_move,
    );
    assert_ciphertext(&move_plan, &state, "pending", &bob, recipient_after);
    assert_eq!(decrypt_small(alice_after_move, alice_key_scalar, 64), 4);
    assert_eq!(
        decrypt_small(alice_pending_after_move, alice_key_scalar, 64),
        1
    );
    assert_eq!(decrypt_small(recipient_after, bob_key_scalar, 64), 5);
    let (alice_memo_count, alice_memos) = memo_records(&move_plan, &state, &alice);
    assert_eq!(alice_memo_count, 2);
    assert_eq!(
        alice_memos[0],
        [
            move_memo.ephemeral.x().unwrap(),
            move_memo.ephemeral.y().unwrap(),
            move_memo.amount,
        ]
    );
    assert_eq!(alice_memos[1], alice_memos_before_move[0]);
    assert_eq!(
        map_record(&move_plan, &state, "creditEpochs", &alice),
        vec![Fr::from(2u64)]
    );
    assert_eq!(
        map_record(&move_plan, &state, "creditEpochs", &bob),
        vec![Fr::from(1u64)]
    );

    let (_, clear_text, _) = artifacts("clearMemos");
    let clear_plan: Plan = serde_json::from_str(clear_text).unwrap();
    let clear_values = |epoch: &str| {
        BTreeMap::from([
            ("accountId".into(), bytes(&alice)),
            ("expectedEpoch".into(), json!(epoch)),
        ])
    };
    let stale_clear = run_entry(
        "clearMemos",
        clear_values("1"),
        &alice_account_secret,
        &alice_encryption_secret,
        &[],
        None,
        8,
        &state,
    );
    assert!(
        stale_clear.is_err(),
        "stale memo epoch passed the native relation"
    );
    let wrong_key_clear = run_entry(
        "clearMemos",
        clear_values("2"),
        &alice_account_secret,
        &bob_encryption_secret,
        &[],
        None,
        9,
        &state,
    );
    assert!(
        wrong_key_clear.is_err(),
        "another account's encryption key cleared Alice's memos"
    );
    let bob_memos_before_clear = memo_records(&clear_plan, &state, &bob);
    state = run_entry(
        "clearMemos",
        clear_values("2"),
        &alice_account_secret,
        &alice_encryption_secret,
        &[],
        None,
        10,
        &state,
    )
    .unwrap()
    .0;
    assert_eq!(memo_records(&clear_plan, &state, &alice), (0, Vec::new()));
    assert_eq!(
        memo_records(&clear_plan, &state, &bob),
        bob_memos_before_clear
    );
    assert_record(
        &clear_plan,
        &state,
        "encryptionKeys",
        &alice,
        &coordinates(alice_key),
    );
    assert_record(
        &clear_plan,
        &state,
        "encryptionKeys",
        &bob,
        &coordinates(bob_key),
    );
    assert_ciphertext(&clear_plan, &state, "balances", &alice, alice_after_move);
    assert_ciphertext(
        &clear_plan,
        &state,
        "balances",
        &bob,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_ciphertext(
        &clear_plan,
        &state,
        "pending",
        &alice,
        alice_pending_after_move,
    );
    assert_ciphertext(&clear_plan, &state, "pending", &bob, recipient_after);
    assert_eq!(
        map_record(&clear_plan, &state, "creditEpochs", &alice),
        vec![Fr::from(2u64)]
    );
    assert_eq!(
        map_record(&clear_plan, &state, "creditEpochs", &bob),
        vec![Fr::from(1u64)]
    );
    assert_eq!(
        state_slot(&clear_plan, &state, "initialized"),
        &StateValue::Cell(storage::arena::Sp::new(field_value(Fr::from(1u64))))
    );
    assert_eq!(view("totalSupply", None, &state)["supply"], "10");

    let (_, approve_text, approve_bytes) = artifacts("approve");
    let approve_plan: Plan = serde_json::from_str(approve_text).unwrap();
    let approve_circuit = IrSource::load(approve_bytes).unwrap();
    let alice_memos_before_approve = memo_records(&approve_plan, &state, &alice);
    let bob_memos_before_approve = memo_records(&approve_plan, &state, &bob);
    assert_empty_allowance(&allowance_view(&missing, &bob, &state), identity);

    let approve_seed = [0x35u8; 32];
    let first_spender_ct = expected_encryption(&approve_seed, "approve_spender_ct", bob_key, 2);
    let first_owner_ct = expected_encryption(&approve_seed, "approve_owner_ct", alice_key, 2);
    let first_owner_memo = expected_owner_memo(&approve_seed, alice_key, 2);
    let first_balance = expected_debit_with_domain(
        &approve_seed,
        alice_after_move,
        alice_key,
        2,
        "approve_debit",
    );
    state = run_entry(
        "approve",
        approve_inputs(&approve_plan, &state, &alice, &bob, bob_key, 2, false),
        &alice_account_secret,
        &alice_encryption_secret,
        &[approve_seed],
        Some(alice_after_move),
        11,
        &state,
    )
    .unwrap()
    .0;
    assert_ciphertext(&approve_plan, &state, "balances", &alice, first_balance);
    assert_escrow(
        &approve_plan,
        &state,
        &alice,
        &bob,
        first_spender_ct,
        first_owner_ct,
        first_owner_memo,
    );
    assert_eq!(decrypt_small(first_balance, alice_key_scalar, 64), 2);
    assert_eq!(decrypt_small(first_spender_ct, bob_key_scalar, 64), 2);
    assert_eq!(decrypt_small(first_owner_ct, alice_key_scalar, 64), 2);
    let first_allowance = allowance_view(&alice, &bob, &state);
    assert_eq!(
        first_allowance["spenderC1"],
        point_json(first_spender_ct.c1)
    );
    assert_eq!(
        first_allowance["spenderC2"],
        point_json(first_spender_ct.c2)
    );
    assert_eq!(first_allowance["ownerC1"], point_json(first_owner_ct.c1));
    assert_eq!(first_allowance["ownerC2"], point_json(first_owner_ct.c2));
    assert_eq!(
        first_allowance["ownerMemoEphemeral"],
        point_json(first_owner_memo.ephemeral)
    );
    assert_eq!(
        first_allowance["ownerMemoAmount"],
        field_decimal(first_owner_memo.amount)
    );
    assert_empty_allowance(&allowance_view(&alice, &missing, &state), identity);

    let refunded_balance = Ciphertext {
        c1: first_balance.c1 + first_owner_ct.c1,
        c2: first_balance.c2 + first_owner_ct.c2,
    };
    assert_eq!(decrypt_small(refunded_balance, alice_key_scalar, 64), 4);
    let reapprove_seed = [0x36u8; 32];
    let second_spender_ct = expected_encryption(&reapprove_seed, "approve_spender_ct", bob_key, 3);
    let second_owner_ct = expected_encryption(&reapprove_seed, "approve_owner_ct", alice_key, 3);
    let second_owner_memo = expected_owner_memo(&reapprove_seed, alice_key, 3);
    let second_balance = expected_debit_with_domain(
        &reapprove_seed,
        refunded_balance,
        alice_key,
        3,
        "approve_debit",
    );
    let state_before_reapprove = state.clone();
    let (after_reapprove, reapprove_inputs) = run_entry(
        "approve",
        approve_inputs(&approve_plan, &state, &alice, &bob, bob_key, 3, true),
        &alice_account_secret,
        &alice_encryption_secret,
        &[reapprove_seed],
        Some(refunded_balance),
        12,
        &state,
    )
    .unwrap();
    assert_rejects_previous_owner_mismatch(
        &approve_plan,
        &approve_circuit,
        &reapprove_inputs,
        &state_before_reapprove,
        first_owner_ct,
        alice_key,
    );
    state = after_reapprove;
    assert_ciphertext(&approve_plan, &state, "balances", &alice, second_balance);
    assert_escrow(
        &approve_plan,
        &state,
        &alice,
        &bob,
        second_spender_ct,
        second_owner_ct,
        second_owner_memo,
    );
    assert_eq!(decrypt_small(second_balance, alice_key_scalar, 64), 1);
    assert_eq!(decrypt_small(second_spender_ct, bob_key_scalar, 64), 3);
    assert_eq!(decrypt_small(second_owner_ct, alice_key_scalar, 64), 3);
    let replacement = allowance_view(&alice, &bob, &state);
    assert_eq!(replacement["spenderC1"], point_json(second_spender_ct.c1));
    assert_eq!(replacement["spenderC2"], point_json(second_spender_ct.c2));
    assert_eq!(replacement["ownerC1"], point_json(second_owner_ct.c1));
    assert_eq!(replacement["ownerC2"], point_json(second_owner_ct.c2));
    assert_eq!(
        replacement["ownerMemoEphemeral"],
        point_json(second_owner_memo.ephemeral)
    );
    assert_eq!(
        replacement["ownerMemoAmount"],
        field_decimal(second_owner_memo.amount)
    );
    assert_eq!(view("totalSupply", None, &state)["supply"], "10");
    assert_ciphertext(
        &approve_plan,
        &state,
        "pending",
        &alice,
        alice_pending_after_move,
    );
    assert_ciphertext(&approve_plan, &state, "pending", &bob, recipient_after);
    assert_eq!(
        memo_records(&approve_plan, &state, &alice),
        alice_memos_before_approve
    );
    assert_eq!(
        memo_records(&approve_plan, &state, &bob),
        bob_memos_before_approve
    );
    assert_eq!(
        map_record(&approve_plan, &state, "creditEpochs", &alice),
        vec![Fr::from(2u64)]
    );
    assert_eq!(
        map_record(&approve_plan, &state, "creditEpochs", &bob),
        vec![Fr::from(1u64)]
    );

    let (_, transfer_from_text, transfer_from_bytes) = artifacts("transferFrom");
    let transfer_from_plan: Plan = serde_json::from_str(transfer_from_text).unwrap();
    let transfer_from_circuit = IrSource::load(transfer_from_bytes).unwrap();
    let state_before_transfer_from = state.clone();
    let (spender_before, owner_before, owner_memo_before) =
        escrow_ciphertexts(&escrow_record(&transfer_from_plan, &state, &alice, &bob));
    assert_eq!(decrypt_small(spender_before, bob_key_scalar, 64), 3);
    assert_eq!(decrypt_small(owner_before, alice_key_scalar, 64), 3);
    assert_eq!(
        decrypt_owner_memo(owner_memo_before, alice_key_scalar, 64),
        3
    );
    let pending_before_transfer_from =
        ciphertext_from_fields(&map_record(&transfer_from_plan, &state, "pending", &bob), 0);
    let bob_memos_before_transfer_from = memo_records(&transfer_from_plan, &state, &bob);
    let transfer_spend_seed = [0x37u8; 32];
    let transfer_credit_seed = [0x38u8; 32];
    let (next_spender, next_owner, next_owner_memo) = expected_escrow_spend(
        &transfer_spend_seed,
        &alice,
        &bob,
        1,
        2,
        1,
        spender_before,
        owner_before,
        bob_key,
        alice_key,
    );
    let (pending_credit, transfer_from_memo) =
        expected_credit(&transfer_credit_seed, &bob, bob_key, 2, 2);
    let next_bob_pending = add_ciphertexts(pending_before_transfer_from, pending_credit);
    let (after_transfer_from, transfer_from_native_inputs) = run_entry(
        "transferFrom",
        transfer_from_inputs(
            &transfer_from_plan,
            &state,
            &alice,
            &bob,
            &bob,
            alice_key,
            bob_key,
            2,
            1,
            2,
        ),
        &bob_account_secret,
        &bob_encryption_secret,
        &[transfer_spend_seed, transfer_credit_seed],
        Some(spender_before),
        13,
        &state,
    )
    .unwrap();
    assert_rejects_spend_overspend(
        &transfer_from_plan,
        &transfer_from_circuit,
        &transfer_from_native_inputs,
        &state_before_transfer_from,
        4,
    );
    state = after_transfer_from;
    assert_escrow(
        &transfer_from_plan,
        &state,
        &alice,
        &bob,
        next_spender,
        next_owner,
        next_owner_memo,
    );
    let (actual_spender, actual_owner, actual_owner_memo) =
        escrow_ciphertexts(&escrow_record(&transfer_from_plan, &state, &alice, &bob));
    assert_eq!(decrypt_small(actual_spender, bob_key_scalar, 64), 1);
    assert_eq!(decrypt_small(actual_owner, alice_key_scalar, 64), 1);
    assert_eq!(
        decrypt_owner_memo(actual_owner_memo, alice_key_scalar, 64),
        1
    );
    assert_eq!(
        escrow_spend_epoch_record(&transfer_from_plan, &state, &alice, &bob),
        vec![Fr::from(1u64)]
    );
    assert_ciphertext(
        &transfer_from_plan,
        &state,
        "balances",
        &alice,
        second_balance,
    );
    assert_ciphertext(
        &transfer_from_plan,
        &state,
        "balances",
        &bob,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_ciphertext(
        &transfer_from_plan,
        &state,
        "pending",
        &alice,
        alice_pending_after_move,
    );
    assert_ciphertext(
        &transfer_from_plan,
        &state,
        "pending",
        &bob,
        next_bob_pending,
    );
    assert_eq!(decrypt_small(next_bob_pending, bob_key_scalar, 64), 7);
    let (bob_memo_count_after_transfer_from, bob_memos_after_transfer_from) =
        memo_records(&transfer_from_plan, &state, &bob);
    assert_eq!(
        bob_memo_count_after_transfer_from,
        bob_memos_before_transfer_from.0 + 1
    );
    assert_eq!(
        bob_memos_after_transfer_from[0],
        [
            transfer_from_memo.ephemeral.x().unwrap(),
            transfer_from_memo.ephemeral.y().unwrap(),
            transfer_from_memo.amount,
        ]
    );
    assert_eq!(
        &bob_memos_after_transfer_from[1..],
        bob_memos_before_transfer_from.1.as_slice()
    );
    assert_eq!(
        map_record(&transfer_from_plan, &state, "creditEpochs", &bob),
        vec![Fr::from(2u64)]
    );
    assert_eq!(view("totalSupply", None, &state)["supply"], "10");

    let (_, burn_from_text, _) = artifacts("burnFrom");
    let burn_from_plan: Plan = serde_json::from_str(burn_from_text).unwrap();
    let (spender_before_burn_from, owner_before_burn_from, _) =
        escrow_ciphertexts(&escrow_record(&burn_from_plan, &state, &alice, &bob));
    let burn_from_seed = [0x39u8; 32];
    let (burned_spender, burned_owner, burned_owner_memo) = expected_escrow_spend(
        &burn_from_seed,
        &alice,
        &bob,
        2,
        1,
        0,
        spender_before_burn_from,
        owner_before_burn_from,
        bob_key,
        alice_key,
    );
    state = run_entry(
        "burnFrom",
        escrow_spend_inputs(&burn_from_plan, &state, &alice, &bob, alice_key, 1, 2),
        &bob_account_secret,
        &bob_encryption_secret,
        &[burn_from_seed],
        Some(spender_before_burn_from),
        14,
        &state,
    )
    .unwrap()
    .0;
    assert_escrow(
        &burn_from_plan,
        &state,
        &alice,
        &bob,
        burned_spender,
        burned_owner,
        burned_owner_memo,
    );
    let (actual_spender_after_burn, actual_owner_after_burn, actual_memo_after_burn) =
        escrow_ciphertexts(&escrow_record(&burn_from_plan, &state, &alice, &bob));
    assert_eq!(
        decrypt_small(actual_spender_after_burn, bob_key_scalar, 64),
        0
    );
    assert_eq!(
        decrypt_small(actual_owner_after_burn, alice_key_scalar, 64),
        0
    );
    assert_eq!(
        decrypt_owner_memo(actual_memo_after_burn, alice_key_scalar, 64),
        0
    );
    assert_eq!(
        escrow_spend_epoch_record(&burn_from_plan, &state, &alice, &bob),
        vec![Fr::from(2u64)]
    );
    assert_ciphertext(&burn_from_plan, &state, "balances", &alice, second_balance);
    assert_ciphertext(
        &burn_from_plan,
        &state,
        "balances",
        &bob,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_ciphertext(
        &burn_from_plan,
        &state,
        "pending",
        &alice,
        alice_pending_after_move,
    );
    assert_ciphertext(&burn_from_plan, &state, "pending", &bob, next_bob_pending);
    assert_eq!(decrypt_small(next_bob_pending, bob_key_scalar, 64), 7);
    assert_eq!(
        memo_records(&burn_from_plan, &state, &bob),
        (
            bob_memo_count_after_transfer_from,
            bob_memos_after_transfer_from
        )
    );
    assert_eq!(
        map_record(&burn_from_plan, &state, "creditEpochs", &alice),
        vec![Fr::from(2u64)]
    );
    assert_eq!(
        map_record(&burn_from_plan, &state, "creditEpochs", &bob),
        vec![Fr::from(2u64)]
    );
    assert_eq!(view("totalSupply", None, &state)["supply"], "9");
    assert_token_metadata(&burn_from_plan, &state);
}
