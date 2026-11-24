#![cfg(feature = "zkir-321")]

use anyhow::{Context, Result};
use base_crypto::{
    fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom},
    hash::HashOutput,
    time::Timestamp,
};
use coin_structure::contract::ContractAddress;
use futures::executor::block_on;
use ledger::{
    semantics::{TransactionContext, TransactionResult},
    structure::{ContractDeploy, LedgerParameters, LedgerState, StandardTransaction, Transaction},
    verify::WellFormedStrictness,
};
use noctium_runtime::{
    Db, Plan,
    artifacts::{self, Role, VerifiedBundle},
    assembly::{CheckedNativeCall, assemble_checked_calls},
    check, create_state, prepare,
    proof::{CompositionMaterial, PreparedComposition, TrustedParameters},
    zkir::IrSource,
};
use onchain_runtime::{
    context::{BlockContext, QueryContext},
    state::{ChargedState, ContractOperation, ContractState, EntryPointBuf, StateValue},
};
use rand::{SeedableRng, rngs::StdRng};
use serde_json::{Value as Json, json};
use serialize::tagged_deserialize;
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use storage::arena::Sp;
use transient_crypto::{curve::Fr, proofs::Zkir};

const PARAMETER_SHA256: &str = "b9009f1098bcefffec3c461ab3a5e3a17f7e5599f0f08c70fcdc55a89227bcbd";

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn aligned_bytes(value: &[u8]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(value)]),
        Alignment::singleton(AlignmentAtom::Bytes {
            length: value.len() as u32,
        }),
    )
    .unwrap()
}

fn aligned_profile(label: &[u8], digest: &[u8]) -> AlignedValue {
    AlignedValue::concat(&[aligned_bytes(label), aligned_bytes(digest)])
}

fn operation(directory: &PathBuf, name: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("NestedRecordKeyByteValues.{name}");
    let plan = serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(fs::read(directory.join(format!("{stem}.zkir")))?.as_slice())?;
    Ok((plan, circuit))
}

fn store_inputs() -> BTreeMap<String, Json> {
    let owner = [1u8; 32];
    let mut id = [3u8; 33];
    id[32] = 4;
    let mut digest = [6u8; 33];
    digest[32] = 4;
    BTreeMap::from([
        ("owner".into(), bytes(&owner)),
        ("tag".into(), bytes(&[7])),
        ("id".into(), bytes(&id)),
        ("label".into(), bytes(&[11])),
        ("digest".into(), bytes(&digest)),
    ])
}

fn lookup_inputs() -> BTreeMap<String, Json> {
    let mut id = [3u8; 33];
    id[32] = 4;
    BTreeMap::from([
        ("owner".into(), bytes(&[1; 32])),
        ("tag".into(), bytes(&[7])),
        ("id".into(), bytes(&id)),
    ])
}

fn changed_profile_state(state: &ChargedState<Db>, malformed_width: bool) -> ChargedState<Db> {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state slots");
    };
    let StateValue::Map(owners) = slots.get(0).expect("profiles root slot") else {
        panic!("expected profiles Map");
    };
    let owner_key = aligned_bytes(&[1; 32]);
    let StateValue::Map(profiles) = &*owners.get(&owner_key).expect("owner bucket") else {
        panic!("expected owner profile Map");
    };
    let mut id = [3u8; 33];
    id[32] = 4;
    let key = AlignedValue::concat(&[aligned_bytes(&[7]), aligned_bytes(&id)]);
    let valid_digest = [9u8; 33];
    let malformed_digest = [6u8; 32];
    let digest = if malformed_width {
        &malformed_digest[..]
    } else {
        &valid_digest[..]
    };
    let profile = StateValue::Cell(Sp::new(aligned_profile(&[12], digest)));
    let changed_profiles = StateValue::Map(profiles.insert(key, profile));
    let changed_owners = StateValue::Map(owners.insert(owner_key, changed_profiles));
    ChargedState::new(StateValue::Array(
        slots
            .insert(0, changed_owners)
            .expect("profiles root slot exists"),
    ))
}

#[test]
#[ignore = "requires a fresh fixed-byte record lookup bundle, strict store artifacts, and trusted K9 parameters"]
fn fixed_byte_record_lookup_proof_is_bound_to_exact_ledger_record() -> Result<()> {
    let bundle_root = PathBuf::from(
        env::var_os("NOCTIUM_FIXED_BYTE_RECORD_LOOKUP_BUNDLE")
            .context("set NOCTIUM_FIXED_BYTE_RECORD_LOOKUP_BUNDLE")?,
    );
    let bundle_digest = env::var("NOCTIUM_FIXED_BYTE_RECORD_LOOKUP_BUNDLE_SHA256")?;
    let store_directory = PathBuf::from(
        env::var_os("NOCTIUM_FIXED_BYTE_RECORD_STORE_DIR")
            .context("set NOCTIUM_FIXED_BYTE_RECORD_STORE_DIR")?,
    );
    let parameters_path = PathBuf::from(
        env::var_os("NOCTIUM_FIXED_BYTE_RECORD_PARAMETERS")
            .context("set NOCTIUM_FIXED_BYTE_RECORD_PARAMETERS")?,
    );
    let bundle: VerifiedBundle = artifacts::verify(&bundle_root, Some(&bundle_digest))?;
    let lookup_plan: Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
    let lookup_circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
    let store = operation(&store_directory, "store")?;
    let verifier: transient_crypto::proofs::VerifierKey =
        tagged_deserialize(&mut bundle.file(Role::VerifierKey)?)?;
    let mut ledger_parameters: LedgerParameters =
        tagged_deserialize(&mut bundle.file(Role::LedgerParameters)?)?;
    ledger_parameters.fee_prices.overall_price =
        base_crypto::cost_model::FixedPoint::from_u64_div(42, 1);
    let proof_parameters = TrustedParameters::from_bytes(
        &fs::read(parameters_path)?,
        lookup_circuit.k(),
        PARAMETER_SHA256,
    )?;

    let initial = create_state(&store.0, &BTreeMap::from([("profiles".into(), json!([]))]))?;
    let seeded = prepare(
        &store.0,
        &store_inputs(),
        &initial,
        &ledger_parameters,
        ContractAddress::default(),
    )?;
    check(&seeded, &store.1)?;
    let data = seeded.after.state;

    let entrypoint = EntryPointBuf(lookup_plan.entrypoint.as_bytes().to_vec());
    let mut contract = ContractState::<Db>::default();
    contract.data = data.clone();
    contract.operations = contract.operations.insert(
        entrypoint.clone(),
        ContractOperation::new(Some(verifier), None),
    );
    let deployment = ContractDeploy::new(&mut rand::rngs::OsRng, contract);
    let address = deployment.address();
    let mut ledger = LedgerState::<Db>::new("noctium-fixed-byte-read");
    ledger.parameters = Sp::new(ledger_parameters.clone());
    ledger.contract = ledger
        .contract
        .insert(address, deployment.initial_state.clone());

    let execution = prepare(
        &lookup_plan,
        &lookup_inputs(),
        &data,
        &ledger_parameters,
        address,
    )?;
    check(&execution, &lookup_circuit)?;
    let intent = assemble_checked_calls(
        &[CheckedNativeCall {
            execution: &execution,
            circuit: &lookup_circuit,
            initial_context: QueryContext::new(data.clone(), address),
            entry_point: entrypoint,
            communication_commitment_rand: Fr::from(71u64),
        }],
        &ledger.parameters,
        1_800_000_100,
        &mut rand::rngs::OsRng,
    )?;
    let prepared = PreparedComposition::from_intent(
        intent,
        &ledger,
        &[CompositionMaterial {
            bundle: &bundle,
            parameters: &proof_parameters,
        }],
    )
    .context("freeze lookup composition")?;
    let proved = block_on(prepared.prove_locally(rand::rngs::OsRng, futures::future::pending()))
        .context("prove lookup composition")?;

    let tx = Transaction::Standard(StandardTransaction {
        network_id: ledger.network_id.clone(),
        binding_randomness: proved.native().binding_commitment,
        intents: [(1, proved.native().clone())].into_iter().collect(),
        guaranteed_coins: None,
        fallible_coins: Default::default(),
    })
    .seal(StdRng::from_entropy());
    let mut strictness = WellFormedStrictness::default();
    strictness.enforce_balancing = false;
    let timestamp = Timestamp::from_secs(1_800_000_000);
    let verified = tx.clone().well_formed(&ledger, strictness, timestamp)?;
    let block_context = BlockContext {
        tblock: timestamp,
        tblock_err: 0,
        parent_block_hash: HashOutput([0; 32]),
        last_block_time: timestamp,
    };
    let context = TransactionContext {
        ref_state: ledger.clone(),
        block_context: block_context.clone(),
        whitelist: None,
    };
    let (applied, outcome) = ledger.apply(&verified, &context);
    assert!(matches!(outcome, TransactionResult::Success(_)));
    assert_eq!(
        applied.contract.get(&address).unwrap().data.get_ref(),
        data.get_ref()
    );

    let mut stale_ledger = ledger.clone();
    let mut stale_contract = (*stale_ledger.contract.get(&address).unwrap()).clone();
    stale_contract.data = changed_profile_state(&data, false);
    stale_ledger.contract = stale_ledger.contract.insert(address, stale_contract);
    let stale_context = TransactionContext {
        ref_state: stale_ledger.clone(),
        block_context: block_context.clone(),
        whitelist: None,
    };
    let (stale_after, stale_outcome) = stale_ledger.apply(&verified, &stale_context);
    assert!(matches!(stale_outcome, TransactionResult::Failure(_)));
    assert_eq!(
        stale_after.contract.get(&address).unwrap().data.get_ref(),
        stale_ledger.contract.get(&address).unwrap().data.get_ref(),
    );

    let mut malformed_ledger = ledger.clone();
    let mut malformed_contract = (*malformed_ledger.contract.get(&address).unwrap()).clone();
    malformed_contract.data = changed_profile_state(&data, true);
    malformed_ledger.contract = malformed_ledger
        .contract
        .insert(address, malformed_contract);
    let malformed_context = TransactionContext {
        ref_state: malformed_ledger.clone(),
        block_context,
        whitelist: None,
    };
    let (malformed_after, malformed_outcome) =
        malformed_ledger.apply(&verified, &malformed_context);
    assert!(matches!(malformed_outcome, TransactionResult::Failure(_)));
    assert_eq!(
        malformed_after
            .contract
            .get(&address)
            .unwrap()
            .data
            .get_ref(),
        malformed_ledger
            .contract
            .get(&address)
            .unwrap()
            .data
            .get_ref(),
    );
    Ok(())
}
