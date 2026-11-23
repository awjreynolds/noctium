#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use ledger::structure::{ContractDeploy, INITIAL_PARAMETERS, LedgerState, ProofPreimageVersioned};
use noctium_runtime::{
    Db, Plan,
    artifacts::{Role, VerifiedBundle, verify},
    assembly::{CheckedNativeCall, assemble_checked_calls},
    check, create_state, prepare,
    proof::{CompositionMaterial, PreparedComposition, TrustedParameters},
    zkir::IrSource,
};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, ContractOperation, ContractState, EntryPointBuf},
};
use rand::rngs::OsRng;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use transient_crypto::{
    curve::Fr,
    proofs::{VerifierKey, Zkir},
};

fn caller_fixture() -> (Plan, IrSource) {
    (
        serde_json::from_str(include_str!(
            "fixtures/native-call-claims/321/NativeCallClaims.claim.impact.json"
        ))
        .unwrap(),
        IrSource::load(
            include_bytes!("fixtures/native-call-claims/321/NativeCallClaims.claim.zkir")
                .as_slice(),
        )
        .unwrap(),
    )
}

fn callee_fixture() -> (Plan, IrSource) {
    (
        serde_json::from_str(include_str!(
            "fixtures/native-returns/321/NativeReturns.advance.impact.json"
        ))
        .unwrap(),
        IrSource::load(
            include_bytes!("fixtures/native-returns/321/NativeReturns.advance.zkir").as_slice(),
        )
        .unwrap(),
    )
}

fn bytes32(value: HashOutput) -> Json {
    json!({"kind":"bytes", "values":value.0})
}

fn caller_inputs(
    target: HashOutput,
    entry_hash: HashOutput,
    enabled: bool,
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("target".into(), bytes32(target)),
        ("entryHash".into(), bytes32(entry_hash)),
        ("enabled".into(), json!(enabled)),
        ("opening".into(), json!("101")),
        ("argument".into(), json!("3")),
        ("expectedBalance".into(), json!("13")),
        ("expectedCount".into(), json!("1")),
        ("expectedEnabled".into(), json!(false)),
    ])
}

fn callee_inputs() -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("amount".into(), json!("3")),
        ("enabled".into(), json!(false)),
    ])
}

fn interface_caller_inputs(expected_amount: &str) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("opening".into(), json!("101")),
        ("requestAmount".into(), json!("7")),
        ("requestAccepted".into(), json!(true)),
        ("expectedAmount".into(), json!(expected_amount)),
        ("expectedAccepted".into(), json!(true)),
    ])
}

fn interface_callee_inputs() -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("request.amount".into(), json!("7")),
        ("request.accepted".into(), json!("1")),
    ])
}

fn checked_call<'a>(
    execution: &'a noctium_runtime::Execution,
    circuit: &'a IrSource,
    state: ChargedState<noctium_runtime::Db>,
    address: ContractAddress,
    entry_point: EntryPointBuf,
    randomness: Fr,
) -> CheckedNativeCall<'a> {
    CheckedNativeCall {
        execution,
        circuit,
        initial_context: QueryContext::new(state, address),
        entry_point,
        communication_commitment_rand: randomness,
    }
}

#[test]
fn ledger_caller_guard_accepts_only_the_parent_in_the_call_forest() {
    use coin_structure::coin::{PublicAddress, UserAddress};
    use noctium_runtime::prepare_with_context;

    let child_plan: Plan = serde_json::from_slice(include_bytes!(
        "fixtures/contract-caller/321/ProtectedCallee.move.impact.json"
    ))
    .unwrap();
    let child_circuit = IrSource::load(
        include_bytes!("fixtures/contract-caller/321/ProtectedCallee.move.zkir").as_slice(),
    )
    .unwrap();
    let parent_plan: Plan = serde_json::from_slice(include_bytes!(
        "fixtures/contract-caller/321/ForwardingCaller.forward.impact.json"
    ))
    .unwrap();
    let parent_circuit = IrSource::load(
        include_bytes!("fixtures/contract-caller/321/ForwardingCaller.forward.zkir").as_slice(),
    )
    .unwrap();
    let parent = ContractAddress(HashOutput([21; 32]));
    let child = ContractAddress(HashOutput([22; 32]));
    let wrong_parent = ContractAddress(HashOutput([23; 32]));
    let child_state = |enforce, balance| {
        create_state(
            &child_plan,
            &BTreeMap::from([
                ("permitted".into(), bytes32(parent.0)),
                ("enforce".into(), json!(enforce)),
                ("balance".into(), json!(balance)),
            ]),
        )
        .unwrap()
    };
    let child_initial = child_state(true, "10");
    let query = |caller: Option<PublicAddress>| {
        let mut context = QueryContext::new(child_initial.clone(), child);
        context.call_context.caller = caller;
        context
    };
    let child_inputs = BTreeMap::from([("amount".into(), json!("3"))]);
    for imposter in [
        None,
        Some(PublicAddress::User(UserAddress(parent.0))),
        Some(PublicAddress::Contract(wrong_parent)),
    ] {
        assert!(
            prepare_with_context(
                &child_plan,
                &child_inputs,
                query(imposter),
                &INITIAL_PARAMETERS
            )
            .is_err()
        );
    }
    let claimed_child = query(Some(PublicAddress::Contract(parent)));
    let execution = prepare_with_context(
        &child_plan,
        &child_inputs,
        claimed_child.clone(),
        &INITIAL_PARAMETERS,
    )
    .unwrap();
    check(&execution, &child_circuit).unwrap();
    assert_eq!(execution.after.state, child_state(true, "13"));
    let inactive = prepare(
        &child_plan,
        &child_inputs,
        &child_state(false, "10"),
        &INITIAL_PARAMETERS,
        child,
    )
    .unwrap();
    check(&inactive, &child_circuit).unwrap();
    assert_eq!(
        inactive
            .activity_schedule
            .iter()
            .filter_map(|count| *count)
            .collect::<Vec<_>>(),
        [1, 4, 10]
    );

    let child_call = || CheckedNativeCall {
        execution: &execution,
        circuit: &child_circuit,
        initial_context: claimed_child.clone(),
        entry_point: EntryPointBuf(b"move".to_vec()),
        communication_commitment_rand: Fr::from(101u64),
    };
    let assemble = |calls: &[CheckedNativeCall<'_>]| {
        assemble_checked_calls(calls, &INITIAL_PARAMETERS, 1_800_000_000, &mut OsRng)
    };
    assert!(assemble(&[child_call()]).is_err());
    let data = create_state(
        &parent_plan,
        &BTreeMap::from([("marker".into(), json!("0"))]),
    )
    .unwrap();
    for actual in [parent, wrong_parent] {
        let forwarded = prepare(
            &parent_plan,
            &BTreeMap::from([
                ("target".into(), bytes32(child.0)),
                ("opening".into(), json!("101")),
                ("amount".into(), json!("3")),
                ("expected".into(), json!("13")),
            ]),
            &data,
            &INITIAL_PARAMETERS,
            actual,
        )
        .unwrap();
        let parent_call = checked_call(
            &forwarded,
            &parent_circuit,
            data.clone(),
            actual,
            EntryPointBuf(b"forward".to_vec()),
            Fr::from(73u64),
        );
        assert_eq!(
            assemble(&[parent_call, child_call()]).is_ok(),
            actual == parent
        );
    }
}

#[test]
fn native_intent_assembles_a_call_forest_and_rejects_unmatched_claims() {
    let (caller_plan, caller_circuit) = caller_fixture();
    let (callee_plan, callee_circuit) = callee_fixture();
    let caller_address = ContractAddress(HashOutput([7; 32]));
    let callee_address = ContractAddress(HashOutput([42; 32]));
    let caller_state = create_state(
        &caller_plan,
        &BTreeMap::from([("marker".into(), json!("9"))]),
    )
    .unwrap();
    let callee_state = create_state(
        &callee_plan,
        &BTreeMap::from([
            ("balance".into(), json!("10")),
            ("count".into(), json!("0")),
        ]),
    )
    .unwrap();
    let callee_entry = EntryPointBuf::from(b"advance".to_vec());
    let callee_execution = prepare(
        &callee_plan,
        &callee_inputs(),
        &callee_state,
        &INITIAL_PARAMETERS,
        callee_address,
    )
    .unwrap();
    check(&callee_execution, &callee_circuit).unwrap();
    assert_eq!(
        callee_execution.returns_json(),
        BTreeMap::from([
            ("balanceValue".into(), json!("13")),
            ("countValue".into(), json!("1")),
            ("enabledValue".into(), json!(false)),
        ])
    );

    let entry_hash = callee_entry.ep_hash();
    let caller_execution = prepare(
        &caller_plan,
        &caller_inputs(callee_address.0, entry_hash, true),
        &caller_state,
        &INITIAL_PARAMETERS,
        caller_address,
    )
    .unwrap();
    assert_eq!(caller_execution.after.state, caller_state);
    assert_eq!(
        caller_execution.returns_json(),
        BTreeMap::from([("didClaim".into(), json!(true))])
    );
    let callee = || {
        checked_call(
            &callee_execution,
            &callee_circuit,
            callee_state.clone(),
            callee_address,
            callee_entry.clone(),
            Fr::from(101u64),
        )
    };
    let caller = |execution| {
        checked_call(
            execution,
            &caller_circuit,
            caller_state.clone(),
            caller_address,
            EntryPointBuf::from(b"claim".to_vec()),
            Fr::from(53u64),
        )
    };
    let assemble = |calls: &[CheckedNativeCall<'_>]| {
        assemble_checked_calls(calls, &INITIAL_PARAMETERS, 1_800_000_000, &mut OsRng)
    };
    let independent_address = ContractAddress(HashOutput([12; 32]));
    let independent_execution = prepare(
        &callee_plan,
        &callee_inputs(),
        &callee_state,
        &INITIAL_PARAMETERS,
        independent_address,
    )
    .unwrap();
    let independent = || {
        checked_call(
            &independent_execution,
            &callee_circuit,
            callee_state.clone(),
            independent_address,
            callee_entry.clone(),
            Fr::from(102u64),
        )
    };
    let mut with_balance = callee();
    with_balance.initial_context.call_context.balance = [(
        coin_structure::coin::TokenType::Unshielded(coin_structure::coin::NIGHT),
        17,
    )]
    .into_iter()
    .collect();
    let offer_bytes = with_balance
        .composition_offer(&INITIAL_PARAMETERS)
        .unwrap()
        .public_bytes()
        .unwrap();
    let offer =
        noctium_runtime::assembly::CompositionOffer::from_public_bytes(&offer_bytes).unwrap();
    assert_eq!(offer.public_bytes().unwrap(), offer_bytes);
    let mut extra = offer_bytes;
    extra.push(0);
    assert!(noctium_runtime::assembly::CompositionOffer::from_public_bytes(&extra).is_err());

    let intent = assemble(&[caller(&caller_execution), callee(), independent()]).unwrap();
    let assembled: Vec<_> = intent.calls().collect();
    assert_eq!(
        assembled.iter().map(|c| c.address).collect::<Vec<_>>(),
        [caller_address, callee_address, independent_address]
    );
    let ProofPreimageVersioned::V2(preimage) = &assembled[1].proof else {
        panic!("expected a V2 preimage");
    };
    assert_eq!(preimage.inputs, [Fr::from(3u64)]);
    assert_eq!(
        preimage.key_location.0,
        format!("{}:advance", hex::encode(callee_address.0.0))
    );
    assert!(assembled[0].calls(assembled[1]));
    assert!(!assembled[0].calls(assembled[2]));
    assert!(assemble(&[callee(), caller(&caller_execution)]).is_err());
    assert!(assemble(&[caller(&caller_execution)]).is_err());
    assert!(assemble(&[callee(), callee()]).is_err());

    let wrong_tuple = prepare(
        &caller_plan,
        &caller_inputs(HashOutput([43; 32]), entry_hash, true),
        &caller_state,
        &INITIAL_PARAMETERS,
        caller_address,
    )
    .unwrap();
    assert!(assemble(&[caller(&wrong_tuple), callee()]).is_err());

    let wrong_entry = EntryPointBuf::from(b"withdraw".to_vec()).ep_hash();
    let wrong_claims = [
        ("entryHash", bytes32(wrong_entry)),
        ("argument", json!("4")),
        ("expectedBalance", json!("14")),
    ]
    .map(|(field, value)| {
        let mut inputs = caller_inputs(callee_address.0, entry_hash, true);
        inputs.insert(field.into(), value);
        let wrong_claim = prepare(
            &caller_plan,
            &inputs,
            &caller_state,
            &INITIAL_PARAMETERS,
            caller_address,
        )
        .unwrap();
        (field, wrong_claim)
    });
    for (field, wrong_claim) in &wrong_claims {
        check(wrong_claim, &caller_circuit).unwrap();
        assert_eq!(
            assemble(&[caller(wrong_claim), callee()])
                .err()
                .unwrap()
                .to_string(),
            "contract claim has no matching later call in this intent",
            "unexpected result for a claim with the wrong {field}"
        );
    }

    let second_parent_address = ContractAddress(HashOutput([13; 32]));
    let second_parent_execution = prepare(
        &caller_plan,
        &caller_inputs(callee_address.0, entry_hash, true),
        &caller_state,
        &INITIAL_PARAMETERS,
        second_parent_address,
    )
    .unwrap();
    check(&second_parent_execution, &caller_circuit).unwrap();
    let second_parent = checked_call(
        &second_parent_execution,
        &caller_circuit,
        caller_state.clone(),
        second_parent_address,
        EntryPointBuf::from(b"claim".to_vec()),
        Fr::from(107u64),
    );
    let multiple_claims = assemble(&[caller(&caller_execution), second_parent, callee()])
        .err()
        .unwrap()
        .to_string();
    assert!(
        multiple_claims == "contract call has multiple claims"
            || multiple_claims == "official native call forest partition failed",
        "unexpected multiple-parent rejection: {multiple_claims}"
    );

    let prepare_inactive = || {
        prepare(
            &caller_plan,
            &caller_inputs(callee_address.0, entry_hash, false),
            &caller_state,
            &INITIAL_PARAMETERS,
            caller_address,
        )
        .unwrap()
    };
    let inactive = prepare_inactive();
    check(&inactive, &caller_circuit).unwrap();
    assert!(inactive.after.effects.claimed_contract_calls.is_empty());
    assert_eq!(
        inactive.returns_json(),
        BTreeMap::from([("didClaim".into(), json!(false))])
    );
    assert_eq!(
        inactive
            .activity_schedule
            .iter()
            .filter_map(|skip| *skip)
            .collect::<Vec<_>>(),
        [1, 4, 1, 1, 11, 2, 2, 1, 1]
    );
    assert!(assemble(&[caller(&inactive)]).is_ok());

    let mut forged_inactive = prepare_inactive();
    forged_inactive.after.effects = caller_execution.after.effects.clone();
    let mut forged = caller(&forged_inactive);
    forged.initial_context.effects = caller_execution.after.effects.clone();
    assert!(assemble(&[forged, callee()]).is_err());
}

struct Operation {
    bundle: VerifiedBundle,
    plan: Plan,
    circuit: IrSource,
    entry: EntryPointBuf,
    deploy: ContractDeploy<Db>,
    srs: TrustedParameters,
}

impl Operation {
    fn load(role: &str, entry: &str, state: BTreeMap<String, Json>) -> Self {
        let root = PathBuf::from(env::var_os("NOCTIUM_COMPOSITION_BUNDLES").unwrap());
        let role_upper = role.to_ascii_uppercase();
        let pin = env::var(format!("NOCTIUM_COMPOSITION_{role_upper}_SHA256")).unwrap();
        let bundle = verify(&root.join(format!("{role}-bundle")), Some(&pin)).unwrap();
        let plan = serde_json::from_slice::<Plan>(bundle.file(Role::Plan).unwrap()).unwrap();
        let circuit = IrSource::load(bundle.file(Role::Circuit).unwrap()).unwrap();
        let verifier = serialize::tagged_deserialize::<VerifierKey>(
            &mut bundle.file(Role::VerifierKey).unwrap(),
        )
        .unwrap();
        let entry = EntryPointBuf(entry.as_bytes().to_vec());
        let mut contract = ContractState::<Db>::default();
        contract.data = create_state(&plan, &state).unwrap();
        contract.operations = contract
            .operations
            .insert(entry.clone(), ContractOperation::new(Some(verifier), None));
        let deploy = ContractDeploy::new(&mut OsRng, contract);
        let dir = PathBuf::from(env::var_os("NOCTIUM_COMPOSITION_SRS").unwrap());
        let srs = TrustedParameters::from_bytes(
            &fs::read(dir.join(format!("bls_midnight_2p{}", circuit.k()))).unwrap(),
            circuit.k(),
            &env::var(format!("NOCTIUM_COMPOSITION_{role_upper}_SRS_SHA256")).unwrap(),
        )
        .unwrap();
        Self {
            bundle,
            plan,
            circuit,
            entry,
            deploy,
            srs,
        }
    }

    fn proof_selection(&self) -> CompositionMaterial<'_> {
        CompositionMaterial {
            bundle: &self.bundle,
            parameters: &self.srs,
        }
    }
}

struct Pair {
    caller: Operation,
    callee: Operation,
}

impl Pair {
    fn load() -> Self {
        Self {
            caller: Operation::load(
                "caller",
                "claim",
                BTreeMap::from([("marker".into(), json!("9"))]),
            ),
            callee: Operation::load(
                "callee",
                "advance",
                BTreeMap::from([
                    ("balance".into(), json!("10")),
                    ("count".into(), json!("0")),
                ]),
            ),
        }
    }

    fn intent(
        &self,
        ledger: &LedgerState<Db>,
        ttl: u64,
    ) -> noctium_runtime::assembly::NativeIntent {
        let address = self.callee.deploy.address();
        self.intent_with_inputs(
            ledger,
            ttl,
            caller_inputs(address.0, self.callee.entry.ep_hash(), true),
            callee_inputs(),
        )
    }

    fn intent_with_inputs(
        &self,
        ledger: &LedgerState<Db>,
        ttl: u64,
        caller_inputs: BTreeMap<String, Json>,
        callee_inputs: BTreeMap<String, Json>,
    ) -> noctium_runtime::assembly::NativeIntent {
        let mut calls = Vec::new();
        let mut executions = Vec::new();
        for (operation, inputs, opening) in [
            (&self.caller, caller_inputs, 53u64),
            (&self.callee, callee_inputs, 101u64),
        ] {
            let address = operation.deploy.address();
            let data = ledger.contract.get(&address).unwrap().data.clone();
            executions.push((
                operation,
                address,
                prepare(&operation.plan, &inputs, &data, &ledger.parameters, address).unwrap(),
                data,
                Fr::from(opening),
            ));
        }
        for (operation, address, execution, data, opening) in &executions {
            calls.push(checked_call(
                execution,
                &operation.circuit,
                data.clone(),
                *address,
                operation.entry.clone(),
                *opening,
            ));
        }
        assemble_checked_calls(&calls, &ledger.parameters, ttl, &mut OsRng).unwrap()
    }

    fn materials(&self) -> [CompositionMaterial<'_>; 2] {
        [self.caller.proof_selection(), self.callee.proof_selection()]
    }
}

#[test]
#[ignore = "requires independently pinned caller/callee bundles and their native SRS files"]
fn composed_intent_attaches_both_proofs_against_installed_keys() {
    use base_crypto::time::Timestamp;
    use futures::{executor::block_on, future::pending};
    use ledger::{
        structure::{LedgerParameters, StandardTransaction, Transaction},
        verify::WellFormedStrictness,
    };
    use noctium_runtime::proof::Error;
    use rand::{SeedableRng, rngs::StdRng};

    let pair = Pair::load();
    let mut ledger = LedgerState::<Db>::new("local");
    let mut ledger_parameters = serialize::tagged_deserialize::<LedgerParameters>(
        &mut pair.caller.bundle.file(Role::LedgerParameters).unwrap(),
    )
    .unwrap();
    ledger_parameters.fee_prices.overall_price =
        base_crypto::cost_model::FixedPoint::from_u64_div(42, 1);
    ledger.parameters = storage::arena::Sp::new(ledger_parameters);
    for operation in [&pair.caller, &pair.callee] {
        ledger.contract = ledger.contract.insert(
            operation.deploy.address(),
            operation.deploy.initial_state.clone(),
        );
    }
    let before = 1_800_000_000;
    let intent = pair.intent(&ledger, before + 30);

    let mut wrong_ledger = ledger.clone();
    let mut wrong_callee = pair.callee.deploy.initial_state.clone();
    let wrong_verifier = serialize::tagged_deserialize::<VerifierKey>(
        &mut pair.caller.bundle.file(Role::VerifierKey).unwrap(),
    )
    .unwrap();
    wrong_callee.operations = wrong_callee.operations.insert(
        pair.callee.entry.clone(),
        ContractOperation::new(Some(wrong_verifier), None),
    );
    wrong_ledger.contract = wrong_ledger
        .contract
        .insert(pair.callee.deploy.address(), wrong_callee);
    assert_eq!(
        PreparedComposition::from_intent(intent.clone(), &wrong_ledger, &pair.materials()).err(),
        Some(Error::BindingMismatch)
    );
    let prepared = PreparedComposition::from_intent(intent, &ledger, &pair.materials()).unwrap();
    let proved = block_on(prepared.prove_locally(OsRng, pending())).unwrap();
    let tx = Transaction::Standard(StandardTransaction {
        network_id: ledger.network_id.clone(),
        binding_randomness: proved.native().binding_commitment,
        intents: [(1, proved.native().clone())].into_iter().collect(),
        guaranteed_coins: None,
        fallible_coins: Default::default(),
    });
    let mut strictness = WellFormedStrictness::default();
    strictness.enforce_balancing = false;
    tx.seal(StdRng::from_entropy())
        .well_formed(&ledger, strictness, Timestamp::from_secs(before))
        .unwrap();
}

#[cfg(feature = "localnet")]
#[path = "native_composition/owner.rs"]
mod owner;

#[cfg(feature = "localnet")]
#[test]
#[ignore = "spends only the public development wallet on the explicit isolated Midnight localnet"]
fn composed_intent_finalizes_both_contract_states_on_localnet() {
    run_local_composition(LocalCase::Plain);
}

#[cfg(feature = "localnet")]
#[test]
#[ignore = "uses independently prepared calls and the funded isolated localnet"]
fn independent_processes_compose_on_localnet() {
    run_local_composition(LocalCase::Independent);
}

#[cfg(feature = "localnet")]
#[test]
#[ignore = "uses the isolated development wallet and the three registry operation bundles"]
fn registry_rotation_routes_two_finalized_calls_without_redeploying() {
    run_local_composition(LocalCase::Registry);
}

#[cfg(feature = "localnet")]
#[test]
#[ignore = "uses the isolated development wallet and authenticated caller bundles"]
fn composed_call_finalizes_with_a_ledger_authenticated_parent() {
    run_local_composition(LocalCase::Caller);
}

#[cfg(feature = "localnet")]
#[test]
#[ignore = "uses the isolated development wallet and typed caller composition bundles"]
fn composed_call_claims_typed_caller_outputs_and_rejects_a_wrong_parent() {
    run_local_composition(LocalCase::TypedCaller);
}

#[cfg(feature = "localnet")]
#[test]
#[ignore = "uses the isolated development wallet and typed-reference caller/callee bundles"]
fn stored_typed_contract_reference_finalizes_record_key_route() {
    run_local_composition(LocalCase::TypedReference);
}

#[cfg(feature = "localnet")]
#[test]
#[ignore = "uses the isolated development wallet and aggregate result bundles"]
fn composed_call_finalizes_with_named_aggregate_results() {
    run_local_composition(LocalCase::Aggregate);
}

#[cfg(feature = "localnet")]
#[test]
#[ignore = "uses the isolated development wallet and typed interface bundles"]
fn interface_selected_aggregate_call_observes_both_states_and_rejects_mismatch() {
    run_local_composition(LocalCase::Interface);
}

#[cfg(feature = "localnet")]
enum LocalCase {
    Plain,
    Independent,
    Registry,
    Caller,
    TypedCaller,
    TypedReference,
    Aggregate,
    Interface,
}

#[cfg(feature = "localnet")]
fn run_local_composition(case: LocalCase) {
    use base_crypto::time::Timestamp;
    use futures::{executor::block_on, future::pending};
    use noctium_runtime::{
        assembly::NativeIntent,
        client::{BoundTransaction, ChainAdapter, FinalizedReceipt, NetworkPolicy, Submission},
        funding::{CONTRACT_SEGMENT, FeePolicy, UnsealedTransaction},
        localnet::{DevelopmentFunding, ExplicitSeal, Node, ProofCache},
        proof::ProvedNativeIntent,
    };
    use rand::{SeedableRng, rngs::StdRng};
    use sha2::{Digest, Sha256};
    use std::time::{Duration, Instant};

    block_on(async {
        let policy = development_policy();
        let node = Node::connect(
            &env::var("NOCTIUM_COMPOSITION_NODE").unwrap(),
            policy.clone(),
            Duration::from_secs(30),
            64 * 1024 * 1024,
            100_000,
        )
        .unwrap();
        let mut seed = [0u8; 32];
        seed[31] = 1;
        node.attach_dust_seed(&seed).unwrap();
        let cache = ProofCache::new(
            PathBuf::from(env::var_os("NOCTIUM_COMPOSITION_SRS").unwrap()),
            "https://srs.midnight.network/".parse().unwrap(),
        )
        .unwrap();
        let dust = cache.dust().await.unwrap();
        let dust_srs = cache.parameters(dust.k()).await.unwrap();
        eprintln!("sync localnet");
        let snapshot = node.sync().unwrap();
        let submit = async |intent: &ProvedNativeIntent| -> FinalizedReceipt {
            let funding = DevelopmentFunding::new(
                &node,
                &dust,
                &dust_srs,
                FeePolicy {
                    max_dust: policy.max_dust,
                    margin_blocks: 3,
                    max_spends: 8,
                },
                StdRng::from_entropy(),
            );
            let signer = ExplicitSeal::new(
                |_: &UnsealedTransaction, actual: &NetworkPolicy| actual == &policy,
                StdRng::from_entropy(),
            );
            let bound = BoundTransaction::prepare(intent, policy.clone(), &node, &funding, &signer)
                .await
                .unwrap();
            eprintln!("submit {}", bound.transaction_id());
            assert!(!matches!(
                node.submit(&bound).await.unwrap(),
                Submission::Rejected
            ));
            let deadline = Instant::now() + Duration::from_secs(120);
            loop {
                if let Some(receipt) = node.finalized_receipt(&bound).unwrap() {
                    bound.check_receipt(&receipt).unwrap();
                    return receipt;
                }
                assert!(Instant::now() < deadline, "localnet finality timeout");
                std::thread::sleep(Duration::from_secs(2));
            }
        };

        let ttl = snapshot.block.tblock.to_secs() + 1800;
        let deploy = async |deployment: &ContractDeploy<Db>| {
            let intent = NativeIntent::empty(&mut OsRng, Timestamp::from_secs(ttl))
                .add_deploy(deployment.clone());
            let provider = builtin_zkir::LocalProvingProvider {
                rng: StdRng::from_entropy(),
                resolver: &dust,
                params: &dust_srs,
            };
            let (_, deployment) = intent
                .prove(
                    CONTRACT_SEGMENT,
                    provider,
                    &snapshot.state.parameters.cost_model.runtime_cost_model,
                )
                .await
                .unwrap();
            submit(&deployment).await
        };
        match case {
            LocalCase::Plain
            | LocalCase::Independent
            | LocalCase::Aggregate
            | LocalCase::Interface => {}
            LocalCase::Registry => return qualify_registry(&node, deploy, submit).await,
            LocalCase::Caller => return qualify_caller(&node, deploy, submit).await,
            LocalCase::TypedCaller => return qualify_typed_caller(&node, deploy, submit).await,
            LocalCase::TypedReference => {
                return qualify_stored_typed_reference(&node, deploy, submit).await
            }
        }
        let independent = matches!(case, LocalCase::Independent);
        let aggregate = matches!(case, LocalCase::Aggregate);
        let interface = matches!(case, LocalCase::Interface);
        let mut owners = independent.then(owner::Owners::spawn);
        let pair = if let Some(owners) = &owners {
            let caller_state =
                BTreeMap::from([("acceptedCredential".into(), owners.credentials[0].clone())]);
            let callee_state = BTreeMap::from([
                ("balance".into(), json!("10")),
                ("count".into(), json!("0")),
                ("acceptedCredential".into(), owners.credentials[1].clone()),
            ]);
            Pair {
                caller: Operation::load("caller", "claim", caller_state),
                callee: Operation::load("callee", "advance", callee_state),
            }
        } else if aggregate {
            let callee = Operation::load("callee", "inspectPayment", BTreeMap::new());
            let caller = Operation::load(
                "caller",
                "claim",
                BTreeMap::from([("route".into(), bytes32(callee.deploy.address().0))]),
            );
            Pair { caller, callee }
        } else if interface {
            let callee = Operation::load(
                "callee",
                "claim",
                BTreeMap::from([("calls".into(), json!("0"))]),
            );
            let caller = Operation::load(
                "caller",
                "claim",
                BTreeMap::from([
                    ("route".into(), bytes32(callee.deploy.address().0)),
                    ("calls".into(), json!("0")),
                ]),
            );
            Pair { caller, callee }
        } else {
            Pair::load()
        };
        let mut deployment_receipts = Vec::new();
        for operation in [&pair.caller, &pair.callee] {
            deployment_receipts.push(deploy(&operation.deploy).await);
        }
        let live = node.sync().unwrap();
        let ttl = live.block.tblock.to_secs() + 1800;
        let (proved, exchange) = if let Some(owners) = &mut owners {
            let (proved, exchange) = owners.compose(&pair, &live.state, ttl);
            (proved, Some(exchange))
        } else {
            let intent = if aggregate {
                pair.intent_with_inputs(
                    &live.state,
                    ttl,
                    BTreeMap::from([
                        ("opening".into(), json!("101")),
                        ("amount".into(), json!("300")),
                        ("approved".into(), json!(true)),
                        (
                            "expectedMemo".into(),
                            json!({"kind":"bytes","values":[12,42]}),
                        ),
                    ]),
                    BTreeMap::from([(
                        "frame".into(),
                        json!({"kind":"bytes","values":[44,1,1,0,1,1,12,42,200,255]}),
                    )]),
                )
            } else if interface {
                let caller_inputs = interface_caller_inputs("7");
                let callee_inputs = interface_callee_inputs();
                let wrong_caller_inputs = interface_caller_inputs("8");
                let caller_address = pair.caller.deploy.address();
                let callee_address = pair.callee.deploy.address();
                let caller_data = live
                    .state
                    .contract
                    .get(&caller_address)
                    .unwrap()
                    .data
                    .clone();
                let callee_data = live
                    .state
                    .contract
                    .get(&callee_address)
                    .unwrap()
                    .data
                    .clone();
                let wrong_caller = prepare(
                    &pair.caller.plan,
                    &wrong_caller_inputs,
                    &caller_data,
                    &live.state.parameters,
                    caller_address,
                )
                .unwrap();
                let callee_execution = prepare(
                    &pair.callee.plan,
                    &callee_inputs,
                    &callee_data,
                    &live.state.parameters,
                    callee_address,
                )
                .unwrap();
                let wrong_calls = [
                    checked_call(
                        &wrong_caller,
                        &pair.caller.circuit,
                        caller_data,
                        caller_address,
                        pair.caller.entry.clone(),
                        Fr::from(53u64),
                    ),
                    checked_call(
                        &callee_execution,
                        &pair.callee.circuit,
                        callee_data,
                        callee_address,
                        pair.callee.entry.clone(),
                        Fr::from(101u64),
                    ),
                ];
                assert!(
                    assemble_checked_calls(&wrong_calls, &live.state.parameters, ttl, &mut OsRng,)
                        .is_err(),
                    "a caller claiming a different aggregate result must fail before proving"
                );
                pair.intent_with_inputs(&live.state, ttl, caller_inputs, callee_inputs)
            } else {
                pair.intent(&live.state, ttl)
            };
            let prepared =
                PreparedComposition::from_intent(intent, &live.state, &pair.materials()).unwrap();
            (
                prepared.prove_locally(OsRng, pending()).await.unwrap(),
                None,
            )
        };
        let receipt = submit(proved.native()).await;
        assert_eq!(
            receipt.contract_address,
            hex::encode(pair.caller.deploy.address().0.0)
        );
        if interface {
            let expected_caller = create_state(
                &pair.caller.plan,
                &BTreeMap::from([
                    ("route".into(), bytes32(pair.callee.deploy.address().0)),
                    ("calls".into(), json!("1")),
                ]),
            )
            .unwrap();
            assert_eq!(
                serialize::tagged_deserialize::<ContractState<Db>>(
                    &mut receipt.contract_state.as_slice()
                )
                .unwrap()
                .data,
                expected_caller
            );
        } else {
            assert_eq!(
                receipt.contract_state,
                deployment_receipts[0].contract_state
            );
        }
        let address = hex::encode(pair.callee.deploy.address().0.0);
        let bytes = &receipt.secondary_states[&address];
        let callee_state =
            serialize::tagged_deserialize::<ContractState<Db>>(&mut bytes.as_slice()).unwrap();
        let mut expected_state = if interface {
            BTreeMap::from([("calls".into(), json!("1"))])
        } else {
            BTreeMap::from([
                ("balance".into(), json!("13")),
                ("count".into(), json!("1")),
            ])
        };
        if let Some(owners) = &owners {
            expected_state.insert("acceptedCredential".into(), owners.credentials[1].clone());
        }
        let mut callee_receipt =
            json!({"address": address, "stateSha256": hex::encode(Sha256::digest(bytes))});
        if aggregate {
            assert_eq!(bytes, &deployment_receipts[1].contract_state);
        } else {
            let expected = create_state(&pair.callee.plan, &expected_state).unwrap();
            assert_eq!(callee_state.data, expected);
            if interface {
                callee_receipt["calls"] = json!("1");
            } else {
                callee_receipt["balance"] = json!("13");
                callee_receipt["count"] = json!("1");
            }
        }
        eprintln!(
            "{}",
            json!({
                "genesis": receipt.chain.genesis,
                "profile": receipt.chain.profile,
                "independentProvers": independent,
                "publicExchange": exchange,
                "height": receipt.height,
                "blockHash": receipt.block_hash,
                "transactionId": receipt.transaction_id,
                "intentId": receipt.intent_id,
                "extrinsicHash": receipt.extrinsic_hash,
                "extrinsicIndex": receipt.extrinsic_index,
                "deployments": deployment_receipts.iter().map(|r| json!({
                    "address": r.contract_address, "height": r.height, "transactionId":r.transaction_id,
                    "blockHash":r.block_hash,
                })).collect::<Vec<_>>(),
                "caller": {"address": receipt.contract_address, "stateSha256": hex::encode(Sha256::digest(&receipt.contract_state))},
                "callee": callee_receipt,
            })
        );
    });
}

#[cfg(feature = "localnet")]
fn development_policy() -> noctium_runtime::client::NetworkPolicy {
    noctium_runtime::client::NetworkPolicy {
        network_id: "undeployed".into(),
        genesis: "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d".into(),
        spec_version: 2001100,
        transaction_version: 4,
        profile: noctium_runtime::profile::NAME.into(),
        max_dust: 10u128.pow(22),
    }
}

#[cfg(feature = "localnet")]
async fn qualify_caller(
    node: &noctium_runtime::localnet::Node,
    deploy: impl AsyncFn(&ContractDeploy<Db>) -> noctium_runtime::client::FinalizedReceipt,
    submit: impl AsyncFn(
        &noctium_runtime::proof::ProvedNativeIntent,
    ) -> noctium_runtime::client::FinalizedReceipt,
) {
    use coin_structure::coin::PublicAddress;
    use futures::future::pending;
    use noctium_runtime::prepare_with_context;

    let caller = Operation::load(
        "caller",
        "forward",
        BTreeMap::from([("marker".into(), json!("0"))]),
    );
    let parent = caller.deploy.address();
    let callee_state = |balance| {
        BTreeMap::from([
            ("permitted".into(), bytes32(parent.0)),
            ("enforce".into(), json!(true)),
            ("balance".into(), json!(balance)),
        ])
    };
    let callee = Operation::load("callee", "move", callee_state("10"));
    let child = callee.deploy.address();
    let parent_deployed = deploy(&caller.deploy).await;
    let child_deployed = deploy(&callee.deploy).await;
    let live = node.sync().unwrap();
    let parent_state = live.state.contract.get(&parent).unwrap().data.clone();
    let child_state = live.state.contract.get(&child).unwrap().data.clone();
    let forwarded = prepare(
        &caller.plan,
        &BTreeMap::from([
            ("target".into(), bytes32(child.0)),
            ("opening".into(), json!("101")),
            ("amount".into(), json!("3")),
            ("expected".into(), json!("13")),
        ]),
        &parent_state,
        &live.state.parameters,
        parent,
    )
    .unwrap();
    let mut context = QueryContext::new(child_state, child);
    context.call_context.caller = Some(PublicAddress::Contract(parent));
    let protected = prepare_with_context(
        &callee.plan,
        &BTreeMap::from([("amount".into(), json!("3"))]),
        context.clone(),
        &live.state.parameters,
    )
    .unwrap();
    let calls = [
        checked_call(
            &forwarded,
            &caller.circuit,
            parent_state,
            parent,
            caller.entry.clone(),
            Fr::from(73u64),
        ),
        CheckedNativeCall {
            execution: &protected,
            circuit: &callee.circuit,
            initial_context: context,
            entry_point: callee.entry.clone(),
            communication_commitment_rand: Fr::from(101u64),
        },
    ];
    let intent = assemble_checked_calls(
        &calls,
        &live.state.parameters,
        live.block.tblock.to_secs() + 1800,
        &mut OsRng,
    )
    .unwrap();
    let selected = [caller.proof_selection(), callee.proof_selection()];
    let prepared = PreparedComposition::from_intent(intent, &live.state, &selected).unwrap();
    let proved = prepared.prove_locally(OsRng, pending()).await.unwrap();
    let receipt = submit(proved.native()).await;
    let address = hex::encode(child.0.0);
    let bytes = &receipt.secondary_states[&address];
    let state = serialize::tagged_deserialize::<ContractState<Db>>(&mut bytes.as_slice()).unwrap();
    assert_eq!(receipt.contract_address, hex::encode(parent.0.0));
    assert_eq!(receipt.contract_state, parent_deployed.contract_state);
    assert_eq!(
        state.data,
        create_state(&callee.plan, &callee_state("13")).unwrap()
    );
    eprintln!(
        "{}",
        json!({
            "genesis": receipt.chain.genesis, "profile": receipt.chain.profile, "height": receipt.height,
            "blockHash": receipt.block_hash, "transactionId": receipt.transaction_id, "extrinsicHash": receipt.extrinsic_hash,
            "caller": {"address":receipt.contract_address,"deploymentHeight":parent_deployed.height},
            "callee": {"address":address,"deploymentHeight":child_deployed.height,"balance":"13"},
        })
    );
}

#[cfg(feature = "localnet")]
async fn qualify_typed_caller(
    node: &noctium_runtime::localnet::Node,
    deploy: impl AsyncFn(&ContractDeploy<Db>) -> noctium_runtime::client::FinalizedReceipt,
    submit: impl AsyncFn(
        &noctium_runtime::proof::ProvedNativeIntent,
    ) -> noctium_runtime::client::FinalizedReceipt,
) {
    use coin_structure::coin::PublicAddress;
    use futures::future::pending;
    use noctium_runtime::prepare_with_context;

    let reporter = Operation::load(
        "caller",
        "forward",
        BTreeMap::from([(
            "observedCaller".into(),
            bytes32(HashOutput([0; 32])),
        )]),
    );
    let reporter_address = reporter.deploy.address();
    let lookup = Operation::load(
        "callee",
        "lookup",
        BTreeMap::from([("recorded".into(), json!(false))]),
    );
    let lookup_address = lookup.deploy.address();
    let reporter_deployment = deploy(&reporter.deploy).await;
    let lookup_deployment = deploy(&lookup.deploy).await;
    let live = node.sync().unwrap();
    let ttl = live.block.tblock.to_secs() + 1800;
    let reporter_data = live
        .state
        .contract
        .get(&reporter_address)
        .unwrap()
        .data
        .clone();
    let lookup_data = live
        .state
        .contract
        .get(&lookup_address)
        .unwrap()
        .data
        .clone();
    let reporter_inputs = |expected_parent: ContractAddress| {
        BTreeMap::from([
            ("target".into(), bytes32(lookup_address.0)),
            ("opening".into(), json!("101")),
            ("expectedParent".into(), bytes32(expected_parent.0)),
        ])
    };
    let lookup_inputs = BTreeMap::from([("enabled".into(), json!(true))]);
    let mut lookup_context = QueryContext::new(lookup_data.clone(), lookup_address);
    lookup_context.call_context.caller = Some(PublicAddress::Contract(reporter_address));
    let lookup_execution = prepare_with_context(
        &lookup.plan,
        &lookup_inputs,
        lookup_context.clone(),
        &live.state.parameters,
    )
    .unwrap();
    assert_eq!(
        check(&lookup_execution, &lookup.circuit).unwrap(),
        lookup_execution.activity_schedule
    );
    assert_eq!(
        lookup_execution.returns_json(),
        BTreeMap::from([
            ("hasCaller".into(), json!(true)),
            ("contractCaller".into(), json!(true)),
            ("callerContract".into(), bytes32(reporter_address.0)),
            ("callerUser".into(), bytes32(HashOutput([0; 32]))),
        ])
    );
    assert_eq!(
        lookup_execution.after.state,
        create_state(&lookup.plan, &BTreeMap::from([("recorded".into(), json!(true))])).unwrap()
    );

    let reporter_execution = prepare(
        &reporter.plan,
        &reporter_inputs(reporter_address),
        &reporter_data,
        &live.state.parameters,
        reporter_address,
    )
    .unwrap();
    assert_eq!(
        check(&reporter_execution, &reporter.circuit).unwrap(),
        reporter_execution.activity_schedule
    );
    assert_eq!(
        reporter_execution.after.state,
        create_state(
            &reporter.plan,
            &BTreeMap::from([("observedCaller".into(), bytes32(reporter_address.0))]),
        )
        .unwrap()
    );
    let lookup_call = || CheckedNativeCall {
        execution: &lookup_execution,
        circuit: &lookup.circuit,
        initial_context: lookup_context.clone(),
        entry_point: lookup.entry.clone(),
        communication_commitment_rand: Fr::from(101u64),
    };
    let reporter_call = |execution| {
        checked_call(
            execution,
            &reporter.circuit,
            reporter_data.clone(),
            reporter_address,
            reporter.entry.clone(),
            Fr::from(73u64),
        )
    };
    let wrong_parent = ContractAddress(HashOutput([0xff; 32]));
    assert_ne!(wrong_parent, reporter_address);
    let wrong_execution = prepare(
        &reporter.plan,
        &reporter_inputs(wrong_parent),
        &reporter_data,
        &live.state.parameters,
        reporter_address,
    )
    .unwrap();
    check(&wrong_execution, &reporter.circuit).unwrap();
    assert!(
        assemble_checked_calls(
            &[reporter_call(&wrong_execution), lookup_call()],
            &live.state.parameters,
            ttl,
            &mut OsRng,
        )
        .is_err(),
        "a reporter claiming a different expected parent must fail composition validation"
    );

    let intent = assemble_checked_calls(
        &[reporter_call(&reporter_execution), lookup_call()],
        &live.state.parameters,
        ttl,
        &mut OsRng,
    )
    .unwrap();
    let selected = [reporter.proof_selection(), lookup.proof_selection()];
    let prepared = PreparedComposition::from_intent(intent, &live.state, &selected).unwrap();
    let proved = prepared.prove_locally(OsRng, pending()).await.unwrap();
    let receipt = submit(proved.native()).await;

    let expected_reporter = create_state(
        &reporter.plan,
        &BTreeMap::from([("observedCaller".into(), bytes32(reporter_address.0))]),
    )
    .unwrap();
    let finalized_reporter = serialize::tagged_deserialize::<ContractState<Db>>(
        &mut receipt.contract_state.as_slice(),
    )
    .unwrap();
    assert_eq!(receipt.contract_address, hex::encode(reporter_address.0.0));
    assert_eq!(finalized_reporter.data, expected_reporter);
    assert_eq!(receipt.secondary_states.len(), 1);
    let lookup_bytes = &receipt.secondary_states[&hex::encode(lookup_address.0.0)];
    let finalized_lookup =
        serialize::tagged_deserialize::<ContractState<Db>>(&mut lookup_bytes.as_slice()).unwrap();
    let expected_lookup =
        create_state(&lookup.plan, &BTreeMap::from([("recorded".into(), json!(true))])).unwrap();
    assert_eq!(finalized_lookup.data, expected_lookup);
    eprintln!(
        "{}",
        json!({
            "genesis": receipt.chain.genesis,
            "profile": receipt.chain.profile,
            "height": receipt.height,
            "blockHash": receipt.block_hash,
            "transactionId": receipt.transaction_id,
            "extrinsicHash": receipt.extrinsic_hash,
            "deployments": [
                {"role":"caller","address":hex::encode(reporter_address.0.0),"height":reporter_deployment.height,"transactionId":reporter_deployment.transaction_id},
                {"role":"callee","address":hex::encode(lookup_address.0.0),"height":lookup_deployment.height,"transactionId":lookup_deployment.transaction_id},
            ],
            "reporterObservedCaller": hex::encode(reporter_address.0.0),
            "calleeRecorded": true,
            "typedCallerReturnsMatched": true,
            "wrongExpectedParentRejectedBeforeSubmission": true,
        })
    );
}

#[cfg(feature = "localnet")]
async fn qualify_stored_typed_reference(
    node: &noctium_runtime::localnet::Node,
    deploy: impl AsyncFn(&ContractDeploy<Db>) -> noctium_runtime::client::FinalizedReceipt,
    submit: impl AsyncFn(
        &noctium_runtime::proof::ProvedNativeIntent,
    ) -> noctium_runtime::client::FinalizedReceipt,
) {
    use futures::future::pending;

    let callee = Operation::load(
        "callee",
        "update",
        BTreeMap::from([("total".into(), json!("0"))]),
    );
    let mut caller = Operation::load(
        "caller",
        "forward",
        BTreeMap::from([
            ("routes".into(), json!([])),
            ("direct".into(), json!([])),
            ("nested".into(), json!([])),
        ]),
    );
    // The same source contract emits insertRoute and forward plans. Seed all
    // of its collection slots through insertRoute before deploying forward.
    let artifacts = PathBuf::from(env::var_os("NOCTIUM_TYPED_CONTRACT_REFERENCE_DIR").unwrap());
    let put_plan: Plan = serde_json::from_slice(
        &fs::read(artifacts.join("TypedRefRecordKeyCaller.insertRoute.impact.json")).unwrap(),
    )
    .unwrap();
    let put_circuit = IrSource::load(
        fs::read(artifacts.join("TypedRefRecordKeyCaller.insertRoute.zkir"))
            .unwrap()
            .as_slice(),
    )
    .unwrap();

    let live = node.sync().unwrap();
    let target_address = callee.deploy.address();
    let key_target = ContractAddress(HashOutput([0xa7; 32]));
    assert_ne!(key_target, target_address);
    let reference = bytes32(target_address.0);
    let put_inputs = BTreeMap::from([
        ("keyTarget".into(), bytes32(key_target.0)),
        ("replacement".into(), reference.clone()),
    ]);
    let put_execution = prepare(
        &put_plan,
        &put_inputs,
        &caller.deploy.initial_state.data,
        &live.state.parameters,
        caller.deploy.address(),
    )
    .unwrap();
    check(&put_execution, &put_circuit).unwrap();

    let mut seeded_caller = caller.deploy.initial_state.clone();
    seeded_caller.data = put_execution.after.state.clone();
    caller.deploy = ContractDeploy::new(&mut OsRng, seeded_caller);
    let caller_address = caller.deploy.address();
    let deployments = [deploy(&callee.deploy).await, deploy(&caller.deploy).await];
    assert_eq!(
        deployments[0].contract_address,
        hex::encode(target_address.0.0)
    );
    assert_eq!(
        deployments[1].contract_address,
        hex::encode(caller_address.0.0)
    );

    let live = node.sync().unwrap();
    let ttl = live.block.tblock.to_secs() + 1800;
    let caller_data = live
        .state
        .contract
        .get(&caller_address)
        .expect("deployed typed-reference caller")
        .data
        .clone();
    assert_eq!(caller_data, put_execution.after.state);
    let callee_data = live
        .state
        .contract
        .get(&target_address)
        .expect("deployed typed-reference callee")
        .data
        .clone();
    let forward_inputs = BTreeMap::from([
        ("keyTarget".into(), bytes32(key_target.0)),
        ("opening".into(), json!("101")),
        ("amount".into(), json!("7")),
        ("expected".into(), json!("7")),
    ]);
    let callee_inputs = BTreeMap::from([("amount".into(), json!("7"))]);
    let forward = prepare(
        &caller.plan,
        &forward_inputs,
        &caller_data,
        &live.state.parameters,
        caller_address,
    )
    .unwrap();
    check(&forward, &caller.circuit).unwrap();
    let update = prepare(
        &callee.plan,
        &callee_inputs,
        &callee_data,
        &live.state.parameters,
        target_address,
    )
    .unwrap();
    check(&update, &callee.circuit).unwrap();
    let expected_callee = create_state(
        &callee.plan,
        &BTreeMap::from([("total".into(), json!("7"))]),
    )
    .unwrap();
    assert_eq!(update.after.state, expected_callee);
    assert_eq!(
        update.returns_json(),
        BTreeMap::from([("stored".into(), json!("7"))])
    );

    let assemble = |parent: &noctium_runtime::Execution,
                    child: &noctium_runtime::Execution,
                    child_address: ContractAddress,
                    child_entry: EntryPointBuf| {
        assemble_checked_calls(
            &[
                checked_call(
                    parent,
                    &caller.circuit,
                    caller_data.clone(),
                    caller_address,
                    EntryPointBuf(b"forward".to_vec()),
                    Fr::from(53u64),
                ),
                checked_call(
                    child,
                    &callee.circuit,
                    callee_data.clone(),
                    child_address,
                    child_entry,
                    Fr::from(101u64),
                ),
            ],
            &live.state.parameters,
            ttl,
            &mut OsRng,
        )
    };
    let wrong_target = prepare(
        &callee.plan,
        &callee_inputs,
        &callee_data,
        &live.state.parameters,
        key_target,
    )
    .unwrap();
    check(&wrong_target, &callee.circuit).unwrap();
    assert!(
        assemble(
            &forward,
            &wrong_target,
            key_target,
            callee.entry.clone(),
        )
        .is_err(),
        "the record key is not the stored call target"
    );
    assert!(
        assemble(
            &forward,
            &update,
            target_address,
            EntryPointBuf(b"other".to_vec()),
        )
        .is_err(),
        "a stored reference must select its declared operation"
    );
    let mut wrong_expected_inputs = forward_inputs.clone();
    wrong_expected_inputs.insert("expected".into(), json!("8"));
    let wrong_expected = prepare(
        &caller.plan,
        &wrong_expected_inputs,
        &caller_data,
        &live.state.parameters,
        caller_address,
    )
    .unwrap();
    check(&wrong_expected, &caller.circuit).unwrap();
    assert!(
        assemble(
            &wrong_expected,
            &update,
            target_address,
            callee.entry.clone(),
        )
        .is_err(),
        "a stored typed-reference call must match the expected result"
    );

    let intent = assemble(
        &forward,
        &update,
        target_address,
        callee.entry.clone(),
    )
    .unwrap();
    let selected = [caller.proof_selection(), callee.proof_selection()];
    let prepared = PreparedComposition::from_intent(intent, &live.state, &selected).unwrap();
    let proved = prepared.prove_locally(OsRng, pending()).await.unwrap();
    let receipt = submit(proved.native()).await;

    assert_eq!(receipt.contract_address, hex::encode(caller_address.0.0));
    assert_eq!(receipt.secondary_states.len(), 1);
    let target_bytes = &receipt.secondary_states[&hex::encode(target_address.0.0)];
    let finalized_target =
        serialize::tagged_deserialize::<ContractState<Db>>(&mut target_bytes.as_slice()).unwrap();
    assert_eq!(finalized_target.data, expected_callee);
    assert_eq!(
        receipt.contract_state,
        deployments[1].contract_state,
        "forward leaves the caller's stored route unchanged"
    );
    eprintln!(
        "{}",
        json!({
            "genesis": receipt.chain.genesis,
            "profile": receipt.chain.profile,
            "height": receipt.height,
            "blockHash": receipt.block_hash,
            "transactionId": receipt.transaction_id,
            "extrinsicHash": receipt.extrinsic_hash,
            "deployments": [
                {"role":"callee","address":hex::encode(target_address.0.0),"height":deployments[0].height,"transactionId":deployments[0].transaction_id},
                {"role":"caller","address":hex::encode(caller_address.0.0),"height":deployments[1].height,"transactionId":deployments[1].transaction_id},
            ],
            "keyTarget": hex::encode(key_target.0.0),
            "replacement": hex::encode(target_address.0.0),
            "callerStateUnchanged": true,
            "calleeTotal": "7",
            "wrongTargetRejectedBeforeProof": true,
            "wrongSelectorRejectedBeforeProof": true,
            "wrongExpectedResultRejectedBeforeProof": true,
        })
    );
}

#[cfg(feature = "localnet")]
async fn qualify_registry(
    node: &noctium_runtime::localnet::Node,
    deploy: impl AsyncFn(&ContractDeploy<Db>) -> noctium_runtime::client::FinalizedReceipt,
    submit: impl AsyncFn(
        &noctium_runtime::proof::ProvedNativeIntent,
    ) -> noctium_runtime::client::FinalizedReceipt,
) {
    use futures::future::pending;
    use noctium_runtime::field_decimal;
    use transient_crypto::hash::transient_hash;

    let callee = Operation::load(
        "callee",
        "store",
        BTreeMap::from([("stored".into(), json!("1"))]),
    );
    let first = callee.deploy.address();
    let replacement = ContractDeploy::new(&mut OsRng, callee.deploy.initial_state.clone());
    let second = replacement.address();
    assert_ne!(first, second);
    let authority = Fr::from(42u64);
    let config = |route: ContractAddress| {
        BTreeMap::from([
            ("route".into(), bytes32(route.0)),
            (
                "adminCommitment".into(),
                json!(field_decimal(transient_hash(&[authority]))),
            ),
        ])
    };
    let mut caller = Operation::load("caller", "claim", config(first));
    let rotate = Operation::load("rotate", "rotateRoute", config(first));
    let extra = rotate
        .deploy
        .initial_state
        .operations
        .get(&rotate.entry)
        .unwrap();
    let mut state = caller.deploy.initial_state.clone();
    state.operations = state
        .operations
        .insert(rotate.entry.clone(), (*extra).clone());
    caller.deploy = ContractDeploy::new(&mut OsRng, state);
    let caller_address = caller.deploy.address();
    let mut deployments = Vec::new();
    for deployment in [&callee.deploy, &replacement, &caller.deploy] {
        deployments.push(deploy(deployment).await);
    }

    let prove = async |intent, state: &LedgerState<Db>, selected: &[CompositionMaterial<'_>]| {
        let prepared = PreparedComposition::from_intent(intent, state, selected).unwrap();
        let proved = prepared.prove_locally(OsRng, pending()).await.unwrap();
        submit(proved.native()).await
    };
    let mut field_bytes = [0u8; 32];
    field_bytes[0] = 9;
    let callee_inputs = BTreeMap::from([
        ("aux".into(), json!("7")),
        ("flag".into(), json!(true)),
        ("score".into(), json!("200")),
        (
            "payload".into(),
            json!({"kind":"bytes", "values":(0..33).collect::<Vec<u8>>()}),
        ),
        ("empty".into(), json!({"kind":"bytes", "values":[]})),
        ("scalar".into(), json!({"kind":"jubjubScalar", "value":"1"})),
        (
            "point".into(),
            json!({"kind":"jubjubPoint", "x":"0", "y":"1"}),
        ),
        (
            "field".into(),
            json!({"kind":"foreign", "type":"Secp256k1Base", "bytes":field_bytes}),
        ),
    ]);
    let call = |ledger: &LedgerState<Db>,
                ttl,
                target: ContractAddress,
                role: EntryPointBuf,
                opening: u64| {
        let mut inputs = callee_inputs.clone();
        inputs.remove("aux");
        inputs.extend([
            ("opening".into(), json!(opening.to_string())),
            ("emptyAccepted".into(), json!(true)),
            ("expectedTail".into(), json!("32")),
            ("expectedScore".into(), json!("200")),
            ("expectedApproval".into(), json!(true)),
        ]);
        let caller_data = ledger.contract.get(&caller_address).unwrap().data.clone();
        let callee_data = ledger.contract.get(&target).unwrap().data.clone();
        let parent = prepare(
            &caller.plan,
            &inputs,
            &caller_data,
            &ledger.parameters,
            caller_address,
        )
        .unwrap();
        let child = prepare(
            &callee.plan,
            &callee_inputs,
            &callee_data,
            &ledger.parameters,
            target,
        )
        .unwrap();
        assemble_checked_calls(
            &[
                checked_call(
                    &parent,
                    &caller.circuit,
                    caller_data,
                    caller_address,
                    caller.entry.clone(),
                    Fr::from(opening + 1),
                ),
                checked_call(
                    &child,
                    &callee.circuit,
                    callee_data,
                    target,
                    role,
                    Fr::from(opening),
                ),
            ],
            &ledger.parameters,
            ttl,
            &mut OsRng,
        )
    };
    let selected = [caller.proof_selection(), callee.proof_selection()];
    let live = node.sync().unwrap();
    let ttl = live.block.tblock.to_secs() + 1800;
    assert!(
        call(
            &live.state,
            ttl,
            first,
            EntryPointBuf(b"other".to_vec()),
            101
        )
        .is_err()
    );
    let intent = call(&live.state, ttl, first, callee.entry.clone(), 101).unwrap();
    assert!(
        PreparedComposition::from_intent(
            intent.clone(),
            &live.state,
            &[caller.proof_selection(), rotate.proof_selection()]
        )
        .is_err()
    );
    let first_call = prove(intent, &live.state, &selected).await;

    let live = node.sync().unwrap();
    let ttl = live.block.tblock.to_secs() + 1800;
    let data = live
        .state
        .contract
        .get(&caller_address)
        .unwrap()
        .data
        .clone();
    let update = prepare(
        &rotate.plan,
        &BTreeMap::from([
            ("newTarget".into(), bytes32(second.0)),
            ("authority".into(), json!(field_decimal(authority))),
        ]),
        &data,
        &live.state.parameters,
        caller_address,
    )
    .unwrap();
    let intent = assemble_checked_calls(
        &[checked_call(
            &update,
            &rotate.circuit,
            data,
            caller_address,
            rotate.entry.clone(),
            Fr::from(99u64),
        )],
        &live.state.parameters,
        ttl,
        &mut OsRng,
    )
    .unwrap();
    let rotated = prove(intent, &live.state, &[rotate.proof_selection()]).await;
    let live = node.sync().unwrap();
    assert_eq!(
        live.state.contract.get(&caller_address).unwrap().data,
        create_state(&caller.plan, &config(second)).unwrap()
    );
    let ttl = live.block.tblock.to_secs() + 1800;
    assert!(call(&live.state, ttl, first, callee.entry.clone(), 103).is_err());
    let intent = call(&live.state, ttl, second, callee.entry.clone(), 103).unwrap();
    let second_call = prove(intent, &live.state, &selected).await;

    let verify = |receipt: &noctium_runtime::client::FinalizedReceipt, address: ContractAddress| {
        let key = hex::encode(address.0.0);
        assert_eq!(receipt.contract_address, hex::encode(caller_address.0.0));
        assert_eq!(receipt.secondary_states.len(), 1);
        let bytes = &receipt.secondary_states[&key];
        let state =
            serialize::tagged_deserialize::<ContractState<Db>>(&mut bytes.as_slice()).unwrap();
        assert_eq!(
            state.data,
            create_state(
                &callee.plan,
                &BTreeMap::from([("stored".into(), json!("200"))])
            )
            .unwrap()
        );
    };
    verify(&first_call, first);
    verify(&second_call, second);
    assert_eq!(first_call.contract_state, deployments[2].contract_state);
    assert_eq!(second_call.contract_state, rotated.contract_state);
    eprintln!(
        "{}",
        json!({
            "genesis": first_call.chain.genesis, "profile": first_call.chain.profile,
            "deployments": deployments.iter().map(|r| json!({"address":r.contract_address,"height":r.height,"blockHash":r.block_hash,"transactionId":r.transaction_id})).collect::<Vec<_>>(),
            "caller": hex::encode(caller_address.0.0),
            "firstCall": {"callee":hex::encode(first.0.0), "height":first_call.height,"blockHash":first_call.block_hash,"transactionId":first_call.transaction_id,"extrinsicHash":first_call.extrinsic_hash},
            "rotation": {"height":rotated.height,"blockHash":rotated.block_hash,"transactionId":rotated.transaction_id,"extrinsicHash":rotated.extrinsic_hash},
            "secondCall": {"callee":hex::encode(second.0.0),"height":second_call.height,"blockHash":second_call.block_hash,"transactionId":second_call.transaction_id,"extrinsicHash":second_call.extrinsic_hash},
            "rejected": ["wrong selector", "wrong callee bundle", "stale registry route"], "stored": "200"
        })
    );
}
