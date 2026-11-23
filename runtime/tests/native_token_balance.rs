#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::{
    coin::{ShieldedTokenType, TokenType, UnshieldedTokenType},
    contract::ContractAddress,
};
use noctium_runtime::{
    Db, Execution, Plan, check, create_state, prepare_with_context, proof::TrustedParameters,
    zkir::IrSource,
};
use onchain_runtime::{context::QueryContext, state::ChargedState};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, env, fs, path::PathBuf};

const BALANCE_HELPERS_K: u8 = 9;
const BALANCE_HELPERS_RELATION_SHA256: &str =
    "e87255cc5e3917eead87106b2e674785d8affea9a5bfd31ff34f5b6f8476ec78";
const OFFICIAL_K9_SRS_SHA256: &str =
    "b9009f1098bcefffec3c461ab3a5e3a17f7e5599f0f08c70fcdc55a89227bcbd";

fn balance_helper_color() -> HashOutput {
    HashOutput(std::array::from_fn(|index| (index + 1) as u8))
}

fn balance_helper_execution(
    plan: &Plan,
    state: &ChargedState<Db>,
    amount: Option<u128>,
    limit: u128,
    enabled: bool,
) -> anyhow::Result<Execution> {
    let color = balance_helper_color();
    let mut context = QueryContext::new(state.clone(), ContractAddress::default());
    let mut balances = context
        .call_context
        .balance
        .insert(TokenType::Shielded(ShieldedTokenType(color)), 11);
    if let Some(amount) = amount {
        balances = balances.insert(TokenType::Unshielded(UnshieldedTokenType(color)), amount);
    }
    context.call_context.balance = balances;
    let inputs = BTreeMap::from([
        ("color".into(), json!({"kind":"bytes", "values":color.0})),
        ("limit".into(), json!(limit.to_string())),
        ("enabled".into(), json!(enabled)),
    ]);
    Ok(prepare_with_context(
        plan,
        &inputs,
        context,
        &ledger::structure::INITIAL_PARAMETERS,
    )?)
}

fn assert_balance_helper_outputs(
    execution: &Execution,
    amount: u128,
    expected: [bool; 4],
) {
    let returns = execution.returns_json();
    assert_eq!(returns["exactAmount"], json!(amount.to_string()));
    for (name, expected) in ["belowLimit", "atLeastLimit", "aboveLimit", "atMostLimit"]
        .into_iter()
        .zip(expected)
    {
        assert_eq!(returns[name], json!(expected), "{name}");
    }
}

#[test]
#[ignore = "requires generated NativeTokenBalance artifacts in NOCTIUM_BALANCE_DIR"]
fn tagged_token_balance_reads_bind_to_the_selected_ledger_namespace() -> anyhow::Result<()> {
    let directory =
        PathBuf::from(std::env::var_os("NOCTIUM_BALANCE_DIR").expect("NOCTIUM_BALANCE_DIR"));
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join("NativeTokenBalance.inspect.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("NativeTokenBalance.inspect.zkir"),
    )?)?;
    let initial = create_state(&plan, &BTreeMap::from([("recorded".into(), json!("17"))]))?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let color = HashOutput(std::array::from_fn(|index| (index + 1) as u8));
    let context = |unshielded: Option<u128>, shielded: Option<u128>| {
        let mut context = QueryContext::new(initial.clone(), ContractAddress::default());
        let balances = &mut context.call_context.balance;
        if let Some(amount) = unshielded {
            *balances = balances.insert(TokenType::Unshielded(UnshieldedTokenType(color)), amount);
        }
        if let Some(amount) = shielded {
            *balances = balances.insert(TokenType::Shielded(ShieldedTokenType(color)), amount);
        }
        context
    };
    let prepare = |is_unshielded, limit: u128, enabled, read_exact, unshielded, shielded| {
        let inputs = BTreeMap::from([
            ("color".into(), json!({"kind":"bytes", "values":color.0})),
            ("isUnshielded".into(), json!(is_unshielded)),
            ("limit".into(), json!(limit.to_string())),
            ("enabled".into(), json!(enabled)),
            ("readExact".into(), json!(read_exact)),
        ]);
        prepare_with_context(&plan, &inputs, context(unshielded, shielded), params)
    };
    let execute = |is_unshielded, limit, enabled, read_exact, unshielded, shielded| {
        let execution = prepare(
            is_unshielded,
            limit,
            enabled,
            read_exact,
            unshielded,
            shielded,
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        Ok::<_, anyhow::Error>(execution)
    };

    for (tag, expected, below, above) in [(true, 17u128, true, false), (false, 23u128, false, true)]
    {
        let execution = execute(tag, 20, true, true, Some(17), Some(23))?;
        let returns = execution.returns_json();
        assert_eq!(returns["exactAmount"], json!(expected.to_string()));
        assert_eq!(returns["belowLimit"], json!(below));
        assert_eq!(returns["aboveLimit"], json!(above));
        let expected_state = create_state(
            &plan,
            &BTreeMap::from([("recorded".into(), json!(expected.to_string()))]),
        )?;
        assert_eq!(execution.after.state, expected_state);
    }

    let absent = execute(true, 20, true, true, None, Some(23))?;
    assert_eq!(absent.returns_json()["exactAmount"], json!("0"));
    assert_eq!(absent.returns_json()["belowLimit"], json!(true));
    assert_eq!(absent.returns_json()["aboveLimit"], json!(false));

    let wide_exact = execute(false, u128::MAX, false, true, None, Some(u128::MAX))?;
    assert_eq!(
        wide_exact.returns_json()["exactAmount"],
        json!(u128::MAX.to_string())
    );
    assert!(prepare(false, 0, true, false, None, Some(u128::MAX)).is_err());
    assert!(prepare(false, u128::MAX, true, false, None, Some(0)).is_err());

    let inactive = execute(true, 20, false, false, Some(17), Some(23))?;
    assert_eq!(inactive.returns_json()["exactAmount"], json!("0"));
    assert_eq!(inactive.returns_json()["belowLimit"], json!(false));
    assert_eq!(inactive.returns_json()["aboveLimit"], json!(false));

    let predicate_only = execute(true, 10, true, false, Some(8), Some(23))?;
    let cost = &params.cost_model.runtime_cost_model;
    assert!(
        context(Some(9), Some(23))
            .query(&predicate_only.program, None, cost)
            .is_ok()
    );
    assert!(
        context(Some(10), Some(23))
            .query(&predicate_only.program, None, cost)
            .is_err()
    );
    Ok(())
}

#[test]
#[ignore = "requires fresh UnshieldedBalanceHelpers artifacts in NOCTIUM_BALANCE_HELPERS_DIR"]
fn unshielded_balance_helpers_match_compact() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_BALANCE_HELPERS_DIR").expect("NOCTIUM_BALANCE_HELPERS_DIR"),
    );
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join("UnshieldedBalanceHelpers.inspect.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("UnshieldedBalanceHelpers.inspect.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let prepare = |amount: Option<u128>, limit: u128, enabled| {
        balance_helper_execution(&plan, &state, amount, limit, enabled)
    };
    for (amount, limit, enabled, expected) in [
        (Some(17), 20, true, [true, false, false, true]),
        (Some(20), 20, true, [false, true, false, true]),
        (Some(23), 20, true, [false, true, true, false]),
        (None, 20, true, [true, false, false, true]),
        (Some(u128::MAX), u128::MAX, false, [false; 4]),
        (
            Some(u64::MAX as u128),
            u64::MAX as u128,
            true,
            [false, true, false, true],
        ),
    ] {
        let execution = prepare(amount, limit, enabled)?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_balance_helper_outputs(&execution, amount.unwrap_or(0), expected);
    }
    assert!(prepare(Some(u128::MAX), 20, true).is_err());
    assert!(prepare(Some(8), u128::MAX, true).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh UnshieldedBalanceHelpers artifacts in NOCTIUM_BALANCE_HELPERS_DIR and the official k9 SRS in NOCTIUM_BALANCE_HELPERS_PROOF_PARAMETERS"]
fn unshielded_balance_helpers_generate_and_bind_native_proof() -> anyhow::Result<()> {
    use futures::executor::block_on;
    use rand::rngs::OsRng;
    use transient_crypto::{
        curve::Fr,
        proofs::{ParamsVerifier, Zkir},
    };

    let directory = PathBuf::from(
        env::var_os("NOCTIUM_BALANCE_HELPERS_DIR").expect("NOCTIUM_BALANCE_HELPERS_DIR"),
    );
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join("UnshieldedBalanceHelpers.inspect.impact.json"),
    )?)?;
    let relation_bytes = fs::read(directory.join("UnshieldedBalanceHelpers.inspect.zkir"))?;
    assert_eq!(
        hex::encode(Sha256::digest(&relation_bytes)),
        BALANCE_HELPERS_RELATION_SHA256
    );
    let relation = IrSource::load(relation_bytes.as_slice())?;
    assert_eq!(relation.k(), BALANCE_HELPERS_K);
    let parameter_bytes = fs::read(
        env::var_os("NOCTIUM_BALANCE_HELPERS_PROOF_PARAMETERS")
            .expect("NOCTIUM_BALANCE_HELPERS_PROOF_PARAMETERS"),
    )?;
    let parameters = TrustedParameters::from_bytes(
        &parameter_bytes,
        BALANCE_HELPERS_K,
        OFFICIAL_K9_SRS_SHA256,
    )?;
    assert_eq!(parameters.sha256(), OFFICIAL_K9_SRS_SHA256);
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execution = balance_helper_execution(&plan, &state, Some(17), 20, true)?;

    assert_eq!(check(&execution, &relation)?, execution.activity_schedule);
    assert_balance_helper_outputs(&execution, 17, [true, false, false, true]);

    let (prover_key, verifier_key) = block_on(relation.keygen(&parameters))?;
    let (proof, statement, activity) = block_on(relation.prove(
        OsRng,
        &parameters,
        prover_key,
        &execution.preimage,
    ))?;
    assert_eq!(activity, execution.activity_schedule);
    verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;

    let (commitment, _) = execution
        .preimage
        .communications_commitment
        .expect("helper outputs are bound by the communication commitment");
    assert_eq!(statement.get(1), Some(&commitment));
    let mut changed_statement = statement;
    changed_statement[1] = commitment + Fr::from(1u64);
    assert!(verifier_key
        .verify(
            &verifier_parameters,
            &proof,
            changed_statement.iter().copied(),
        )
        .is_err());

    println!(
        "Unshielded balance helper proof passed: k={}, relation_sha256={}, srs_sha256={}, proof_bytes={}, five_outputs=checked, changed_communication_commitment=rejected",
        BALANCE_HELPERS_K,
        BALANCE_HELPERS_RELATION_SHA256,
        parameters.sha256(),
        proof.0.len(),
    );
    Ok(())
}
