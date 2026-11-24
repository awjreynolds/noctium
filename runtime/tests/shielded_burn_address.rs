#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Plan, check, create_state, prepare, proof::TrustedParameters, zkir::IrSource,
};
use rand::rngs::OsRng;
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use transient_crypto::proofs::{ParamsVerifier, Zkir};

const BURN_RELATION_K: u8 = 8;
const BURN_RELATION_SHA256: &str =
    "5a57137147fe937b2b125c81994efe2d275f97dd8616a9a10fc0f3bb09d309c1";
const OFFICIAL_K8_SRS_SHA256: &str =
    "909b707551eaaea79828e883cde6fc46ab15986c3b1d791bed462c9e2805c933";

#[test]
#[ignore = "requires fresh ShieldedBurnAddress.lean outputs"]
fn burn_returns_both_typed_address_arms_without_ledger_effects() -> anyhow::Result<()> {
    let directory =
        PathBuf::from(env::var_os("NOCTIUM_BURN_ADDRESS_DIR").expect("set artifact directory"));
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("ShieldedBurnAddressReturnFixture.burn.impact.json"),
    )?)?;
    let relation_bytes = fs::read(directory.join("ShieldedBurnAddressReturnFixture.burn.zkir"))?;
    assert_eq!(
        hex::encode(Sha256::digest(&relation_bytes)),
        BURN_RELATION_SHA256
    );
    let circuit = IrSource::load(relation_bytes.as_slice())?;
    assert_eq!(circuit.k(), BURN_RELATION_K);
    let state = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &BTreeMap::new(),
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )?;
    check(&execution, &circuit)?;
    let address = |id: &str| {
        json!({"kind":"struct","id":id,"fields":[
            {"name":"bytes","value":{"kind":"bytes","values":vec![0u8; 32]}}
        ]})
    };
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([(
            "result".into(),
            json!({
                "kind":"struct",
                "id":"Noctium.Midnight.ShieldedBurnAddressResult",
                "fields":[
                    {"name":"is_left","value":{"kind":"bool","value":true}},
                    {"name":"left","value":address("Noctium.Midnight.ZswapCoinPublicKey")},
                    {"name":"right","value":address("Noctium.Midnight.ContractAddress")}
                ]
            })
        )]),
    );
    assert_eq!(execution.after.state, state);
    assert!(execution.guaranteed.is_none() && execution.fallible.is_none());

    let parameter_path = env::var_os("NOCTIUM_BURN_ADDRESS_PROOF_PARAMETERS")
        .expect("set NOCTIUM_BURN_ADDRESS_PROOF_PARAMETERS to the pinned official k8 SRS");
    let parameter_bytes = fs::read(parameter_path)?;
    let parameters =
        TrustedParameters::from_bytes(&parameter_bytes, BURN_RELATION_K, OFFICIAL_K8_SRS_SHA256)?;
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())?;
    let (prover_key, verifier_key) = futures::executor::block_on(circuit.keygen(&parameters))?;
    let (proof, statement, activity) = futures::executor::block_on(circuit.prove(
        OsRng,
        &parameters,
        prover_key,
        &execution.preimage,
    ))?;
    assert_eq!(activity, execution.activity_schedule);
    verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;
    let (return_commitment, _) = execution
        .preimage
        .communications_commitment
        .expect("the logical return is bound by the communication commitment");
    assert_eq!(statement.get(1), Some(&return_commitment));
    let mut changed_return_commitment = statement;
    changed_return_commitment[1] = return_commitment + transient_crypto::curve::Fr::from(1u64);
    assert!(
        verifier_key
            .verify(
                &verifier_parameters,
                &proof,
                changed_return_commitment.iter().copied(),
            )
            .is_err()
    );
    Ok(())
}
