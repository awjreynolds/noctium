#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh BooleanParity artifacts in NOCTIUM_BOOLEAN_PARITY_DIR"]
fn pinned_boolean_values_operators_and_casts_match_native() -> Result<()> {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_BOOLEAN_PARITY_DIR").expect("NOCTIUM_BOOLEAN_PARITY_DIR"),
    );
    let artifact = |entry: &str| -> Result<(Plan, IrSource)> {
        let base = format!("BooleanParity.{entry}");
        Ok((
            serde_json::from_reader(File::open(directory.join(format!("{base}.impact.json")))?)?,
            IrSource::load(File::open(directory.join(format!("{base}.zkir")))?)?,
        ))
    };

    let (table_plan, table) = artifact("truthTable")?;
    let table_state = create_state(&table_plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = ContractAddress::default();
    for left in [false, true] {
        for right in [false, true] {
            let execution = prepare(
                &table_plan,
                &BTreeMap::from([("left".into(), json!(left)), ("right".into(), json!(right))]),
                &table_state,
                parameters,
                address,
            )?;
            check(&execution, &table)?;
            assert_eq!(
                execution.returns_json(),
                BTreeMap::from([
                    ("alwaysFalse".into(), json!(false)),
                    ("alwaysTrue".into(), json!(true)),
                    ("notResult".into(), json!(!left)),
                    ("andResult".into(), json!(left && right)),
                    ("orResult".into(), json!(left || right)),
                    ("equalResult".into(), json!(left == right)),
                    ("differentResult".into(), json!(left != right)),
                ])
            );
            let mut forged = execution;
            forged.preimage.public_transcript_outputs[0] = Fr::from(2u64);
            assert!(
                check(&forged, &table).is_err(),
                "Boolean field must be zero or one"
            );
        }
    }
    assert!(
        prepare(
            &table_plan,
            &BTreeMap::from([("left".into(), json!(1)), ("right".into(), json!(false))]),
            &table_state,
            parameters,
            address,
        )
        .is_err()
    );

    let (convert_plan, convert) = artifact("convert")?;
    let convert_state = create_state(&convert_plan, &BTreeMap::new())?;
    let max_field = "52435875175126190479447740508185965837690552500527637822603658699938581184512";
    for flag in [false, true] {
        for field in ["0", max_field] {
            let amount = if flag { "255" } else { "0" };
            let bit = if flag { "1" } else { "0" };
            let execution = prepare(
                &convert_plan,
                &BTreeMap::from([
                    ("flag".into(), json!(flag)),
                    ("field".into(), json!(field)),
                    ("amount".into(), json!(amount)),
                ]),
                &convert_state,
                parameters,
                address,
            )?;
            check(&execution, &convert)?;
            assert_eq!(
                execution.returns_json(),
                BTreeMap::from([
                    ("asField".into(), json!(bit)),
                    ("asBit".into(), json!(bit)),
                    ("fromField".into(), json!(field != "0")),
                    ("fromAmount".into(), json!(amount != "0")),
                    ("defaultBool".into(), json!(false)),
                ])
            );
        }
    }

    let (narrow_plan, narrow) = artifact("narrow")?;
    let narrow_state = create_state(&narrow_plan, &BTreeMap::new())?;
    let narrow_flag = |flag: Json| {
        prepare(
            &narrow_plan,
            &BTreeMap::from([("flag".into(), flag)]),
            &narrow_state,
            parameters,
            address,
        )
    };
    let zero = narrow_flag(json!(false))?;
    check(&zero, &narrow)?;
    assert_eq!(zero.returns_json()["zero"], "0");
    assert!(narrow_flag(json!(true)).is_err());
    let mut forged = zero;
    forged.preimage.public_transcript_outputs[0] = Fr::from(1u64);
    assert!(check(&forged, &narrow).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh Boolean artifacts and official K6/K7 parameters"]
fn boolean_relations_generate_and_bind_native_proofs() -> Result<()> {
    use futures::executor::block_on;
    use noctium_runtime::proof::TrustedParameters;
    use rand::rngs::OsRng;
    use std::fs;
    use transient_crypto::proofs::{ParamsVerifier, Zkir};

    let artifacts = PathBuf::from(
        env::var_os("NOCTIUM_BOOLEAN_PARITY_DIR").expect("NOCTIUM_BOOLEAN_PARITY_DIR"),
    );
    let srs = PathBuf::from(
        env::var_os("NOCTIUM_BOOLEAN_PROOF_PARAMETERS_DIR")
            .expect("NOCTIUM_BOOLEAN_PROOF_PARAMETERS_DIR"),
    );
    for (entry, inputs, k) in [
        (
            "BooleanParity.truthTable",
            json!({"left": true, "right": false}),
            7,
        ),
        (
            "BooleanParity.convert",
            json!({"flag": true, "field": "0", "amount": "255"}),
            7,
        ),
        ("BooleanParity.narrow", json!({"flag": false}), 6),
        (
            "LazyBoolean.lazy",
            json!({"andEnabled": false, "orEnabled": true,
            "nestedOuter": true, "nestedInner": true, "amount": "2"}),
            7,
        ),
    ] {
        let relation = IrSource::load(File::open(artifacts.join(format!("{entry}.zkir")))?)?;
        assert_eq!(relation.k(), k, "{entry}");
        let plan: Plan =
            serde_json::from_reader(File::open(artifacts.join(format!("{entry}.impact.json")))?)?;
        let execution = prepare(
            &plan,
            &serde_json::from_value(inputs)?,
            &create_state(&plan, &BTreeMap::new())?,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress::default(),
        )?;
        let srs_hash = if k == 6 {
            "cf2ad6be7d0fedf5bec2aaa35f6be4aca33053d74268fdf5aa54fcb2891ea6df"
        } else {
            "e82ae890c080188355f37feaffe91372584cd810615082d9143d4dec0453fd9d"
        };
        let bytes = fs::read(srs.join(format!("bls_midnight_2p{k}")))?;
        let parameters = TrustedParameters::from_bytes(&bytes, k, srs_hash)?;
        let verifier_parameters = ParamsVerifier::read(bytes.as_slice())?;
        let (prover_key, verifier_key) = block_on(relation.keygen(&parameters))?;
        let (proof, mut statement, activity) =
            block_on(relation.prove(OsRng, &parameters, prover_key, &execution.preimage))?;
        assert_eq!(activity, execution.activity_schedule);
        let (commitment, _) = execution.preimage.communications_commitment.unwrap();
        assert_eq!(statement.get(1), Some(&commitment), "{entry}");
        verifier_key.verify(&verifier_parameters, &proof, statement.iter().copied())?;
        statement[1] = commitment + Fr::from(1u64);
        assert!(
            verifier_key
                .verify(&verifier_parameters, &proof, statement.iter().copied())
                .is_err(),
            "{entry} proof must bind the original commitment"
        );
    }
    Ok(())
}
