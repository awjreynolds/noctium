#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::{
    coin::{Commitment, Nullifier},
    contract::ContractAddress,
};
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires fresh RawShieldedClaims ZKIR 3.2.1 artifacts"]
fn emitted_raw_claims_match_native_effects() -> anyhow::Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_RAW_SHIELDED_CLAIMS_DIR")?);
    let cases = [
        ("claimNullifier", 6, None, [1, 0, 0]),
        ("claimNullifierTwice", 6, None, [1, 0, 0]),
        ("claimReceive", 7, None, [0, 1, 0]),
        ("claimSpend", 8, None, [0, 0, 1]),
        ("guardedClaimReceive", 7, Some(false), [0, 0, 0]),
        ("guardedClaimReceive", 7, Some(true), [0, 1, 0]),
        ("helperClaimReceive", 7, Some(false), [0, 0, 0]),
        ("helperClaimReceive", 7, Some(true), [0, 1, 0]),
    ];
    for (entry, byte, enabled, counts) in cases {
        let stem = format!("RawShieldedClaims.{entry}");
        let plan: Plan =
            serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
        let circuit = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
        let digest = [byte; 32];
        let mut inputs =
            BTreeMap::from([("digest".into(), json!({"kind": "bytes", "values": digest}))]);
        if let Some(enabled) = enabled {
            inputs.insert("enabled".into(), json!(enabled));
        }
        let state = create_state(&plan, &BTreeMap::new())?;
        let execution = prepare(
            &plan,
            &inputs,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress(HashOutput([4; 32])),
        )?;
        assert_eq!(
            check(&execution, &circuit)?,
            execution.activity_schedule,
            "{entry}"
        );
        let effects = &execution.after.effects;
        let digest = HashOutput(digest);
        assert_eq!(
            [
                effects.claimed_nullifiers.size(),
                effects.claimed_shielded_receives.size(),
                effects.claimed_shielded_spends.size(),
            ],
            counts,
            "{entry}"
        );
        assert_eq!(
            [
                effects.claimed_nullifiers.member(&Nullifier(digest)),
                effects
                    .claimed_shielded_receives
                    .member(&Commitment(digest)),
                effects.claimed_shielded_spends.member(&Commitment(digest)),
            ],
            counts.map(|count| count == 1),
            "{entry}"
        );
    }

    let entry = "guardedHelperClaimSpendNullifier";
    let stem = format!("RawShieldedClaims.{entry}");
    let plan: Plan =
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
    let digest = [0x61; 32];
    let other_digest = [0x62; 32];
    assert_ne!(digest, other_digest);
    for enabled in [false, true] {
        let inputs = BTreeMap::from([
            ("enabled".into(), json!(enabled)),
            ("digest".into(), json!({"kind": "bytes", "values": digest})),
            (
                "otherDigest".into(),
                json!({"kind": "bytes", "values": other_digest}),
            ),
        ]);
        let state = create_state(&plan, &BTreeMap::new())?;
        let execution = prepare(
            &plan,
            &inputs,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            ContractAddress(HashOutput([4; 32])),
        )?;
        assert_eq!(
            check(&execution, &circuit)?,
            execution.activity_schedule,
            "{entry}, enabled={enabled}"
        );
        let effects = &execution.after.effects;
        let count = if enabled { 2 } else { 0 };
        assert_eq!(
            [
                effects.claimed_nullifiers.size(),
                effects.claimed_shielded_receives.size(),
                effects.claimed_shielded_spends.size(),
            ],
            [count, 0, count],
            "{entry}, enabled={enabled}"
        );
        let digest = HashOutput(digest);
        let other_digest = HashOutput(other_digest);
        assert_eq!(
            [
                effects.claimed_nullifiers.member(&Nullifier(digest)),
                effects.claimed_nullifiers.member(&Nullifier(other_digest)),
                effects
                    .claimed_shielded_receives
                    .member(&Commitment(digest)),
                effects
                    .claimed_shielded_receives
                    .member(&Commitment(other_digest)),
                effects.claimed_shielded_spends.member(&Commitment(digest)),
                effects
                    .claimed_shielded_spends
                    .member(&Commitment(other_digest)),
            ],
            [enabled, enabled, false, false, enabled, enabled],
            "{entry}, enabled={enabled}"
        );
    }
    Ok(())
}
