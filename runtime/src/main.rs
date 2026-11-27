use anyhow::{Context, Result, anyhow, ensure};
use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Db, LEDGER_REVISION, Plan, ZKIR_REVISION, check, environment, parse_private_config, prepare,
};
use noctium_runtime::constructor::deployment_state;
use onchain_runtime::state::ContractState;
use serialize::{tagged_deserialize, tagged_serialize};
use sha2::{Digest, Sha256};
use std::{fs, path::Path};

fn bytes<T: serialize::Serializable + serialize::Tagged>(value: &T) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    tagged_serialize(value, &mut out)?;
    Ok(out)
}
fn load<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T> {
    serde_json::from_slice(&fs::read(path)?).context("invalid runtime JSON input")
}
fn run() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    ensure!(
        args.len() == 1
            || args.len() == 3 && args[1] == "--write-checker-preimage"
            || args.len() == 4 && args[1] == "--check-state" && args[3] == "--expect-rejection",
        "usage: noctium-runtime ARTIFACT_DIRECTORY [--write-checker-preimage PRIVATE_FILE | --check-state STATE.bin --expect-rejection]"
    );
    let directory = Path::new(&args[0]);
    let plan: Plan = load(&directory.join("source-plan.json"))?;
    ensure!(
        noctium_runtime::profile::validate_plan(
            plan.target.as_deref(),
            plan.target_profile.as_ref()
        ),
        "plan target differs from linked native profile"
    );
    let config = parse_private_config(
        &fs::read(directory.join("runtime-config.json"))
            .context("cannot read private configuration")?,
    )?;
    ensure!(
        plan.entrypoint
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_')
            && !plan.entrypoint.is_empty(),
        "unsafe entrypoint name"
    );
    let parameters = tagged_deserialize(fs::read(directory.join("ledger.params"))?.as_slice())
        .context("invalid ledger parameters")?;
    let ir = noctium_runtime::zkir::IrSource::load(fs::File::open(
        directory
            .join("zkir")
            .join(format!("{}.zkir", plan.entrypoint)),
    )?)?;
    let summary: serde_json::Value = load(&directory.join("native-contract.json"))?;
    let address_bytes: [u8; 32] = hex::decode(
        summary["address"]
            .as_str()
            .ok_or_else(|| anyhow!("missing public address"))?,
    )?
    .try_into()
    .map_err(|_| anyhow!("invalid public address"))?;
    let address = ContractAddress(HashOutput(address_bytes));
    if args.len() == 4 {
        // Decode and validate before treating an execution error as rejection.
        environment(&plan, &config.inputs)?;
        let state_bytes = fs::read(&args[2]).context("cannot read supplied state")?;
        let mut reader = state_bytes.as_slice();
        let supplied: ContractState<Db> =
            tagged_deserialize(&mut reader).context("invalid supplied contract state")?;
        ensure!(
            reader.is_empty(),
            "trailing bytes in supplied contract state"
        );
        let unchanged = bytes(&supplied)?;
        let rejected = prepare(&plan, &config.inputs, &supplied.data, &parameters, address)
            .and_then(|execution| check(&execution, &ir))
            .is_err();
        ensure!(
            bytes(&supplied)? == unchanged,
            "state check mutated supplied state"
        );
        ensure!(rejected, "execution accepted supplied state");
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "runtime":"native Rust","nodeInvoked":false,"rejected":true,
                "scope":"execution and official circuit checking against supplied state",
                "stateSha256":hex::encode(Sha256::digest(&state_bytes)),
                "stateUnchangedOnRejection":true
            }))?
        );
        return Ok(());
    }
    let state = deployment_state(&plan, &config.state)?;
    let golden_initial: ContractState<Db> =
        tagged_deserialize(fs::read(directory.join("initial-state.bin"))?.as_slice())?;
    ensure!(
        bytes(&state)? == bytes(&golden_initial.data)?,
        "native initial state differs from qualified fixture"
    );
    let execution = prepare(&plan, &config.inputs, &state, &parameters, address)?;
    let activity = check(&execution, &ir)?;
    let mut predicted: ContractState<Db> =
        tagged_deserialize(fs::read(directory.join("initial-state.bin"))?.as_slice())?;
    predicted.data = execution.after.state.clone();
    let predicted_bytes = bytes(&predicted)?;
    ensure!(
        predicted_bytes == fs::read(directory.join("predicted-state.bin"))?,
        "native predicted state differs from qualified fixture"
    );
    let unchanged = bytes(&state)?;
    let mut negatives = Vec::new();
    ensure!(
        !config.negative_cases.is_empty(),
        "fixture has no negative cases"
    );
    for case in &config.negative_cases {
        let mut inputs = config.inputs.clone();
        inputs.extend(case.inputs.clone());
        let rejected = prepare(&plan, &inputs, &state, &parameters, address)
            .and_then(|e| check(&e, &ir))
            .is_err();
        ensure!(rejected, "negative fixture was accepted");
        ensure!(
            bytes(&state)? == unchanged,
            "rejected fixture changed state"
        );
        negatives.push(serde_json::json!({"name":case.name,"rejected":true}));
    }
    let after_bytes = bytes(&execution.after.state)?;
    ensure!(
        prepare(
            &plan,
            &config.inputs,
            &execution.after.state,
            &parameters,
            address
        )
        .and_then(|execution| check(&execution, &ir))
        .is_err(),
        "native replay was accepted"
    );
    ensure!(
        after_bytes == bytes(&execution.after.state)?,
        "replay changed accepted state"
    );
    if args.len() == 3 {
        use std::io::Write;
        #[cfg(unix)]
        use std::os::unix::fs::OpenOptionsExt;
        let mut options = fs::OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        options.mode(0o600);
        options
            .open(&args[2])?
            .write_all(&bytes(&execution.preimage)?)?;
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&serde_json::json!({
            "runtime":"native Rust","nodeInvoked":false,"ledgerRevision":LEDGER_REVISION,"zkirRevision":ZKIR_REVISION,"zkirRelease":noctium_runtime::profile::RELEASE,"runtimeProfile":noctium_runtime::profile::ABI,
            "scope":"plan evaluation, native state/transcripts, budgeting, checker preimage, official circuit checking; no proof or transaction submission",
            "initialStateMatches":true,"predictedStateMatches":true,"predictedStateSha256":hex::encode(Sha256::digest(&predicted_bytes)),
            "operations":execution.program.len(),"activityGroups":activity.len(),"privateInputCount":execution.preimage.private_transcript.len(),
            "publicTranscriptInputCount":execution.preimage.public_transcript_inputs.len(),"publicTranscriptOutputCount":execution.preimage.public_transcript_outputs.len(),
            "guaranteedOperations":execution.guaranteed.as_ref().map_or(0,|t|t.program.len()),"fallibleOperations":execution.fallible.as_ref().map_or(0,|t|t.program.len()),
            "validCheck":true,"negativeChecks":negatives,"replayRejected":true,"stateUnchangedOnRejection":true
        }))?
    );
    Ok(())
}
fn main() {
    if let Err(error) = run() {
        eprintln!("noctium-runtime: {error:#}");
        std::process::exit(1);
    }
}
