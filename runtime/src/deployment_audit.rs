//! Selected PrivateClaim deployment identity qualification. The public controller must
//! first replay the independently pinned issue56 authority through its trusted checker.
use crate::{
    Db, Plan,
    artifacts::{Role, VerifiedBundle},
    client::{
        ContractEvent, FinalizedReceipt, NetworkPolicy, PublicTransactionReference, Snapshot,
    },
    localnet::Node,
    proof::TrustedParameters,
};
use anyhow::{Result, anyhow, ensure};
use ledger::structure::{ContractAction, PedersenDowngradeable, ProofVersioned, Transaction};
use onchain_runtime::state::{ContractOperation, ContractState};
use serde::{Deserialize, Serialize};
use serde_json::{Value as Json, json};
use serialize::{Deserializable, Serializable, Tagged, tagged_deserialize, tagged_serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use transient_crypto::proofs::Zkir;

pub const GUARANTEE: &str = "PrivateClaimDeploymentIdentity/v1";
pub const SOURCE_POLICY: &str = "Noctium.PrivateClaimVerification.policy";
pub const NATIVE_POLICY: &str = "Noctium.PrivateClaimNativePrivacy.policy";
pub fn hash(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}
pub fn encode<T: Serializable + Tagged>(value: &T) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    tagged_serialize(value, &mut out)?;
    Ok(out)
}
pub fn decode<T: Deserializable + Tagged>(bytes: &[u8]) -> Result<T> {
    Ok(tagged_deserialize(bytes)?)
}
fn pin(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Specification {
    pub schema_version: u32,
    pub guarantee_version: String,
    pub authority_sha256: String,
    pub source_commit: String,
    pub source_tree: String,
    pub entrypoint: String,
    pub initialization: BTreeMap<String, Json>,
    pub policy: NetworkPolicy,
    pub ledger_parameters_sha256: String,
    pub ledger_parameters_block_hash: String,
    pub ledger_parameters_height: u64,
    pub ledger_price_policy: String,
    pub srs_sha256: String,
    pub native_toolchain_sha256: String,
    pub runtime_code_hash: String,
    pub metadata_sha256: String,
}
impl Specification {
    pub fn validate(&self) -> Result<()> {
        ensure!(
            self.schema_version == 1 && self.guarantee_version == GUARANTEE,
            "unsupported_deployment_guarantee"
        );
        ensure!(
            crate::profile::NAME == "midnight-ledger-9-zkir-3.2.1" && self.entrypoint == "claim",
            "wrong_deployment_target"
        );
        self.policy.validate()?;
        ensure!(
            pin(&self.ledger_parameters_block_hash)
                && self.ledger_price_policy == "adaptive-fee-prices-v1",
            "invalid_parameter_reference_policy"
        );
        for x in [
            &self.authority_sha256,
            &self.ledger_parameters_sha256,
            &self.srs_sha256,
            &self.native_toolchain_sha256,
            &self.runtime_code_hash,
            &self.metadata_sha256,
        ] {
            ensure!(pin(x), "invalid_deployment_pin");
        }
        for x in [&self.source_commit, &self.source_tree] {
            ensure!(
                x.len() == 40
                    && x.bytes()
                        .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)),
                "invalid_source_revision"
            );
        }
        ensure!(
            self.initialization.len() == 3
                && self.initialization.contains_key("acceptedRoot")
                && self.initialization.contains_key("campaignId")
                && self.initialization.get("spent") == Some(&json!([])),
            "invalid_public_initialization"
        );
        Ok(())
    }
}
pub struct QualifiedMaterial<'a> {
    pub bundle: &'a VerifiedBundle,
    pub plan: Plan,
    pub parameters: TrustedParameters,
    initial: ContractState<Db>,
    verifier_parameters: transient_crypto::proofs::ParamsVerifier,
    ledger_parameters: ledger::structure::LedgerParameters,
    pub identity: Json,
}
impl QualifiedMaterial<'_> {
    pub fn initial_bytes(&self) -> Result<Vec<u8>> {
        encode(&self.initial)
    }
    pub fn check_parameter_reference(&self, spec: &Specification, node: &Node) -> Result<()> {
        let bytes = node.finalized_ledger_parameters_at(
            &spec.ledger_parameters_block_hash,
            spec.ledger_parameters_height,
        )?;
        ensure!(
            bytes == encode(&self.ledger_parameters)?
                && hash(&bytes) == spec.ledger_parameters_sha256,
            "historical_ledger_parameter_mismatch"
        );
        Ok(())
    }
    pub fn check_live(
        &self,
        spec: &Specification,
        snapshot: &Snapshot,
        fingerprint: (String, String),
    ) -> Result<FundingQuote> {
        spec.policy.check(&snapshot.chain)?;
        ensure!(
            fingerprint == (spec.runtime_code_hash.clone(), spec.metadata_sha256.clone()),
            "runtime_identity_mismatch"
        );
        let actual = &*snapshot.state.parameters;
        check_non_price_parameters(&self.ledger_parameters, actual)?;
        Ok(FundingQuote {
            block_hash: snapshot.finalized_hash.clone(),
            height: snapshot.height,
            ledger_parameters_hex: hex::encode(encode(actual)?),
            ledger_parameters_sha256: hash(&encode(actual)?),
        })
    }
    pub fn check_initial(&self, bytes: &[u8]) -> Result<()> {
        check_initial_state(&self.initial, bytes)
    }
    pub fn check_revision(&self, bytes: &[u8]) -> Result<()> {
        check_operation_revision(&self.initial, bytes)
    }
}
fn check_non_price_parameters(
    expected: &ledger::structure::LedgerParameters,
    actual: &ledger::structure::LedgerParameters,
) -> Result<()> {
    let mut allowed = expected.clone();
    allowed.fee_prices = actual.fee_prices.clone();
    ensure!(
        encode(&allowed)? == encode(actual)?,
        "non_price_ledger_parameters_changed"
    );
    Ok(())
}

fn check_initial_state(expected: &ContractState<Db>, bytes: &[u8]) -> Result<()> {
    ensure!(
        bytes == encode(expected)?,
        "initial_contract_state_mismatch"
    );
    Ok(())
}
fn check_operation_revision(expected: &ContractState<Db>, bytes: &[u8]) -> Result<()> {
    let observed: ContractState<Db> = decode(bytes)?;
    ensure!(encode(&observed)? == bytes, "noncanonical_contract_state");
    ensure!(
        observed.operations == expected.operations
            && observed.maintenance_authority == expected.maintenance_authority,
        "deployed_operation_revision_changed"
    );
    Ok(())
}

/// Independently regenerate both keys from the audited CALL bytes and pinned SRS.
/// The CLI producer's output is compared, never treated as corresponding merely
/// because a manifest happens to list a circuit hash and key hashes together.
pub async fn qualify<'a>(
    spec: &Specification,
    authority_bytes: &[u8],
    bundle: &'a VerifiedBundle,
    srs: &[u8],
    native_toolchain: &[u8],
) -> Result<QualifiedMaterial<'a>> {
    spec.validate()?;
    ensure!(
        hash(authority_bytes) == spec.authority_sha256,
        "external_authority_mismatch"
    );
    ensure!(
        hash(native_toolchain) == spec.native_toolchain_sha256,
        "native_toolchain_pin_mismatch"
    );
    let authority: Json = serde_json::from_slice(authority_bytes)?;
    let build = &authority["build"];
    ensure!(
        authority["schemaVersion"] == 1 && authority["compiledContractVerified"] == false,
        "unsupported_source_authority"
    );
    ensure!(
        build["sourceCommit"] == spec.source_commit
            && build["sourceTree"] == spec.source_tree
            && build["sourcePolicy"] == SOURCE_POLICY
            && build["nativePolicy"] == NATIVE_POLICY,
        "audited_source_identity_mismatch"
    );
    ensure!(
        bundle.authenticated_manifest_sha256().is_some()
            && bundle.manifest().compiler.source_revision == spec.source_commit,
        "bundle_source_revision_mismatch"
    );
    for (role, name) in [
        (Role::Circuit, "PrivateClaim.claim.zkir"),
        (Role::Plan, "PrivateClaim.claim.impact.json"),
        (Role::Profile, "target-profile.json"),
        (Role::Metadata, "noctium.json"),
    ] {
        ensure!(
            authority["record"]["artifacts"][name].as_str()
                == Some(hash(bundle.file(role)?).as_str()),
            "audited_artifact_bytes_mismatch"
        );
    }
    ensure!(
        authority["record"]["source"]["files"]["examples/PrivateClaim.lean"].as_str()
            == Some(hash(bundle.source("examples/PrivateClaim.lean")?).as_str()),
        "audited_source_bytes_mismatch"
    );
    let native: Json = serde_json::from_slice(native_toolchain)?;
    let retained: Json = serde_json::from_slice(bundle.file(Role::Toolchain)?)?;
    for key in [
        "repository",
        "revision",
        "rust",
        "host",
        "version",
        "binarySha256",
        "cargoLockSha256",
        "command",
        "requestedVersion",
        "releaseLabel",
        "expectedCliVersion",
    ] {
        ensure!(
            native[key] == retained[key],
            "native_toolchain_association_mismatch"
        );
    }
    ensure!(
        native["revision"] == crate::profile::REVISION,
        "native_source_revision_mismatch"
    );
    ensure!(
        hash(bundle.file(Role::LedgerParameters)?) == spec.ledger_parameters_sha256,
        "ledger_parameter_pin_mismatch"
    );
    let ledger_parameters: ledger::structure::LedgerParameters =
        decode(bundle.file(Role::LedgerParameters)?)?;
    ensure!(
        encode(&ledger_parameters)? == bundle.file(Role::LedgerParameters)?,
        "noncanonical_ledger_parameters"
    );
    let plan_json: Json = serde_json::from_slice(bundle.file(Role::Plan)?)?;
    ensure!(
        plan_json["contractName"] == "PrivateClaim" && plan_json["entrypoint"] == spec.entrypoint,
        "entrypoint_mismatch"
    );
    let circuit = crate::zkir::IrSource::load(bundle.file(Role::Circuit)?)?;
    let parameters = TrustedParameters::from_bytes(srs, circuit.k(), &spec.srs_sha256)?;
    let (pk, vk) = circuit.keygen(&parameters).await?;
    ensure!(
        encode(&pk)? == bundle.file(Role::ProverKey)?
            && encode(&vk)? == bundle.file(Role::VerifierKey)?,
        "independent_native_keygen_mismatch"
    );
    let plan: Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
    let mut initial = ContractState::<Db>::default();
    initial.data = crate::create_state(&plan, &spec.initialization)?;
    initial.operations = initial.operations.insert(
        onchain_runtime::state::EntryPointBuf(spec.entrypoint.as_bytes().to_vec()),
        ContractOperation::new(Some(vk), None),
    );
    let identity = json!({"guaranteeVersion":GUARANTEE,"externalAuthoritySha256":spec.authority_sha256,"build":build,"sourceRecord":authority["record"],"certificateSha256":authority["certificateSha256"],"sourcePolicy":SOURCE_POLICY,"nativePolicy":NATIVE_POLICY,"profile":crate::profile::target_json(),"nativeSourceRevision":crate::profile::REVISION,"ledgerRevision":crate::LEDGER_REVISION,"manifestSha256":bundle.authenticated_manifest_sha256(),"callCircuitSha256":hash(bundle.file(Role::Circuit)?),"planSha256":hash(bundle.file(Role::Plan)?),"proverKeySha256":hash(bundle.file(Role::ProverKey)?),"verifierKeySha256":hash(bundle.file(Role::VerifierKey)?),"ledgerParametersSha256":spec.ledger_parameters_sha256,"ledgerParametersBlockHash":spec.ledger_parameters_block_hash,"ledgerParametersHeight":spec.ledger_parameters_height,"ledgerPricePolicy":spec.ledger_price_policy,"srsSha256":spec.srs_sha256,"nativeToolchain":native,"independentRustKeyRegenerationMatched":true,"initialContractStateSha256":hash(&encode(&initial)?),"businessSpecificationReviewed":false,"universalCompilerVerified":false});
    Ok(QualifiedMaterial {
        bundle,
        plan,
        parameters,
        initial,
        ledger_parameters,
        verifier_parameters: transient_crypto::proofs::ParamsVerifier::read(srs)?,
        identity,
    })
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct FundingQuote {
    pub block_hash: String,
    pub height: u64,
    pub ledger_parameters_hex: String,
    pub ledger_parameters_sha256: String,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ObservedTransaction {
    pub native_transaction_hex: String,
    pub after_height: u64,
    pub funding_quote: FundingQuote,
    pub receipt: FinalizedReceipt,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct DeploymentRecord {
    pub schema_version: u32,
    pub guarantee_version: String,
    pub specification_sha256: String,
    pub material_identity: Json,
    pub address: String,
    pub deployment: ObservedTransaction,
    pub call: ObservedTransaction,
}
fn receipt_identity(expected: &FinalizedReceipt, actual: &FinalizedReceipt) -> Result<()> {
    ensure!(
        expected.chain == actual.chain
            && expected.block_hash == actual.block_hash
            && expected.height == actual.height
            && expected.extrinsic_hash == actual.extrinsic_hash
            && expected.extrinsic_index == actual.extrinsic_index
            && expected.transaction_id == actual.transaction_id
            && expected.intent_id == actual.intent_id
            && expected.contract_address == actual.contract_address
            && expected.event == actual.event
            && expected.contract_state == actual.contract_state,
        "finalized_reference_mismatch"
    );
    Ok(())
}
/// Public proof/deployment verification. No seed, witness configuration or private journal.
pub fn observe_record(
    spec: &Specification,
    specification_bytes: &[u8],
    material: &QualifiedMaterial<'_>,
    record: &DeploymentRecord,
    expected_address: &str,
    node: &Node,
) -> Result<Json> {
    ensure!(
        record.schema_version == 1
            && record.guarantee_version == GUARANTEE
            && record.specification_sha256 == hash(specification_bytes)
            && record.material_identity == material.identity,
        "deployment_record_identity_mismatch"
    );
    ensure!(
        record.address == expected_address,
        "expected_address_mismatch"
    );
    material.check_initial(&record.deployment.receipt.contract_state)?;
    let mut observations = Vec::new();
    for (item, event) in [
        (&record.deployment, ContractEvent::Deploy),
        (&record.call, ContractEvent::Call),
    ] {
        ensure!(
            item.native_transaction_hex.len() <= 8 * 1024 * 1024,
            "public_transaction_limit"
        );
        let bytes = hex::decode(&item.native_transaction_hex)?;
        ensure!(
            item.funding_quote.height == item.after_height,
            "funding_quote_reference_mismatch"
        );
        let quoted = hex::decode(&item.funding_quote.ledger_parameters_hex)?;
        ensure!(
            hash(&quoted) == item.funding_quote.ledger_parameters_sha256,
            "funding_quote_hash_mismatch"
        );
        ensure!(
            node.finalized_ledger_parameters_at(
                &item.funding_quote.block_hash,
                item.funding_quote.height
            )? == quoted,
            "funding_quote_history_mismatch"
        );
        let actual: ledger::structure::LedgerParameters = decode(&quoted)?;
        check_non_price_parameters(&material.ledger_parameters, &actual)?;
        let reference = PublicTransactionReference::from_bytes(
            spec.policy.clone(),
            &bytes,
            item.after_height,
            &item.receipt.contract_state,
        )?;
        ensure!(
            reference.contract_address() == expected_address && reference.event() == event,
            "native_action_identity_mismatch"
        );
        reference.check_receipt(&item.receipt)?;
        let native: crate::funding::SealedTransaction = decode(&bytes)?;
        if let Transaction::Standard(stx) = native {
            let intent = stx
                .intents
                .get(&crate::funding::CONTRACT_SEGMENT)
                .ok_or_else(|| anyhow!("missing_contract_intent"))?;
            if let Some(ContractAction::Call(call)) = intent.actions.iter_deref().next() {
                ensure!(
                    call.entry_point.0 == spec.entrypoint.as_bytes(),
                    "observed_entrypoint_mismatch"
                );
                let ProofVersioned::V3(proof) = &call.proof else {
                    return Err(anyhow!("observed_proof_version_mismatch"));
                };
                let operation = material
                    .initial
                    .operations
                    .get(&onchain_runtime::state::EntryPointBuf(
                        spec.entrypoint.as_bytes().to_vec(),
                    ))
                    .ok_or_else(|| anyhow!("missing_expected_operation"))?;
                operation.v3_vk().ok_or_else(||anyhow!("missing_expected_verifier"))?.verify(&material.verifier_parameters,proof,call.public_inputs(<transient_crypto::commitment::PureGeneratorPedersen as PedersenDowngradeable<Db>>::downgrade(&intent.binding_commitment))?.into_iter())?;
            }
        }
        let actual = node
            .observe_public_reference(&reference)?
            .ok_or_else(|| anyhow!("finalized_reference_not_found"))?;
        receipt_identity(&item.receipt, &actual)?;
        material.check_revision(&actual.contract_state)?;
        observations.push(json!({"event":format!("{event:?}"),"transactionId":actual.transaction_id,"blockHash":actual.block_hash,"height":actual.height,"extrinsicIndex":actual.extrinsic_index,"extrinsicHash":actual.extrinsic_hash,"contractStateSha256":hash(&actual.contract_state)}));
    }
    ensure!(
        record.deployment.receipt.height < record.call.receipt.height,
        "deployment_call_order_mismatch"
    );
    let current = node.finalized_contract_state(expected_address)?;
    material.check_revision(&current.bytes)?;
    Ok(
        json!({"status":"selected-private-claim-deployment-identity-qualified","guaranteeVersion":GUARANTEE,"address":expected_address,"observations":observations,"currentFinalizedHash":current.block_hash,"currentFinalizedHeight":current.height,"currentOperationRevisionMatched":true,"publicOnly":true,"nativeKeygenAndImplementationAssumptionsRequired":true,"trustedNodeFinalityRequired":true,"consensusLightClient":false,"businessSpecificationReviewed":false,"universalCompilerVerified":false}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn adaptive_quote_changes_never_rewrite_the_pinned_historical_bytes() {
        let pinned = ledger::structure::INITIAL_PARAMETERS.clone();
        let original = encode(&pinned).unwrap();
        let mut live = pinned.clone();
        live.fee_prices.overall_price = base_crypto::cost_model::FixedPoint::ONE;
        assert_ne!(encode(&live).unwrap(), original);
        check_non_price_parameters(&pinned, &live).unwrap();
        live.global_ttl = base_crypto::time::Duration::from_secs(1);
        assert!(check_non_price_parameters(&pinned, &live).is_err());
        assert_eq!(encode(&pinned).unwrap(), original);
    }
    #[test]
    fn full_initial_state_and_operation_revision_are_distinct_checks() {
        let initial = ContractState::<Db>::default();
        check_initial_state(&initial, &encode(&initial).unwrap()).unwrap();
        let mut changed = initial.clone();
        changed.maintenance_authority.counter += 1;
        assert!(check_initial_state(&initial, &encode(&changed).unwrap()).is_err());
        assert!(check_operation_revision(&initial, &encode(&changed).unwrap()).is_err());
        let mut changed = initial.clone();
        changed.operations = changed.operations.insert(
            onchain_runtime::state::EntryPointBuf(b"other".to_vec()),
            ContractOperation::new(None, None),
        );
        assert!(check_operation_revision(&initial, &encode(&changed).unwrap()).is_err());
        let mut changed = initial.clone();
        changed.balance = changed
            .balance
            .insert(coin_structure::coin::TokenType::Dust, 1);
        assert!(check_initial_state(&initial, &encode(&changed).unwrap()).is_err());
        let mut trailing = encode(&initial).unwrap();
        trailing.push(0);
        assert!(check_operation_revision(&initial, &trailing).is_err());
    }
    #[test]
    fn public_specification_rejects_wrong_scope_and_nonempty_initial_map() {
        let mut spec = Specification {
            schema_version: 1,
            guarantee_version: GUARANTEE.into(),
            authority_sha256: "1".repeat(64),
            source_commit: "1".repeat(40),
            source_tree: "2".repeat(40),
            entrypoint: "claim".into(),
            initialization: BTreeMap::from([
                ("acceptedRoot".into(), json!("1")),
                ("campaignId".into(), json!("9")),
                ("spent".into(), json!([])),
            ]),
            policy: NetworkPolicy {
                network_id: "undeployed".into(),
                genesis: "1".repeat(64),
                spec_version: 2001100,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
                max_dust: 1,
            },
            ledger_parameters_sha256: "1".repeat(64),
            ledger_parameters_block_hash: "1".repeat(64),
            ledger_parameters_height: 1,
            ledger_price_policy: "adaptive-fee-prices-v1".into(),
            srs_sha256: "1".repeat(64),
            native_toolchain_sha256: "1".repeat(64),
            runtime_code_hash: "1".repeat(64),
            metadata_sha256: "1".repeat(64),
        };
        spec.validate().unwrap();
        spec.entrypoint = "other".into();
        assert!(spec.validate().is_err());
        spec.entrypoint = "claim".into();
        spec.initialization.insert("spent".into(), json!([true]));
        assert!(spec.validate().is_err());
        spec.initialization.insert("spent".into(), json!([]));
        spec.policy.profile = "midnight-ledger-9".into();
        assert!(spec.validate().is_err());
    }
}
