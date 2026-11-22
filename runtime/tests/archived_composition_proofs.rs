#![cfg(all(feature = "localnet", feature = "zkir-321"))]

//! Offline verification of the two sealed calls retained in block 30432.
//! Public transaction, state, verifier-key, and SRS bytes are supplied by env.
use blake2::{
    Blake2bVar,
    digest::{Update, VariableOutput},
};
use ledger::structure::{ContractAction, PedersenDowngradeable, ProofVersioned, Transaction};
use noctium_runtime::{Db, funding::SealedTransaction, proof::TrustedParameters};
use onchain_runtime::state::{ContractState, EntryPointBuf};
use parity_scale_codec::{Compact, Decode};
use serialize::{Deserializable, Tagged, tagged_deserialize, tagged_serialize};
use sha2::{Digest, Sha256};
use std::{env, fs, path::PathBuf};
use transient_crypto::{
    commitment::PureGeneratorPedersen,
    curve::Fr,
    proofs::{ParamsVerifier, Proof, VerifierKey},
};

const CALLER_ADDRESS: &str = "a0cc5e863a975944bf82548438bf527cdeb95c33eba83a7af1230f31e1025695";
const CALLEE_ADDRESS: &str = "50896ca2fa4858b4d0119751331d464e7f44960980b78f24fd4c1575d9d6b41a";
const CALLER_STATE_SHA256: &str =
    "d3c2f809b7c6a6fd56ad7e9e1ff5d1979e0f94a9cc30f1d63d3087ef63e09cbf";
const CALLEE_STATE_SHA256: &str =
    "96c73b9b42978a0411a12a16846d5c1ae6fb5ac544472f0843c29e2e37493bc0";
const CALLER_KEY_SHA256: &str = "92431428b668f256d648dbd8547dc6bc5ece18055661af8a792d453738aba25d";
const CALLEE_KEY_SHA256: &str = "de10e307fdca29760d8235c8646f0589783c01d02b134a95f0197731651ed365";
const CALLER_SRS_SHA256: &str = "b9009f1098bcefffec3c461ab3a5e3a17f7e5599f0f08c70fcdc55a89227bcbd";
const CALLEE_SRS_SHA256: &str = "e82ae890c080188355f37feaffe91372584cd810615082d9143d4dec0453fd9d";
const EXTRINSIC_BLAKE2B256: &str =
    "cd6999fc7ec8fbd6a691f8a7ef3311441f278df1c0e20b019a6da89e3ff8bea8";

struct RetainedCall {
    address: String,
    entrypoint: String,
    proof: Proof,
    statement: Vec<Fr>,
}

fn read_tagged<T: Deserializable + Tagged>(bytes: &[u8]) -> T {
    let mut reader = bytes;
    let value = tagged_deserialize(&mut reader).expect("tagged public bytes decode");
    assert!(
        reader.is_empty(),
        "tagged public bytes have no trailing data"
    );
    value
}

fn read_state(directory: &PathBuf, name: &str, expected_sha256: &str) -> ContractState<Db> {
    let bytes = fs::read(directory.join(name)).expect("retained public state is readable");
    assert_eq!(hex::encode(Sha256::digest(&bytes)), expected_sha256);
    let state: ContractState<Db> = read_tagged(&bytes);
    let mut canonical = Vec::new();
    tagged_serialize(&state, &mut canonical).expect("state re-encodes");
    assert_eq!(canonical, bytes, "state encoding is canonical");
    state
}

fn pinned_parameters(
    directory: &PathBuf,
    name: &str,
    k: u8,
    expected_sha256: &str,
) -> ParamsVerifier {
    let bytes = fs::read(directory.join(name)).expect("pinned public SRS is readable");
    let trusted = TrustedParameters::from_bytes(&bytes, k, expected_sha256)
        .expect("SRS digest, degree, and raw encoding match the receipt");
    assert_eq!(trusted.k(), k);
    ParamsVerifier::read(bytes.as_slice()).expect("checked SRS decodes for verification")
}

fn operation(state: &ContractState<Db>, name: &str, key_sha256: &str) -> VerifierKey {
    let operation = state
        .operations
        .get(&EntryPointBuf(name.as_bytes().to_vec()))
        .expect("installed operation exists in retained state");
    let key = operation
        .v3_vk()
        .expect("retained operation has a 3.2.1 verifier key")
        .clone();
    let mut encoded = Vec::new();
    tagged_serialize(&key, &mut encoded).expect("verifier key re-encodes");
    assert_eq!(hex::encode(Sha256::digest(&encoded)), key_sha256);
    key
}

fn verify(key: &VerifierKey, parameters: &ParamsVerifier, proof: &Proof, statement: &[Fr]) -> bool {
    key.verify(parameters, proof, statement.iter().copied())
        .is_ok()
}

#[test]
#[ignore = "requires the public retained block-30432 bytes in NOCTIUM_ARCHIVED_COMPOSITION_DIR"]
fn retained_composition_proofs_verify_against_their_installed_keys_and_historical_srs() {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_ARCHIVED_COMPOSITION_DIR")
            .expect("set NOCTIUM_ARCHIVED_COMPOSITION_DIR to the retained public byte directory"),
    );

    let extrinsic =
        fs::read(directory.join("extrinsic.scale")).expect("retained public extrinsic is readable");
    let mut extrinsic_hash = [0u8; 32];
    let mut hasher = Blake2bVar::new(extrinsic_hash.len()).expect("valid BLAKE2b digest size");
    Update::update(&mut hasher, &extrinsic);
    hasher
        .finalize_variable(&mut extrinsic_hash)
        .expect("BLAKE2b-256 output has the expected size");
    assert_eq!(hex::encode(extrinsic_hash), EXTRINSIC_BLAKE2B256);
    let mut scale = extrinsic.as_slice();
    let Compact(extrinsic_len) = Compact::<u32>::decode(&mut scale).expect("SCALE length prefix");
    assert_eq!(extrinsic_len as usize, scale.len());
    assert_eq!(u8::decode(&mut scale).unwrap(), 4, "unsigned v4 extrinsic");
    assert_eq!(u8::decode(&mut scale).unwrap(), 5, "pinned pallet index");
    assert_eq!(u8::decode(&mut scale).unwrap(), 0, "pinned send call index");
    let transaction_bytes = Vec::<u8>::decode(&mut scale).expect("transaction call bytes");
    assert!(scale.is_empty());
    let transaction: SealedTransaction = read_tagged(&transaction_bytes);
    let Transaction::Standard(transaction) = transaction else {
        panic!("retained extrinsic contains a standard transaction");
    };
    assert_eq!(transaction.network_id, "undeployed");

    let caller_state = read_state(&directory, "caller.state", CALLER_STATE_SHA256);
    let callee_state = read_state(&directory, "callee.state", CALLEE_STATE_SHA256);
    let caller_key = operation(&caller_state, "claim", CALLER_KEY_SHA256);
    let callee_key = operation(&callee_state, "advance", CALLEE_KEY_SHA256);
    let caller_parameters = pinned_parameters(&directory, "bls_midnight_2p9", 9, CALLER_SRS_SHA256);
    let callee_parameters = pinned_parameters(&directory, "bls_midnight_2p7", 7, CALLEE_SRS_SHA256);
    let caller_srs = fs::read(directory.join("bls_midnight_2p9")).unwrap();
    let callee_srs = fs::read(directory.join("bls_midnight_2p7")).unwrap();
    assert!(TrustedParameters::from_bytes(&caller_srs, 7, CALLER_SRS_SHA256).is_err());
    assert!(TrustedParameters::from_bytes(&callee_srs, 9, CALLEE_SRS_SHA256).is_err());
    assert!(TrustedParameters::from_bytes(&caller_srs, 9, CALLEE_SRS_SHA256).is_err());

    let intent = transaction
        .intents
        .get(&noctium_runtime::funding::CONTRACT_SEGMENT)
        .expect("contract intent exists in retained transaction");
    assert_eq!(
        intent.actions.len(),
        2,
        "retained transaction has two calls"
    );
    let binding =
        <PureGeneratorPedersen as PedersenDowngradeable<Db>>::downgrade(&intent.binding_commitment);
    let calls: Vec<RetainedCall> = intent
        .actions
        .iter_deref()
        .map(|action| {
            let ContractAction::Call(call) = action else {
                panic!("both retained actions are contract calls");
            };
            let ProofVersioned::V3(proof) = &call.proof else {
                panic!("both retained calls use the pinned 3.2.1 proof version");
            };
            RetainedCall {
                address: hex::encode(call.address.0.0),
                entrypoint: String::from_utf8(call.entry_point.0.clone())
                    .expect("entrypoint is UTF-8"),
                proof: proof.clone(),
                statement: call
                    .public_inputs(binding)
                    .expect("bounded call statement materializes"),
            }
        })
        .collect();

    assert_eq!(calls[0].address, CALLER_ADDRESS);
    assert_eq!(calls[0].entrypoint, "claim");
    assert_eq!(calls[1].address, CALLEE_ADDRESS);
    assert_eq!(calls[1].entrypoint, "advance");
    assert!(verify(
        &caller_key,
        &caller_parameters,
        &calls[0].proof,
        &calls[0].statement
    ));
    assert!(verify(
        &callee_key,
        &callee_parameters,
        &calls[1].proof,
        &calls[1].statement
    ));

    let mut changed_statement = calls[0].statement.clone();
    assert!(changed_statement.len() >= 2);
    changed_statement[1] = changed_statement[1] + Fr::from(1u64);
    assert!(!verify(
        &caller_key,
        &caller_parameters,
        &calls[0].proof,
        &changed_statement
    ));
    assert!(!verify(
        &callee_key,
        &caller_parameters,
        &calls[0].proof,
        &calls[0].statement
    ));
    assert!(!verify(
        &caller_key,
        &callee_parameters,
        &calls[1].proof,
        &calls[1].statement
    ));
    assert!(!verify(
        &caller_key,
        &caller_parameters,
        &calls[1].proof,
        &calls[0].statement
    ));
    assert!(!verify(
        &callee_key,
        &callee_parameters,
        &calls[0].proof,
        &calls[1].statement
    ));
}
