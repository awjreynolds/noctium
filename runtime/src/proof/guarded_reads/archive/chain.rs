use anyhow::{Context, Result, ensure};
use onchain_runtime::state::ContractState;
use parity_scale_codec::{Compact, Decode};
use serde_json::{Value as Json, json};

use crate::{
    Db,
    client::{ContractEvent, NetworkPolicy, PublicTransactionReference},
    funding::SealedTransaction,
    localnet::{Node, Rpc},
};

fn text<'a>(record: &'a Json, key: &str) -> Result<&'a str> {
    record
        .get(key)
        .and_then(Json::as_str)
        .with_context(|| format!("archived {key} is missing"))
}

fn number(record: &Json, key: &str) -> Result<u64> {
    record
        .get(key)
        .and_then(Json::as_u64)
        .with_context(|| format!("archived {key} is invalid"))
}

fn hash_field(record: &Json, key: &str) -> Result<String> {
    let value = text(record, key)?.trim_start_matches("0x");
    let bytes = hex::decode(value).with_context(|| format!("archived {key} is not hex"))?;
    ensure!(bytes.len() == 32, "archived {key} must be 32 bytes");
    Ok(hex::encode(bytes))
}

fn block_hash(rpc: &Rpc, height: u64) -> Result<String> {
    let value = rpc.call("chain_getBlockHash", json!([height]))?;
    let encoded = value
        .as_str()
        .context("chain_getBlockHash returned a non-string")?
        .strip_prefix("0x")
        .context("chain_getBlockHash omitted its 0x prefix")?;
    let bytes = hex::decode(encoded).context("chain_getBlockHash returned invalid hex")?;
    ensure!(
        bytes.len() == 32,
        "chain_getBlockHash returned a non-32-byte hash"
    );
    Ok(hex::encode(bytes))
}

fn hex_bytes(value: &Json) -> Result<Vec<u8>> {
    let encoded = value
        .as_str()
        .context("chain RPC returned a non-string byte value")?;
    hex::decode(encoded.strip_prefix("0x").unwrap_or(encoded))
        .context("chain RPC returned invalid hex bytes")
}

/// Re-read one retained public transaction and its exact inclusion-block state.
/// Panics with the failing archive check because callers are focused regression tests.
pub(super) fn read_finalized_transaction(
    node: &Node,
    rpc: &Rpc,
    policy: &NetworkPolicy,
    address: &str,
    record: &Json,
    expected_event: ContractEvent,
) -> (SealedTransaction, ContractState<Db>) {
    let checked = || -> Result<(SealedTransaction, ContractState<Db>)> {
        let height = number(record, "height")?;
        let finalized_height = number(record, "finalizedHeight")?;
        let extrinsic_index = number(record, "extrinsicIndex")?;
        let extrinsic_index =
            u32::try_from(extrinsic_index).context("archived extrinsic index exceeds u32")?;
        ensure!(height > 0, "archived inclusion height must be nonzero");
        ensure!(
            finalized_height >= height,
            "archived finalized height precedes inclusion"
        );

        let archived_block_hash = hash_field(record, "blockHash")?;
        let archived_finalized_hash = hash_field(record, "finalizedHash")?;
        ensure!(
            block_hash(rpc, height)? == archived_block_hash,
            "archived block hash is not canonical at its height"
        );
        ensure!(
            block_hash(rpc, finalized_height)? == archived_finalized_hash,
            "archived finalized hash is not canonical at its height"
        );
        ensure!(
            text(record, "event")? == format!("{expected_event:?}"),
            "archived event differs from the expected event"
        );
        let block = rpc.call(
            "chain_getBlock",
            json!([format!("0x{archived_block_hash}")]),
        )?;
        let extrinsics = block["block"]["extrinsics"]
            .as_array()
            .context("archived block has no extrinsics array")?;
        let header_number = block["block"]["header"]["number"]
            .as_str()
            .context("archived block header number is missing")?
            .trim_start_matches("0x");
        ensure!(
            u64::from_str_radix(header_number, 16).context("invalid archived block number")?
                == height,
            "archived block header number differs from its recorded height"
        );
        let encoded_extrinsic = hex_bytes(
            extrinsics
                .get(extrinsic_index as usize)
                .context("archived extrinsic index is outside its block")?,
        )?;

        let metadata = rpc.metadata(&archived_block_hash)?;
        let mut cursor = encoded_extrinsic.as_slice();
        let Compact(payload_length) =
            Compact::<u32>::decode(&mut cursor).context("invalid extrinsic length prefix")?;
        ensure!(
            usize::try_from(payload_length).ok() == Some(cursor.len()),
            "extrinsic length prefix does not match its bytes"
        );
        ensure!(
            u8::decode(&mut cursor).context("missing extrinsic version")? == 4,
            "archived transaction is not an unsigned v4 extrinsic"
        );
        ensure!(
            u8::decode(&mut cursor).context("missing extrinsic pallet index")? == metadata.pallet,
            "archived extrinsic uses a different pallet"
        );
        ensure!(
            u8::decode(&mut cursor).context("missing extrinsic call index")? == metadata.call,
            "archived extrinsic uses a different call"
        );
        let transaction_bytes =
            Vec::<u8>::decode(&mut cursor).context("invalid native transaction SCALE bytes")?;
        ensure!(!transaction_bytes.is_empty(), "native transaction is empty");
        ensure!(cursor.is_empty(), "extrinsic has trailing bytes");
        ensure!(
            metadata.extrinsic(&transaction_bytes)? == encoded_extrinsic,
            "metadata re-encoding differs from the archived extrinsic"
        );
        use blake2::Digest;
        let extrinsic_hash = hex::encode(blake2::Blake2b::<blake2::digest::consts::U32>::digest(
            &encoded_extrinsic,
        ));
        ensure!(
            extrinsic_hash == hash_field(record, "extrinsicHash")?,
            "archived extrinsic hash differs"
        );

        let state_bytes = hex_bytes(&rpc.call(
            "midnight_contractState",
            json!([address, format!("0x{archived_block_hash}")]),
        )?)?;
        let state: ContractState<Db> = crate::proof::decode(&state_bytes).map_err(|error| {
            anyhow::anyhow!("historical state is not a tagged ContractState: {error}")
        })?;
        let mut canonical_state = Vec::new();
        serialize::tagged_serialize(&state, &mut canonical_state)
            .context("cannot encode canonical historical ContractState")?;
        ensure!(
            canonical_state == state_bytes,
            "historical ContractState encoding is not canonical"
        );
        ensure!(
            crate::artifacts::digest(&canonical_state) == hash_field(record, "stateSha256")?,
            "historical state digest differs from the archived digest"
        );

        let reference = PublicTransactionReference::from_bytes(
            policy.clone(),
            &transaction_bytes,
            height - 1,
            &canonical_state,
        )?;
        ensure!(
            reference.transaction_id() == text(record, "transactionId")?,
            "archived transaction id differs from native transaction bytes"
        );
        ensure!(
            reference.contract_address() == address && reference.event() == expected_event,
            "native transaction address or event differs from the archive"
        );
        ensure!(
            reference.bound_view().intent_id() == text(record, "intentId")?,
            "archived intent id differs from native transaction bytes"
        );

        let observed = node
            .observe_public_reference(&reference)?
            .context("archived transaction is not found in finalized history")?;
        ensure!(
            observed.block_hash == archived_block_hash
                && observed.height == height
                && observed.extrinsic_index == extrinsic_index
                && observed.extrinsic_hash == extrinsic_hash
                && observed.transaction_id == text(record, "transactionId")?
                && observed.intent_id == text(record, "intentId")?
                && observed.contract_address == address
                && observed.event == expected_event
                && observed.contract_state == canonical_state,
            "observed finalized receipt differs from the archived transaction"
        );
        ensure!(
            observed.finalized_height >= finalized_height,
            "observed finality does not cover the archived finalized height"
        );
        ensure!(
            block_hash(rpc, observed.finalized_height)? == observed.finalized_hash,
            "observed finalized hash is not canonical at its height"
        );

        let transaction: SealedTransaction =
            crate::proof::decode(&transaction_bytes).map_err(|error| {
                anyhow::anyhow!("native transaction is not a sealed transaction: {error}")
            })?;
        Ok((transaction, state))
    };

    checked()
        .unwrap_or_else(|error| panic!("archived finalized transaction check failed: {error:#}"))
}
