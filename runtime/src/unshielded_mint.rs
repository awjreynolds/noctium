//! Exact recipient outputs derived from a proved custom unshielded mint.
use crate::{Db, proof::ProvedNativeIntent};
use base_crypto::hash::HashOutput;
use coin_structure::coin::{PublicAddress, TokenType};
use ledger::structure::{ContractAction, UnshieldedOffer, UtxoOutput};
use onchain_runtime::context::{ClaimedUnshieldedSpendsKey, Effects};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Error {
    UnsupportedShape,
    InvalidOutput,
}

/// Derive one user UTXO from the exact guaranteed effects of a proved single-call mint.
///
/// The issuer comes from the proved call address. The domain, user address, and amount come
/// from its guaranteed transcript. No caller-provided output participates in this derivation.
pub(crate) fn derive_user_output(intent: &ProvedNativeIntent) -> Result<UtxoOutput, Error> {
    if intent.actions.len() != 1
        || intent.fallible_unshielded_offer.is_some()
        || intent.dust_actions.is_some()
    {
        return Err(Error::UnsupportedShape);
    }
    let Some(ContractAction::Call(call)) = intent.actions.get(0) else {
        return Err(Error::UnsupportedShape);
    };
    if call.fallible_transcript.is_some() {
        return Err(Error::UnsupportedShape);
    }
    let Some(transcript) = call.guaranteed_transcript.as_deref() else {
        return Err(Error::UnsupportedShape);
    };
    output_from_effects(call.address, &transcript.effects)
}

/// Check that the attached offer contains exactly the derived output.
///
/// The offer must be present and contain no inputs, signatures, or additional outputs.
/// Construction starts from `derive_user_output`, attaches that output, then calls this.
pub(crate) fn validate_user_output_offer(intent: &ProvedNativeIntent) -> Result<UtxoOutput, Error> {
    let expected = derive_user_output(intent)?;
    let Some(offer) = intent.guaranteed_unshielded_offer.as_deref() else {
        return Err(Error::InvalidOutput);
    };
    validate_offer(offer, &expected)?;
    Ok(expected)
}

fn validate_offer(
    offer: &UnshieldedOffer<ledger::structure::Signature, Db>,
    expected: &UtxoOutput,
) -> Result<(), Error> {
    if !offer.inputs.is_empty()
        || !offer.signatures.is_empty()
        || offer.outputs.len() != 1
        || offer.outputs.get(0) != Some(expected)
    {
        return Err(Error::InvalidOutput);
    }
    Ok(())
}

fn output_from_effects(
    issuer: coin_structure::contract::ContractAddress,
    effects: &Effects<Db>,
) -> Result<UtxoOutput, Error> {
    if effects.unshielded_mints.size() != 1
        || effects.claimed_unshielded_spends.size() != 1
        || effects.unshielded_inputs.size() != 0
        || effects.unshielded_outputs.size() != 0
        || effects.claimed_nullifiers.size() != 0
        || effects.claimed_shielded_receives.size() != 0
        || effects.claimed_shielded_spends.size() != 0
        || effects.claimed_contract_calls.size() != 0
        || effects.shielded_mints.size() != 0
    {
        return Err(Error::UnsupportedShape);
    }

    let Some(mint_entry) = effects.unshielded_mints.iter().next() else {
        return Err(Error::UnsupportedShape);
    };
    let (domain, mint_amount) = &*mint_entry;
    let domain: HashOutput = **domain;
    let mint_amount: u64 = **mint_amount;
    let color = issuer.custom_unshielded_token_type(domain);
    let expected_token = TokenType::Unshielded(color);

    let Some(claim_entry) = effects.claimed_unshielded_spends.iter().next() else {
        return Err(Error::UnsupportedShape);
    };
    let (claim_key, claim_amount) = &*claim_entry;
    let claim_amount: u128 = **claim_amount;
    let ClaimedUnshieldedSpendsKey(token, PublicAddress::User(owner)) = &**claim_key else {
        return Err(Error::UnsupportedShape);
    };
    if mint_amount == 0 || claim_amount != u128::from(mint_amount) || *token != expected_token {
        return Err(Error::UnsupportedShape);
    }

    Ok(UtxoOutput {
        value: claim_amount,
        owner: *owner,
        type_: color,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use base_crypto::hash::HashOutput;

    #[test]
    fn exact_output_offer_rejects_substitutions() {
        let expected = UtxoOutput {
            value: 7,
            owner: coin_structure::coin::UserAddress(HashOutput([9; 32])),
            type_: coin_structure::coin::UnshieldedTokenType(HashOutput([3; 32])),
        };
        let matching = UnshieldedOffer::<ledger::structure::Signature, Db> {
            inputs: Default::default(),
            outputs: vec![expected.clone()].into(),
            signatures: Default::default(),
        };
        assert_eq!(validate_offer(&matching, &expected), Ok(()));

        for output in [
            UtxoOutput {
                owner: coin_structure::coin::UserAddress(HashOutput([10; 32])),
                ..expected.clone()
            },
            UtxoOutput {
                value: 8,
                ..expected.clone()
            },
            UtxoOutput {
                type_: coin_structure::coin::UnshieldedTokenType(HashOutput([4; 32])),
                ..expected.clone()
            },
        ] {
            let mut substituted = matching.clone();
            substituted.outputs = vec![output].into();
            assert_eq!(
                validate_offer(&substituted, &expected),
                Err(Error::InvalidOutput)
            );
        }
        let mut extra = matching;
        extra.outputs = vec![expected.clone(), expected.clone()].into();
        assert_eq!(validate_offer(&extra, &expected), Err(Error::InvalidOutput));
    }
}
