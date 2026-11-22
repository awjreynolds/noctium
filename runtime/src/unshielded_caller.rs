//! Snapshot-bound validation for an unshielded caller input scope.
use crate::{Db, client::Snapshot, proof::ProvedNativeIntent};
use coin_structure::coin::UserAddress;
use ledger::structure::{
    ContractAction, Signature, SignatureVerifyingKey, UnshieldedOffer, Utxo, UtxoOutput, UtxoSpend,
};
use serialize::Serializable;
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Error {
    Empty,
    ZeroValue,
    Size,
    MixedOwners,
    NonCanonicalOrder,
    DuplicateOutpoint,
    SpendNotInSnapshot,
    InvalidOffer,
}

/// The exact ordered spend inputs accepted against one retained client snapshot.
pub(crate) struct SnapshotUnshieldedSpendScope<'snapshot> {
    snapshot: &'snapshot Snapshot,
    owner: SignatureVerifyingKey,
    address: UserAddress,
    spends: Vec<UtxoSpend>,
}

impl<'snapshot> SnapshotUnshieldedSpendScope<'snapshot> {
    pub(crate) fn snapshot(&self) -> &'snapshot Snapshot {
        self.snapshot
    }

    pub(crate) fn owner(&self) -> &SignatureVerifyingKey {
        &self.owner
    }

    pub(crate) fn address(&self) -> UserAddress {
        self.address
    }

    pub(crate) fn spends(&self) -> &[UtxoSpend] {
        &self.spends
    }

    /// Build the guaranteed offer with one same-owner return per exact spend.
    ///
    /// The signatures stay empty here. The later approved `Intent::sign` stage
    /// fills them from the caller's signing keys.
    pub(crate) fn guaranteed_offer(&self) -> UnshieldedOffer<Signature, Db> {
        let inputs = self.spends.clone().into();
        let outputs = self
            .spends
            .iter()
            .map(|spend| UtxoOutput {
                value: spend.value,
                owner: self.address,
                type_: spend.type_.clone(),
            })
            .collect::<Vec<_>>()
            .into();

        UnshieldedOffer {
            inputs,
            outputs,
            signatures: Default::default(),
        }
    }
}

/// Validate ledger-ordered, owner-consistent spends against the snapshot's exact UTXO keys.
pub(crate) fn check_snapshot_spends<'snapshot>(
    snapshot: &'snapshot Snapshot,
    spends: &[UtxoSpend],
) -> Result<SnapshotUnshieldedSpendScope<'snapshot>, Error> {
    let Some(first) = spends.first() else {
        return Err(Error::Empty);
    };

    let limit = snapshot.state.parameters.limits.transaction_byte_limit;
    spends.iter().try_fold(0u64, |size, spend| {
        if spend.value == 0 {
            return Err(Error::ZeroValue);
        }
        let length = u64::try_from(spend.serialized_size()).map_err(|_| Error::Size)?;
        size.checked_add(length)
            .filter(|&total| total <= limit)
            .ok_or(Error::Size)
    })?;

    let owner = &first.owner;
    if spends.iter().any(|spend| &spend.owner != owner) {
        return Err(Error::MixedOwners);
    }
    if !spends.is_sorted() {
        return Err(Error::NonCanonicalOrder);
    }

    let mut outpoints = BTreeSet::new();
    if spends
        .iter()
        .any(|spend| !outpoints.insert((spend.intent_hash.clone(), spend.output_no)))
    {
        return Err(Error::DuplicateOutpoint);
    }

    for spend in spends {
        let utxo = Utxo::from(spend.clone());
        if !snapshot.state.utxo.utxos.contains_key(&utxo) {
            return Err(Error::SpendNotInSnapshot);
        }
    }

    let owner = owner.clone();
    let address = UserAddress::from(owner.clone());
    Ok(SnapshotUnshieldedSpendScope {
        snapshot,
        owner,
        address,
        spends: spends.to_vec(),
    })
}

/// Re-admit the exact unsealed offer against the funding snapshot before requesting approval.
pub(crate) fn validate_guaranteed_caller_offer(
    snapshot: &Snapshot,
    contract: &ProvedNativeIntent,
) -> Result<(), Error> {
    if contract.actions.len() != 1
        || !matches!(contract.actions.get(0), Some(ContractAction::Call(_)))
        || contract.fallible_unshielded_offer.is_some()
        || contract.dust_actions.is_some()
    {
        return Err(Error::InvalidOffer);
    }
    let offer = contract
        .guaranteed_unshielded_offer
        .as_deref()
        .ok_or(Error::InvalidOffer)?;
    if !offer.signatures.is_empty()
        || offer.inputs.len() != offer.outputs.len()
        || u64::try_from(offer.inputs.len()).map_err(|_| Error::Size)?
            > snapshot.state.parameters.limits.transaction_byte_limit
    {
        return Err(Error::InvalidOffer);
    }
    let spends: Vec<UtxoSpend> = (&offer.inputs).into();
    let scope = check_snapshot_spends(snapshot, &spends)?;
    if *offer != scope.guaranteed_offer() {
        return Err(Error::InvalidOffer);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::client::ChainIdentity;
    use base_crypto::{hash::HashOutput, time::Timestamp};
    use coin_structure::coin::{NIGHT, UnshieldedTokenType};
    use ledger::structure::{LedgerState, UtxoMeta, UtxoState};
    use onchain_runtime::context::BlockContext;
    use storage::arena::Sp;

    fn test_spend(value: u128, token: UnshieldedTokenType, hash: u8) -> UtxoSpend {
        UtxoSpend {
            value,
            owner: SignatureVerifyingKey::default(),
            type_: token,
            intent_hash: ledger::structure::IntentHash(HashOutput([hash; 32])),
            output_no: u32::from(hash),
        }
    }

    fn snapshot_with(spends: &[UtxoSpend]) -> Snapshot {
        let utxos = spends
            .iter()
            .fold(UtxoState::<Db>::default(), |state, spend| {
                state.insert(
                    Utxo::from(spend.clone()),
                    UtxoMeta {
                        ctime: Timestamp::from_secs(1),
                    },
                )
            });
        let mut state = LedgerState::<Db>::new("test");
        state.utxo = Sp::new(utxos);

        Snapshot {
            chain: ChainIdentity {
                network_id: "test".into(),
                genesis: "test".into(),
                spec_version: 1,
                transaction_version: 1,
                profile: "test".into(),
            },
            finalized_hash: String::new(),
            height: 1,
            state,
            block: BlockContext::default(),
        }
    }

    #[test]
    fn accepted_scope_builds_exact_balanced_guaranteed_offer() {
        let token = UnshieldedTokenType(HashOutput([0x44; 32]));
        let mut spends = vec![test_spend(9, NIGHT, 2), test_spend(4, token, 1)];
        spends.sort();
        let snapshot = snapshot_with(&spends);

        let scope = check_snapshot_spends(&snapshot, &spends).unwrap();
        assert_eq!(scope.spends(), spends.as_slice());
        assert_eq!(scope.owner(), &spends[0].owner);
        assert_eq!(scope.snapshot().height, snapshot.height);

        let offer = scope.guaranteed_offer();
        let offer_inputs: Vec<UtxoSpend> = (&offer.inputs).into();
        let offer_outputs: Vec<UtxoOutput> = (&offer.outputs).into();
        assert_eq!(offer_inputs, spends);
        assert_eq!(offer_outputs.len(), spends.len());
        for (spend, output) in spends.iter().zip(&offer_outputs) {
            assert_eq!(
                output,
                &UtxoOutput {
                    value: spend.value,
                    owner: scope.address(),
                    type_: spend.type_.clone(),
                }
            );
        }
        assert!(offer_outputs.is_sorted());
        assert_eq!(offer.signatures.len(), 0);

        let mut wrong_value = spends[0].clone();
        wrong_value.value += 1;
        assert!(matches!(
            check_snapshot_spends(&snapshot, &[wrong_value]),
            Err(Error::SpendNotInSnapshot)
        ));

        let zero = test_spend(0, NIGHT, 3);
        assert!(matches!(
            check_snapshot_spends(&snapshot_with(std::slice::from_ref(&zero)), &[zero]),
            Err(Error::ZeroValue)
        ));

        let mut mixed_owner = spends[0].clone();
        mixed_owner.owner = SignatureVerifyingKey::ECDSA(Default::default());
        assert!(matches!(
            check_snapshot_spends(&snapshot, &[spends[0].clone(), mixed_owner]),
            Err(Error::MixedOwners)
        ));
    }
}
