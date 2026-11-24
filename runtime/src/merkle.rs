//! Read-only access to Merkle trees stored in a typed ledger snapshot.
#[cfg(feature = "zkir-321")]
use crate::foreign;
use crate::{Db, StateDecl, Value, aggregates::Schema, ledger_key_type, native_ffi};
use anyhow::{Context, Result, anyhow, bail, ensure};
use base_crypto::{
    fab::{AlignedValue, Alignment, AlignmentAtom, AlignmentSegment, ValueAtom},
    hash::HashOutput,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::Value as Json;
use std::collections::HashSet;
use storage::{
    arena::{ArenaHash, Sp},
    db::DB,
};
use transient_crypto::{
    curve::Fr,
    fab::ValueReprAlignedValue,
    hash::{degrade_to_transient, transient_hash},
    merkle_tree::{MerklePath, MerklePathEntry, MerkleTree, MerkleTreeNode, leaf_hash},
};

/// A Merkle tree's root and append position in a supplied ledger snapshot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MerkleTreeView {
    pub root: Fr,
    /// Equal to the capacity when the tree is full.
    pub first_free: u64,
}

/// A candidate path for a supplied leaf digest at an index.
pub struct IndexedMerklePath {
    pub snapshot_root: Fr,
    pub candidate_root: Fr,
    /// Siblings and directions in leaf-to-root order.
    pub entries: Vec<MerklePathEntry>,
}

/// A snapshot-checked path to a leaf stored as a 32-byte digest.
pub struct PrehashedMerklePath {
    leaf_hash: HashOutput,
    entries: Vec<MerklePathEntry>,
    root: Fr,
}

impl PrehashedMerklePath {
    pub fn root(&self) -> Fr {
        self.root
    }

    pub fn leaf_hash(&self) -> &[u8; 32] {
        &self.leaf_hash.0
    }

    /// Siblings and directions in leaf-to-root order.
    pub fn entries(&self) -> &[MerklePathEntry] {
        &self.entries
    }
}

/// A read-only snapshot view of an ordinary or historic Merkle tree.
pub struct MerkleTreeSnapshot {
    tree: MerkleTree<(), Db>,
    first_free: u64,
    historic_state: Option<StateValue<Db>>,
}

impl MerkleTreeSnapshot {
    /// True when the declared tree records historical roots.
    pub fn is_historic(&self) -> bool {
        self.historic_state.is_some()
    }

    /// Read the current root and append position, rejecting unrehashed trees.
    pub fn view(&self) -> Result<MerkleTreeView> {
        let root = self
            .tree
            .root()
            .context("MerkleTree state has an unrehashed root")?
            .0;
        Ok(MerkleTreeView {
            root,
            first_free: self.first_free,
        })
    }

    /// Find a checked path for a Field leaf at a known written index.
    pub fn field_path(&self, index: u64, leaf: Fr) -> Result<MerklePath<Fr>> {
        let path = self.prehashed_path(index, leaf_hash(&leaf).0)?;
        Ok(MerklePath {
            leaf,
            path: path.entries,
        })
    }

    /// Search the written range and return the first stored Field leaf match.
    pub fn find_field_path(&self, leaf: Fr) -> Result<Option<MerklePath<Fr>>> {
        Ok(self
            .find_prehashed_path(leaf_hash(&leaf).0)?
            .map(|path| MerklePath {
                leaf,
                path: path.entries,
            }))
    }

    /// Find the exact stored hash at a known written index.
    pub fn prehashed_path(&self, index: u64, leaf_hash: [u8; 32]) -> Result<PrehashedMerklePath> {
        ensure!(
            index < self.first_free,
            "MerkleTree index is outside the written range"
        );
        let digest = HashOutput(leaf_hash);
        ensure!(
            self.tree
                .index(index)
                .is_some_and(|(hash, ())| hash == digest),
            "no matching hash at the MerkleTree index"
        );
        let path = self.indexed_prehashed_path(index, leaf_hash)?;
        ensure!(
            path.candidate_root == path.snapshot_root,
            "MerkleTree path does not reproduce the snapshot root"
        );
        Ok(PrehashedMerklePath {
            leaf_hash: digest,
            entries: path.entries,
            root: path.snapshot_root,
        })
    }

    /// Search the written range and return the first exact stored hash match.
    pub fn find_prehashed_path(&self, leaf_hash: [u8; 32]) -> Result<Option<PrehashedMerklePath>> {
        self.view()?;
        first_merkle_hash_index(
            &self.tree.0,
            HashOutput(leaf_hash),
            self.first_free,
            &mut HashSet::new(),
        )
        .map(|index| self.prehashed_path(index, leaf_hash))
        .transpose()
    }

    /// Read a candidate path for a supplied digest at an index.
    /// The index may point to a materialized branch at or beyond the append cursor.
    pub fn indexed_prehashed_path(
        &self,
        index: u64,
        digest: [u8; 32],
    ) -> Result<IndexedMerklePath> {
        let snapshot_root = self.view()?.root;
        ensure!(
            index < 1u64 << self.tree.height(),
            "MerkleTree index exceeds its capacity"
        );
        // The pinned path reader assumes the final parent is a materialized branch.
        let mut parent = &self.tree.0;
        loop {
            let MerkleTreeNode::Node {
                height,
                left,
                right,
                ..
            } = &**parent
            else {
                bail!("no materialized MerkleTree branch at the index");
            };
            if *height == 1 {
                break;
            }
            let bit = 1u64 << (*height - 1);
            parent = if index & bit == 0 { left } else { right };
        }
        let digest = HashOutput(digest);
        let path = self.tree.path_for_leaf(index, digest)?;
        Ok(IndexedMerklePath {
            snapshot_root,
            candidate_root: merkle_root_from_hash(digest, &path.path),
            entries: path.path,
        })
    }

    /// Read an indexed candidate path for a raw Field leaf.
    pub fn indexed_field_path(&self, index: u64, leaf: Fr) -> Result<IndexedMerklePath> {
        self.indexed_prehashed_path(index, leaf_hash(&leaf).0)
    }

    /// Read an indexed candidate path for a raw leaf encoded by its FAB schema.
    pub fn indexed_structured_path(
        &self,
        index: u64,
        schema: &Schema,
        leaf_json: &[u8],
    ) -> Result<IndexedMerklePath> {
        self.indexed_prehashed_path(index, schema.merkle_leaf_hash(leaf_json)?)
    }

    /// Find a checked path for a typed raw leaf at a known written index.
    pub fn structured_path(
        &self,
        index: u64,
        schema: &Schema,
        leaf_json: &[u8],
    ) -> Result<PrehashedMerklePath> {
        self.prehashed_path(index, schema.merkle_leaf_hash(leaf_json)?)
    }

    /// Search the written range for the first exact hash of a typed raw leaf.
    pub fn find_structured_path(
        &self,
        schema: &Schema,
        leaf_json: &[u8],
    ) -> Result<Option<PrehashedMerklePath>> {
        self.find_prehashed_path(schema.merkle_leaf_hash(leaf_json)?)
    }

    /// Iterate over validated historic root keys without allocating a copy.
    pub fn historic_roots(&self) -> Result<impl Iterator<Item = Result<Fr>> + '_> {
        let state = self
            .historic_state
            .as_ref()
            .ok_or_else(|| anyhow!("historic roots require a historic MerkleTree"))?;
        let StateValue::Map(history) = state else {
            bail!("historic MerkleTree state is missing its root map")
        };
        Ok(history.iter().map(|entry| {
            let (root, value) = &*entry;
            let decoded = decode_historic_root(root)?;
            ensure!(
                matches!(**value, StateValue::Null),
                "historic MerkleTree root value must be Null"
            );
            Ok(decoded)
        }))
    }
}

/// Read a declared root or nested MerkleTree from a typed ledger snapshot.
pub fn merkle_tree_at(
    declarations: &[StateDecl],
    state: &ChargedState<Db>,
    name: &str,
    keys: &[Value],
) -> Result<MerkleTreeSnapshot> {
    let (slot, schema, aligned_keys) = typed_schema_path(declarations, name, keys)?;
    let (depth, historic) = checked_merkle_tree_schema(schema)?;
    let node = state_node_at_path(state, declarations.len(), slot, &aligned_keys)?;
    merkle_tree_snapshot_from_checked_node(&node, depth, historic)
}

/// Build a snapshot after a caller has resolved a typed state path.
pub(crate) fn merkle_tree_at_node(
    schema: &Json,
    node: &StateValue<Db>,
) -> Result<MerkleTreeSnapshot> {
    let (depth, historic) = checked_merkle_tree_schema(schema)?;
    merkle_tree_snapshot_from_checked_node(node, depth, historic)
}

/// Resolve a declared map path with the same typed key alignment used by Merkle reads.
/// The returned node owns a reference-counted snapshot value, while `schema` borrows
/// the final path schema from its declaration.
pub(crate) fn typed_state_path<'a>(
    declarations: &'a [StateDecl],
    state: &ChargedState<Db>,
    name: &str,
    keys: &[Value],
) -> Result<(&'a Json, Sp<StateValue<Db>>)> {
    let (slot, schema, aligned_keys) = typed_schema_path(declarations, name, keys)?;
    let node = state_node_at_path(state, declarations.len(), slot, &aligned_keys)?;
    Ok((schema, node))
}

fn typed_schema_path<'a>(
    declarations: &'a [StateDecl],
    name: &str,
    keys: &[Value],
) -> Result<(usize, &'a Json, Vec<AlignedValue>)> {
    ensure!(declarations.len() <= 16, "state array exceeds native limit");
    let mut matches = declarations
        .iter()
        .enumerate()
        .filter(|(_, declaration)| declaration.name == name);
    let (slot, declaration) = matches.next().context("unknown MerkleTree state name")?;
    ensure!(matches.next().is_none(), "duplicate MerkleTree state name");
    ensure!(keys.len() <= 12, "MerkleTree path exceeds 12 keys");

    let mut schema = declaration.kind.get("tree").unwrap_or(&declaration.kind);
    let mut aligned_keys = Vec::with_capacity(keys.len());
    for key in keys {
        let parts = schema
            .get("map")
            .and_then(Json::as_array)
            .filter(|parts| parts.len() == 2)
            .ok_or_else(|| anyhow!("map path exceeds declared schema"))?;
        let key_type = ledger_key_type(&parts[0])?;
        key.validate()?;
        ensure!(
            key.scalar_type() == key_type,
            "ledger path key type mismatch"
        );
        aligned_keys.push(if key_type.bytes_length().is_some() {
            crate::aligned_bytes(key)?
        } else {
            crate::aligned(key, crate::key_alignment(&key_type).as_ref())?
        });
        schema = &parts[1];
    }
    Ok((slot, schema, aligned_keys))
}

fn state_node_at_path(
    state: &ChargedState<Db>,
    declaration_count: usize,
    slot: usize,
    aligned_keys: &[AlignedValue],
) -> Result<Sp<StateValue<Db>>> {
    let StateValue::Array(root) = state.get_ref() else {
        bail!("contract state must be an array")
    };
    ensure!(
        root.len() == declaration_count,
        "contract state schema mismatch"
    );
    let mut node = Sp::new(
        root.get(slot)
            .ok_or_else(|| anyhow!("state slot out of range"))?
            .clone(),
    );
    for key in aligned_keys {
        node = match &*node {
            StateValue::Map(map) => map
                .get(key)
                .ok_or_else(|| anyhow!("missing map path key"))?,
            _ => bail!("state path does not address a map"),
        };
    }
    Ok(node)
}

fn checked_merkle_tree_schema(schema: &Json) -> Result<(u8, bool)> {
    let fields = schema
        .as_object()
        .ok_or_else(|| anyhow!("invalid MerkleTree schema"))?;
    let depth = fields
        .get("merkleTree")
        .and_then(Json::as_u64)
        .ok_or_else(|| anyhow!("state path is not a declared MerkleTree"))?;
    ensure!(
        (2..=32).contains(&depth),
        "MerkleTree depth must be between 2 and 32"
    );
    ensure!(
        fields.len() == 1 || (fields.len() == 2 && fields.contains_key("historic")),
        "invalid MerkleTree schema"
    );
    let historic = match fields.get("historic") {
        None => false,
        Some(Json::Bool(historic)) => *historic,
        Some(_) => bail!("MerkleTree historic flag must be Boolean"),
    };
    Ok((depth.try_into()?, historic))
}

fn merkle_tree_snapshot_from_checked_node(
    node: &StateValue<Db>,
    depth: u8,
    historic: bool,
) -> Result<MerkleTreeSnapshot> {
    let (tree, first_free) = merkle_tree_parts(node, depth, historic)?;
    let historic_state = if historic {
        let StateValue::Array(parts) = node else {
            bail!("historic MerkleTree state must be an array")
        };
        Some(
            parts
                .get(2)
                .context("historic MerkleTree state is missing its root map")?
                .clone(),
        )
    } else {
        None
    };
    Ok(MerkleTreeSnapshot {
        tree: tree.clone(),
        first_free,
        historic_state,
    })
}

fn merkle_tree_parts(
    state: &StateValue<Db>,
    depth: u8,
    historic: bool,
) -> Result<(&MerkleTree<(), Db>, u64)> {
    let StateValue::Array(node) = state else {
        bail!("MerkleTree state must be an array")
    };
    let expected_len = if historic { 3 } else { 2 };
    ensure!(
        node.len() == expected_len,
        "MerkleTree state has an invalid shape"
    );
    let Some(StateValue::BoundedMerkleTree(tree)) = node.get(0) else {
        bail!("MerkleTree state is missing its bounded tree")
    };
    ensure!(
        tree.height() == depth,
        "MerkleTree height differs from state schema"
    );
    let Some(StateValue::Cell(count)) = node.get(1) else {
        bail!("MerkleTree state is missing its insertion count")
    };
    let Value::UInt { number, .. } =
        crate::decode_state_cell(count, "UIntRange<18446744073709551616>", "u64")?
    else {
        bail!("MerkleTree count must be UInt64")
    };
    let count: u64 = number.try_into()?;
    ensure!(
        count <= 1u64 << depth,
        "MerkleTree count exceeds its capacity"
    );
    if historic {
        let Some(StateValue::Map(history)) = node.get(2) else {
            bail!("historic MerkleTree is missing its root map")
        };
        for entry in history.iter() {
            let (root, value) = &*entry;
            decode_historic_root(root)?;
            ensure!(
                matches!(**value, StateValue::Null),
                "historic MerkleTree root value must be Null"
            );
        }
    }
    Ok((tree, count))
}

fn decode_historic_root(root: &AlignedValue) -> Result<Fr> {
    ensure!(
        root.alignment == Alignment::singleton(AlignmentAtom::Field),
        "historic MerkleTree root key must be Field"
    );
    ensure!(
        root.value.0.len() == 1,
        "invalid historic MerkleTree root key"
    );
    let decoded = Fr::from_le_bytes(&root.value.0[0].0)
        .ok_or_else(|| anyhow!("noncanonical historic MerkleTree root key"))?;
    ensure!(
        root == &crate::field_value(decoded),
        "historic MerkleTree root key encoding mismatch"
    );
    Ok(decoded)
}

fn first_merkle_hash_index(
    node: &Sp<MerkleTreeNode<(), Db>, Db>,
    digest: HashOutput,
    limit: u64,
    misses: &mut HashSet<(ArenaHash<<Db as DB>::Hasher>, u64)>,
) -> Option<u64> {
    if limit == 0 {
        return None;
    }
    // Tagged snapshots share nodes, so memoize misses over each local range.
    let key = (node.hash(), limit);
    if misses.contains(&key) {
        return None;
    }
    let found = match &**node {
        MerkleTreeNode::Leaf { hash, .. } if *hash == digest => Some(0),
        MerkleTreeNode::Node {
            height,
            left,
            right,
            ..
        } => {
            let midpoint = 1 << (*height - 1);
            first_merkle_hash_index(left, digest, limit.min(midpoint), misses).or_else(|| {
                first_merkle_hash_index(right, digest, limit.saturating_sub(midpoint), misses)
                    .map(|index| midpoint + index)
            })
        }
        _ => None,
    };
    if found.is_none() {
        misses.insert(key);
    }
    found
}

fn merkle_root_from_hash(digest: HashOutput, entries: &[MerklePathEntry]) -> Fr {
    entries
        .iter()
        .fold(degrade_to_transient(digest), |child, entry| {
            let sibling = entry.sibling.0;
            if entry.goes_left {
                transient_hash(&[child, sibling])
            } else {
                transient_hash(&[sibling, child])
            }
        })
}

/// Hash a checked curve value with the ledger's native FAB leaf representation.
pub fn merkle_curve_leaf_hash(value: &Value) -> Result<[u8; 32]> {
    let aligned = match value {
        Value::JubjubScalar(_) | Value::JubjubPoint(_) => crate::aligned_storage_cell(value)?,
        #[cfg(feature = "zkir-321")]
        Value::Foreign(value) => {
            use base_crypto::fab::Value as FabValue;
            use foreign::{ForeignFamily, ForeignRole};
            let ty = value.foreign_type();
            let bytes = |length| AlignmentSegment::Atom(AlignmentAtom::Bytes { length });
            let field = AlignmentSegment::Atom(AlignmentAtom::Field);
            let segments = match (ty.family(), ty.role()) {
                (ForeignFamily::Curve25519, ForeignRole::Scalar) => vec![bytes(26), bytes(7)],
                (ForeignFamily::Curve25519, ForeignRole::Point) => {
                    vec![bytes(24), bytes(8), bytes(24), bytes(8)]
                }
                (_, ForeignRole::Point) => {
                    vec![bytes(24), bytes(8), bytes(24), bytes(8), field]
                }
                _ => vec![bytes(24), bytes(8)],
            };
            let atoms = FabValue(value.encode()?.into_iter().map(ValueAtom::from).collect());
            AlignedValue::new(atoms, Alignment(segments))
                .context("foreign curve value does not fit its Merkle FAB alignment")?
        }
        _ => bail!("expected a typed curve value for the Merkle leaf"),
    };
    merkle_fab_leaf_hash(aligned)
}

/// Hash a nonopaque FAB value, including a record containing curve atoms.
pub fn merkle_fab_leaf_hash(value: AlignedValue) -> Result<[u8; 32]> {
    merkle_fab_width(&value.alignment, 0)?;
    ensure!(
        value
            .alignment
            .fits_field_check(&value.value, |atom| Fr::from_le_bytes(&atom.0).is_some())
            && value.value.0.iter().all(ValueAtom::is_in_normal_form),
        "invalid or noncanonical Merkle FAB value"
    );
    Ok(leaf_hash(&ValueReprAlignedValue(value)).0)
}

fn merkle_fab_width(alignment: &Alignment, depth: usize) -> Result<usize> {
    ensure!(
        depth <= 64,
        "Merkle FAB alignment nesting exceeds the limit"
    );
    alignment.0.iter().try_fold(0usize, |total, part| {
        let width = match part {
            AlignmentSegment::Atom(AlignmentAtom::Field) => 32,
            AlignmentSegment::Atom(AlignmentAtom::Bytes { length }) => *length as usize,
            AlignmentSegment::Atom(AlignmentAtom::Compress) => bail!("Merkle FAB leaf is opaque"),
            AlignmentSegment::Option(variants) => {
                let mut widest = 0;
                for variant in variants {
                    widest = widest.max(merkle_fab_width(variant, depth + 1)?);
                }
                2 + widest
            }
        };
        let total = total
            .checked_add(width)
            .context("Merkle FAB width overflow")?;
        ensure!(
            total <= native_ffi::MAX_BYTES,
            "Merkle FAB leaf exceeds the byte limit"
        );
        Ok(total)
    })
}

#[cfg(test)]
#[test]
fn merkle_path_search_handles_shared_and_collapsed_branches() {
    let digest = leaf_hash(&Fr::from(7u64));
    let mut root = degrade_to_transient(digest);
    let mut node = Sp::new(MerkleTreeNode::Leaf {
        hash: digest,
        aux: (),
    });
    for height in 1..=32 {
        root = transient_hash(&[root, root]);
        node = Sp::new(MerkleTreeNode::Node {
            hash: Some(Sp::new(root)),
            left: node.clone(),
            right: node,
            height,
        });
    }
    let mut snapshot = MerkleTreeSnapshot {
        tree: MerkleTree(node),
        first_free: 1 << 32,
        historic_state: None,
    };
    assert!(snapshot.find_prehashed_path([0; 32]).unwrap().is_none());
    let first = snapshot.find_prehashed_path(digest.0).unwrap().unwrap();
    assert_eq!(first.root(), root);
    assert!(first.entries().iter().all(|step| step.goes_left));
    snapshot.tree = snapshot.tree.collapse(0, 1);
    assert!(snapshot.indexed_prehashed_path(0, digest.0).is_err());
    let next = snapshot.find_prehashed_path(digest.0).unwrap().unwrap();
    assert_eq!(next.root(), root);
    assert!(next.entries()[0].goes_left && !next.entries()[1].goes_left);
}
