//! Canonical composite schema/value transport. Compiler layout construction remains Lean.
use anyhow::{Result, anyhow, bail, ensure};
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Mutex, OnceLock};
use zeroize::Zeroize;

pub const MAX_TRANSPORT_BYTES: usize = 1_048_576;
pub const MAX_LEAVES: usize = 4096;
pub const MAX_NODES: usize = 16384;
pub const MAX_SEQUENCE: usize = 1024;
pub const MAX_DECLARATIONS: usize = 1024;
// Each checked layout/value node has fewer than sixteen JSON metadata nodes.
// This bounds malformed syntax before semantic layout validation, without a depth cap.
const MAX_JSON_NODES: usize = 16 * MAX_NODES + 16;
pub const MAGIC: &[u8] = b"noctium:aggregate:value:v1:";

#[derive(Debug)]
enum JsonNode {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<usize>),
    Object(Vec<(String, usize)>),
}
struct JsonTree {
    nodes: Vec<JsonNode>,
    root: usize,
}
impl Drop for JsonTree {
    fn drop(&mut self) {
        for node in &mut self.nodes {
            match node {
                JsonNode::Number(s) | JsonNode::String(s) => s.zeroize(),
                JsonNode::Bool(b) => *b = false,
                JsonNode::Object(fields) => {
                    for (name, _) in fields {
                        name.zeroize();
                    }
                }
                _ => {}
            }
        }
    }
}
struct JsonFrame {
    index: usize,
    state: u8,
    key: Option<String>,
    keys: BTreeSet<String>,
}
struct Parser<'a> {
    bytes: &'a [u8],
    at: usize,
    nodes: Vec<JsonNode>,
}
impl Parser<'_> {
    fn ws(&mut self) {
        while self.at < self.bytes.len()
            && matches!(self.bytes[self.at], b' ' | b'\n' | b'\r' | b'\t')
        {
            self.at += 1;
        }
    }
    fn string(&mut self) -> Result<String> {
        ensure!(
            self.bytes.get(self.at) == Some(&b'"'),
            "expected JSON string"
        );
        let start = self.at;
        self.at += 1;
        loop {
            match self.bytes.get(self.at).copied() {
                Some(b'"') => {
                    self.at += 1;
                    return serde_json::from_slice(&self.bytes[start..self.at])
                        .map_err(|_| anyhow!("invalid JSON string"));
                }
                Some(b'\\') => {
                    self.at += 2;
                }
                Some(_) => {
                    self.at += 1;
                }
                None => bail!("unterminated JSON string"),
            }
        }
    }
    fn value(&mut self) -> Result<(usize, bool)> {
        self.ws();
        let (node, compound) = match self.bytes.get(self.at).copied() {
            Some(b'{') => {
                self.at += 1;
                (JsonNode::Object(vec![]), true)
            }
            Some(b'[') => {
                self.at += 1;
                (JsonNode::Array(vec![]), true)
            }
            Some(b'"') => (JsonNode::String(self.string()?), false),
            Some(b't') if self.bytes.get(self.at..self.at + 4) == Some(b"true") => {
                self.at += 4;
                (JsonNode::Bool(true), false)
            }
            Some(b'f') if self.bytes.get(self.at..self.at + 5) == Some(b"false") => {
                self.at += 5;
                (JsonNode::Bool(false), false)
            }
            Some(b'n') if self.bytes.get(self.at..self.at + 4) == Some(b"null") => {
                self.at += 4;
                (JsonNode::Null, false)
            }
            Some(b'0'..=b'9') => {
                let start = self.at;
                while self.bytes.get(self.at).is_some_and(u8::is_ascii_digit) {
                    self.at += 1;
                }
                let text = std::str::from_utf8(&self.bytes[start..self.at])
                    .map_err(|_| anyhow!("invalid JSON integer"))?;
                ensure!(
                    text == "0" || !text.starts_with('0'),
                    "noncanonical JSON integer"
                );
                (JsonNode::Number(text.into()), false)
            }
            _ => bail!("unsupported or malformed JSON value"),
        };
        ensure!(
            self.nodes.len() < MAX_JSON_NODES,
            "aggregate JSON syntax resource limit exceeded"
        );
        let index = self.nodes.len();
        self.nodes.push(node);
        Ok((index, compound))
    }
}
impl JsonTree {
    fn parse(bytes: &[u8]) -> Result<Self> {
        ensure!(
            !bytes.is_empty() && bytes.len() <= MAX_TRANSPORT_BYTES,
            "aggregate transport limit exceeded"
        );
        let mut parser = Parser {
            bytes,
            at: 0,
            nodes: vec![],
        };
        let (root, compound) = parser.value()?;
        let mut stack = vec![];
        if compound {
            stack.push(JsonFrame {
                index: root,
                state: 0,
                key: None,
                keys: BTreeSet::new(),
            });
        }
        while let Some(frame) = stack.last_mut() {
            parser.ws();
            let index = frame.index;
            if matches!(parser.nodes[index], JsonNode::Array(_)) {
                match frame.state {
                    0 | 1 => {
                        if frame.state == 0 && parser.bytes.get(parser.at) == Some(&b']') {
                            parser.at += 1;
                            stack.pop();
                            continue;
                        }
                        let (child, compound) = parser.value()?;
                        if let JsonNode::Array(items) = &mut parser.nodes[index] {
                            items.push(child);
                        }
                        frame.state = 2;
                        if compound {
                            stack.push(JsonFrame {
                                index: child,
                                state: 0,
                                key: None,
                                keys: BTreeSet::new(),
                            });
                        }
                    }
                    2 => match parser.bytes.get(parser.at) {
                        Some(b',') => {
                            parser.at += 1;
                            frame.state = 1;
                        }
                        Some(b']') => {
                            parser.at += 1;
                            stack.pop();
                        }
                        _ => bail!("malformed JSON array"),
                    },
                    _ => unreachable!(),
                }
            } else {
                match frame.state {
                    0 | 1 => {
                        if frame.state == 0 && parser.bytes.get(parser.at) == Some(&b'}') {
                            parser.at += 1;
                            stack.pop();
                            continue;
                        }
                        let key = parser.string()?;
                        ensure!(frame.keys.insert(key.clone()), "duplicate JSON field");
                        frame.key = Some(key);
                        frame.state = 2;
                    }
                    2 => {
                        ensure!(
                            parser.bytes.get(parser.at) == Some(&b':'),
                            "malformed JSON object"
                        );
                        parser.at += 1;
                        frame.state = 3;
                    }
                    3 => {
                        let (child, compound) = parser.value()?;
                        if let JsonNode::Object(fields) = &mut parser.nodes[index] {
                            fields.push((
                                frame
                                    .key
                                    .take()
                                    .ok_or_else(|| anyhow!("missing JSON key"))?,
                                child,
                            ));
                        }
                        frame.state = 4;
                        if compound {
                            stack.push(JsonFrame {
                                index: child,
                                state: 0,
                                key: None,
                                keys: BTreeSet::new(),
                            });
                        }
                    }
                    4 => match parser.bytes.get(parser.at) {
                        Some(b',') => {
                            parser.at += 1;
                            frame.state = 1;
                        }
                        Some(b'}') => {
                            parser.at += 1;
                            stack.pop();
                        }
                        _ => bail!("malformed JSON object"),
                    },
                    _ => unreachable!(),
                }
            }
        }
        parser.ws();
        ensure!(parser.at == bytes.len(), "trailing JSON data");
        Ok(Self {
            nodes: parser.nodes,
            root,
        })
    }
    fn object(&self, index: usize) -> Result<&[(String, usize)]> {
        match self.nodes.get(index) {
            Some(JsonNode::Object(fields)) => Ok(fields),
            _ => bail!("expected aggregate object"),
        }
    }
    fn exact(&self, index: usize, expected: &[&str]) -> Result<()> {
        let fields = self.object(index)?;
        ensure!(
            fields.len() == expected.len()
                && fields
                    .iter()
                    .all(|(name, _)| expected.contains(&name.as_str())),
            "unknown or missing aggregate field"
        );
        Ok(())
    }
    fn field(&self, index: usize, name: &str) -> Result<usize> {
        self.object(index)?
            .iter()
            .find_map(|(key, value)| (key == name).then_some(*value))
            .ok_or_else(|| anyhow!("missing aggregate field"))
    }
    fn string(&self, index: usize) -> Result<&str> {
        match self.nodes.get(index) {
            Some(JsonNode::String(value)) => Ok(value),
            _ => bail!("expected aggregate string"),
        }
    }
    fn text(&self, index: usize, name: &str) -> Result<&str> {
        self.string(self.field(index, name)?)
    }
    fn array(&self, index: usize) -> Result<&[usize]> {
        match self.nodes.get(index) {
            Some(JsonNode::Array(items)) => Ok(items),
            _ => bail!("expected aggregate array"),
        }
    }
    fn items(&self, index: usize, name: &str) -> Result<&[usize]> {
        self.array(self.field(index, name)?)
    }
    fn number(&self, index: usize) -> Result<usize> {
        match self.nodes.get(index) {
            Some(JsonNode::Number(value)) => value
                .parse()
                .map_err(|_| anyhow!("aggregate integer outside supported size")),
            _ => bail!("expected aggregate natural number"),
        }
    }
    fn natural(&self, index: usize, name: &str) -> Result<usize> {
        self.number(self.field(index, name)?)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Counts {
    pub leaves: usize,
    pub expanded_nodes: usize,
    pub layout_nodes: usize,
}
impl Counts {
    fn check(self) -> Result<Self> {
        ensure!(
            self.leaves <= MAX_LEAVES
                && self.expanded_nodes <= MAX_NODES
                && self.layout_nodes <= MAX_NODES,
            "aggregate checked-layout resource limit exceeded"
        );
        Ok(self)
    }
}
#[derive(Clone, Debug)]
enum Leaf {
    Native,
    Bool,
    UInt(BigUint),
}
#[derive(Clone, Debug)]
struct Field {
    name: String,
    layout: usize,
}
#[derive(Clone, Debug)]
struct Variant {
    name: String,
    fields: Vec<Field>,
    leaves: usize,
}
#[derive(Clone, Debug)]
struct SourceLeaf {
    type_name: String,
    physical_width: usize,
    curve_type: Option<crate::ScalarType>,
}
#[derive(Debug)]
enum LayoutNode {
    Unit,
    Scalar(Leaf),
    Curve(crate::ScalarType),
    Tuple(Vec<usize>),
    Struct {
        id: String,
        fields: Vec<Field>,
    },
    Vector {
        length: usize,
        element: usize,
    },
    Bytes {
        length: usize,
    },
    Enum {
        id: String,
        variants: Vec<Variant>,
        payload: usize,
    },
}
#[derive(Debug)]
struct Declaration {
    is_enum: bool,
    encoding: String,
    references: BTreeSet<String>,
}

#[derive(Debug)]
pub struct Schema {
    nodes: Vec<LayoutNode>,
    measures: Vec<Counts>,
    root: usize,
    fingerprint: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum FabHashField {
    Bytes(usize),
    Bool,
    UInt(BigUint),
    EnumTag { id: String, maximum: BigUint },
    Native,
}

impl FabHashField {
    fn encoded_field_count(&self) -> usize {
        match self {
            Self::Bytes(length) => length.div_ceil(31),
            _ => 1,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Projection {
    pub kind: String,
    pub index: Option<usize>,
    pub name: Option<String>,
    pub variant: Option<String>,
}

pub struct ProjectedValue {
    pub value: Vec<u8>,
    pub leaf_range: std::ops::Range<usize>,
    pub type_key: String,
}
fn valid_segment(name: &str) -> bool {
    let mut chars = name.bytes();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == b'_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == b'_')
}
fn valid_id(name: &str) -> bool {
    name.split('.').all(valid_segment)
}
fn decimal(text: &str) -> Result<BigUint> {
    ensure!(
        !text.is_empty()
            && text.len() <= crate::MODULUS.len()
            && text.bytes().all(|b| b.is_ascii_digit())
            && (text == "0" || !text.starts_with('0')),
        "expected canonical aggregate scalar decimal"
    );
    BigUint::parse_bytes(text.as_bytes(), 10)
        .ok_or_else(|| anyhow!("invalid aggregate scalar decimal"))
}
fn scalar_maximum(leaf: &Leaf) -> BigUint {
    match leaf {
        Leaf::Native => decimal(crate::MODULUS).expect("fixed modulus") - 1u8,
        Leaf::Bool => 1u8.into(),
        Leaf::UInt(max) => max.clone(),
    }
}
fn encoded_text(text: &str) -> String {
    format!("{}:{}", text.len(), text)
}
fn add(a: usize, b: usize) -> Result<usize> {
    a.checked_add(b)
        .ok_or_else(|| anyhow!("aggregate count overflow"))
}
fn curve_width(ty: &crate::ScalarType) -> Result<usize> {
    Ok(match ty {
        crate::ScalarType::JubjubScalar => 1,
        crate::ScalarType::JubjubPoint => 2,
        #[cfg(feature = "zkir-321")]
        crate::ScalarType::Foreign(ty) => ty.native_type().encoded_len(),
        _ => bail!("unsupported aggregate curve type"),
    })
}
fn curve_source_name(ty: &crate::ScalarType) -> Result<String> {
    Ok(match ty {
        crate::ScalarType::JubjubScalar => "JubjubScalar".to_owned(),
        crate::ScalarType::JubjubPoint => "JubjubPoint".to_owned(),
        #[cfg(feature = "zkir-321")]
        crate::ScalarType::Foreign(ty) => ty.source_name().to_owned(),
        _ => bail!("unsupported aggregate curve type"),
    })
}
fn curve_type_encoding(ty: &crate::ScalarType) -> Result<String> {
    Ok(match ty {
        crate::ScalarType::JubjubScalar => "sJS".to_owned(),
        crate::ScalarType::JubjubPoint => "sJP".to_owned(),
        #[cfg(feature = "zkir-321")]
        crate::ScalarType::Foreign(ty) => {
            format!("sF{}:{}", ty.source_name().len(), ty.source_name())
        }
        _ => bail!("unsupported aggregate curve type"),
    })
}
fn curve_type_key(ty: &crate::ScalarType) -> Result<String> {
    Ok(match ty {
        crate::ScalarType::JubjubScalar => "jubjubScalar".to_owned(),
        crate::ScalarType::JubjubPoint => "jubjubPoint".to_owned(),
        #[cfg(feature = "zkir-321")]
        crate::ScalarType::Foreign(ty) => format!("foreign:{}", ty.source_name()),
        _ => bail!("unsupported aggregate curve type"),
    })
}
fn curve_from_tree(tree: &JsonTree, raw: usize, ty: &crate::ScalarType) -> Result<Vec<BigUint>> {
    let value = match ty {
        crate::ScalarType::JubjubScalar => {
            tree.exact(raw, &["kind", "value"])?;
            ensure!(
                tree.text(raw, "kind")? == "jubjubScalar",
                "aggregate curve value type mismatch"
            );
            serde_json::json!({"kind":"jubjubScalar","value":tree.text(raw, "value")?})
        }
        crate::ScalarType::JubjubPoint => {
            tree.exact(raw, &["kind", "x", "y"])?;
            ensure!(
                tree.text(raw, "kind")? == "jubjubPoint",
                "aggregate curve value type mismatch"
            );
            serde_json::json!({
                "kind":"jubjubPoint",
                "x":tree.text(raw, "x")?,
                "y":tree.text(raw, "y")?
            })
        }
        #[cfg(feature = "zkir-321")]
        crate::ScalarType::Foreign(foreign_ty) => {
            tree.exact(raw, &["kind", "type", "bytes"])?;
            ensure!(
                tree.text(raw, "kind")? == "foreign"
                    && tree.text(raw, "type")? == foreign_ty.source_name(),
                "aggregate curve value type mismatch"
            );
            let bytes = tree
                .items(raw, "bytes")?
                .iter()
                .map(|index| {
                    let byte = tree.number(*index)?;
                    ensure!(byte <= 255, "aggregate foreign byte out of range");
                    Ok(byte)
                })
                .collect::<Result<Vec<_>>>()?;
            serde_json::json!({"kind":"foreign","type":foreign_ty.source_name(),"bytes":bytes})
        }
        _ => bail!("unsupported aggregate curve type"),
    };
    let value = crate::input_value(&curve_source_name(ty)?, &value)?;
    let fields = crate::typed_scalar_fields(&value)?;
    ensure!(
        fields.len() == curve_width(ty)?,
        "aggregate curve encoding width mismatch"
    );
    Ok(fields
        .iter()
        .map(|field| BigUint::from_bytes_le(&field.as_le_bytes()))
        .collect())
}
fn curve_merkle_widths(ty: &crate::ScalarType) -> Result<Vec<usize>> {
    Ok(match ty {
        crate::ScalarType::JubjubScalar => vec![32],
        crate::ScalarType::JubjubPoint => vec![32, 32],
        #[cfg(feature = "zkir-321")]
        crate::ScalarType::Foreign(ty) => {
            use crate::foreign::{ForeignFamily, ForeignRole};
            match (ty.family(), ty.role()) {
                (ForeignFamily::Curve25519, ForeignRole::Scalar) => vec![26, 7],
                (ForeignFamily::Curve25519, ForeignRole::Point) => vec![24, 8, 24, 8],
                (_, ForeignRole::Point) => vec![24, 8, 24, 8, 32],
                _ => vec![24, 8],
            }
        }
        _ => bail!("unsupported aggregate curve type"),
    })
}
fn mul(a: usize, b: usize) -> Result<usize> {
    a.checked_mul(b)
        .ok_or_else(|| anyhow!("aggregate count overflow"))
}
fn counts_fields(fields: &[Field], counts: &[Counts]) -> Result<Counts> {
    let mut result = Counts {
        leaves: 0,
        expanded_nodes: 0,
        layout_nodes: 0,
    };
    for field in fields {
        let c = counts[field.layout];
        result.leaves = add(result.leaves, c.leaves)?;
        result.expanded_nodes = add(result.expanded_nodes, c.expanded_nodes)?;
        result.layout_nodes = add(result.layout_nodes, c.layout_nodes)?;
    }
    Ok(result)
}
fn fields_raw(tree: &JsonTree, parent: usize) -> Result<Vec<(String, usize)>> {
    let mut names = BTreeSet::new();
    tree.items(parent, "fields")?
        .iter()
        .map(|index| {
            tree.exact(*index, &["name", "layout"])?;
            let name = tree.text(*index, "name")?;
            ensure!(
                valid_segment(name) && names.insert(name.to_string()),
                "invalid or duplicate aggregate field name"
            );
            Ok((name.into(), tree.field(*index, "layout")?))
        })
        .collect()
}
fn layout_children(tree: &JsonTree, index: usize) -> Result<Vec<usize>> {
    Ok(match tree.text(index, "kind")? {
        "unit" => {
            tree.exact(index, &["kind"])?;
            vec![]
        }
        "scalar" => {
            tree.exact(index, &["kind", "leaf"])?;
            vec![]
        }
        "curve" => {
            tree.exact(index, &["kind", "type"])?;
            vec![]
        }
        "tuple" => {
            tree.exact(index, &["kind", "items"])?;
            tree.items(index, "items")?.to_vec()
        }
        "struct" => {
            tree.exact(index, &["kind", "id", "fields"])?;
            fields_raw(tree, index)?
                .into_iter()
                .map(|(_, child)| child)
                .collect()
        }
        "vector" => {
            tree.exact(index, &["kind", "length", "element"])?;
            vec![tree.field(index, "element")?]
        }
        "bytes" => {
            tree.exact(index, &["kind", "length"])?;
            vec![]
        }
        "enum" => {
            tree.exact(index, &["kind", "id", "variants"])?;
            let mut names = BTreeSet::new();
            let variants = tree.items(index, "variants")?;
            ensure!(!variants.is_empty(), "empty aggregate enum");
            let mut children = vec![];
            for variant in variants {
                tree.exact(*variant, &["name", "fields"])?;
                let name = tree.text(*variant, "name")?;
                ensure!(
                    valid_segment(name) && names.insert(name.to_string()),
                    "invalid or duplicate aggregate variant name"
                );
                children.extend(
                    fields_raw(tree, *variant)?
                        .into_iter()
                        .map(|(_, child)| child),
                );
            }
            children
        }
        _ => bail!("unsupported aggregate layout kind"),
    })
}
fn mapped_fields(
    tree: &JsonTree,
    parent: usize,
    mapping: &BTreeMap<usize, usize>,
) -> Result<Vec<Field>> {
    fields_raw(tree, parent)?
        .into_iter()
        .map(|(name, raw)| {
            Ok(Field {
                name,
                layout: *mapping
                    .get(&raw)
                    .ok_or_else(|| anyhow!("missing aggregate child layout"))?,
            })
        })
        .collect()
}
fn type_encoding(nodes: &[LayoutNode], root: usize) -> Result<String> {
    enum Task {
        Node(usize),
        Text(String),
    }
    let mut stack = vec![Task::Node(root)];
    let mut output = String::new();
    while let Some(task) = stack.pop() {
        match task {
            Task::Text(text) => output.push_str(&text),
            Task::Node(index) => match &nodes[index] {
                LayoutNode::Unit => output.push('u'),
                LayoutNode::Scalar(Leaf::Native) => output.push_str("sN"),
                LayoutNode::Scalar(Leaf::Bool) => output.push_str("sB"),
                LayoutNode::Scalar(Leaf::UInt(max)) => {
                    output.push_str(&format!("sU{};", max.to_str_radix(10)))
                }
                LayoutNode::Curve(ty) => output.push_str(&curve_type_encoding(ty)?),
                LayoutNode::Struct { id, .. } => output.push_str(&format!("r{}", encoded_text(id))),
                LayoutNode::Enum { id, .. } => output.push_str(&format!("e{}", encoded_text(id))),
                LayoutNode::Vector { length, element } => {
                    output.push_str(&format!("v{length};"));
                    stack.push(Task::Node(*element));
                }
                LayoutNode::Bytes { length } => output.push_str(&format!("b{length};")),
                LayoutNode::Tuple(items) => {
                    output.push_str(&format!("t{};[", items.len()));
                    stack.push(Task::Text("]".into()));
                    stack.extend(items.iter().rev().map(|child| Task::Node(*child)));
                }
            },
        }
        ensure!(
            output.len() <= MAX_TRANSPORT_BYTES,
            "aggregate fingerprint transport limit exceeded"
        );
    }
    Ok(output)
}
fn type_references(
    nodes: &[LayoutNode],
    roots: impl IntoIterator<Item = usize>,
) -> BTreeSet<String> {
    let mut pending: Vec<_> = roots.into_iter().collect();
    let mut ids = BTreeSet::new();
    while let Some(index) = pending.pop() {
        match &nodes[index] {
            LayoutNode::Struct { id, .. } | LayoutNode::Enum { id, .. } => {
                ids.insert(id.clone());
            }
            LayoutNode::Vector { element, .. } => pending.push(*element),
            LayoutNode::Tuple(items) => pending.extend(items),
            _ => {}
        }
    }
    ids
}
fn encode_fields(nodes: &[LayoutNode], fields: &[Field]) -> Result<String> {
    let mut output = String::new();
    for field in fields {
        output.push_str(&format!(
            "f{}{}",
            encoded_text(&field.name),
            type_encoding(nodes, field.layout)?
        ));
        ensure!(
            output.len() <= MAX_TRANSPORT_BYTES,
            "aggregate fingerprint transport limit exceeded"
        );
    }
    Ok(output)
}
fn register_declaration(
    nodes: &[LayoutNode],
    index: usize,
    declarations: &mut BTreeMap<String, Declaration>,
) -> Result<()> {
    let entry = match &nodes[index] {
        LayoutNode::Struct { id, fields } => Some((
            id,
            Declaration {
                is_enum: false,
                encoding: format!(
                    "R{}{};{}",
                    encoded_text(id),
                    fields.len(),
                    encode_fields(nodes, fields)?
                ),
                references: type_references(nodes, fields.iter().map(|field| field.layout)),
            },
        )),
        LayoutNode::Enum { id, variants, .. } => {
            let mut encoding = format!("E{}{};", encoded_text(id), variants.len());
            for variant in variants {
                encoding.push_str(&format!(
                    "V{}{};{}",
                    encoded_text(&variant.name),
                    variant.fields.len(),
                    encode_fields(nodes, &variant.fields)?
                ));
            }
            Some((
                id,
                Declaration {
                    is_enum: true,
                    encoding,
                    references: type_references(
                        nodes,
                        variants
                            .iter()
                            .flat_map(|v| v.fields.iter().map(|f| f.layout)),
                    ),
                },
            ))
        }
        _ => None,
    };
    if let Some((id, declaration)) = entry {
        if let Some(previous) = declarations.get(id) {
            ensure!(
                previous.is_enum == declaration.is_enum
                    && previous.encoding == declaration.encoding,
                "conflicting nominal aggregate definitions"
            );
        } else {
            ensure!(
                declarations.len() < MAX_DECLARATIONS,
                "aggregate declaration limit exceeded"
            );
            declarations.insert(id.clone(), declaration);
        }
    }
    Ok(())
}
impl Schema {
    pub fn from_json(bytes: &[u8]) -> Result<Self> {
        let tree = JsonTree::parse(bytes)?;
        tree.exact(
            tree.root,
            &["schemaVersion", "typeFingerprint", "layout", "counts"],
        )?;
        ensure!(
            tree.natural(tree.root, "schemaVersion")? == 1,
            "unsupported aggregate schema version"
        );
        let raw_root = tree.field(tree.root, "layout")?;
        let mut pending = vec![(raw_root, false)];
        let mut mapping = BTreeMap::new();
        let mut nodes = vec![];
        let mut measures: Vec<Counts> = vec![];
        let mut declarations = BTreeMap::new();
        while let Some((raw, visited)) = pending.pop() {
            if !visited {
                ensure!(
                    pending.len() <= MAX_NODES * 2 && nodes.len() < MAX_NODES,
                    "aggregate retained layout limit exceeded"
                );
                let children = layout_children(&tree, raw)?;
                ensure!(
                    children.len() <= MAX_NODES,
                    "aggregate retained layout limit exceeded"
                );
                pending.push((raw, true));
                pending.extend(children.into_iter().rev().map(|child| (child, false)));
                continue;
            }
            let (node, counts) = match tree.text(raw, "kind")? {
                "unit" => (
                    LayoutNode::Unit,
                    Counts {
                        leaves: 0,
                        expanded_nodes: 1,
                        layout_nodes: 1,
                    },
                ),
                "scalar" => {
                    let leaf = tree.field(raw, "leaf")?;
                    let leaf = match tree.text(leaf, "kind")? {
                        "native" => {
                            tree.exact(leaf, &["kind"])?;
                            Leaf::Native
                        }
                        "bool" => {
                            tree.exact(leaf, &["kind"])?;
                            Leaf::Bool
                        }
                        "uint" => {
                            tree.exact(leaf, &["kind", "maximum"])?;
                            let maximum = decimal(tree.text(leaf, "maximum")?)?;
                            ensure!(
                                maximum <= crate::max_uint(),
                                "aggregate unsigned type exceeds target maximum"
                            );
                            Leaf::UInt(maximum)
                        }
                        _ => bail!("unsupported aggregate scalar leaf"),
                    };
                    (
                        LayoutNode::Scalar(leaf),
                        Counts {
                            leaves: 1,
                            expanded_nodes: 1,
                            layout_nodes: 1,
                        },
                    )
                }
                "curve" => {
                    let ty = crate::ScalarType::parse(tree.text(raw, "type")?)?;
                    let width = curve_width(&ty)?;
                    (
                        LayoutNode::Curve(ty),
                        Counts {
                            leaves: width,
                            expanded_nodes: add(1, width)?,
                            layout_nodes: 1,
                        },
                    )
                }
                "tuple" => {
                    let children: Vec<_> = tree
                        .items(raw, "items")?
                        .iter()
                        .map(|child| mapping[child])
                        .collect();
                    let fields: Vec<_> = children
                        .iter()
                        .map(|child| Field {
                            name: String::new(),
                            layout: *child,
                        })
                        .collect();
                    let count = counts_fields(&fields, &measures)?;
                    (
                        LayoutNode::Tuple(children),
                        Counts {
                            leaves: count.leaves,
                            expanded_nodes: add(1, count.expanded_nodes)?,
                            layout_nodes: add(1, count.layout_nodes)?,
                        },
                    )
                }
                "struct" => {
                    let id = tree.text(raw, "id")?.to_string();
                    ensure!(valid_id(&id), "invalid aggregate nominal identity");
                    let fields = mapped_fields(&tree, raw, &mapping)?;
                    let count = counts_fields(&fields, &measures)?;
                    (
                        LayoutNode::Struct { id, fields },
                        Counts {
                            leaves: count.leaves,
                            expanded_nodes: add(1, count.expanded_nodes)?,
                            layout_nodes: add(1, count.layout_nodes)?,
                        },
                    )
                }
                "vector" => {
                    let length = tree.natural(raw, "length")?;
                    ensure!(
                        length <= MAX_SEQUENCE,
                        "aggregate vector length exceeds target limit"
                    );
                    let element = mapping[&tree.field(raw, "element")?];
                    let child = measures[element];
                    (
                        LayoutNode::Vector { length, element },
                        Counts {
                            leaves: mul(length, child.leaves)?,
                            expanded_nodes: add(1, mul(length, child.expanded_nodes)?)?,
                            layout_nodes: add(1, child.layout_nodes)?,
                        },
                    )
                }
                "bytes" => {
                    let length = tree.natural(raw, "length")?;
                    ensure!(
                        length <= MAX_SEQUENCE,
                        "aggregate byte length exceeds target limit"
                    );
                    (
                        LayoutNode::Bytes { length },
                        Counts {
                            leaves: length,
                            expanded_nodes: add(1, length)?,
                            layout_nodes: 1,
                        },
                    )
                }
                "enum" => {
                    let id = tree.text(raw, "id")?.to_string();
                    ensure!(valid_id(&id), "invalid aggregate nominal identity");
                    let mut variants = vec![];
                    let mut payload = 0;
                    let mut expanded = 1;
                    let mut retained = 1;
                    for variant in tree.items(raw, "variants")? {
                        let fields = mapped_fields(&tree, *variant, &mapping)?;
                        let count = counts_fields(&fields, &measures)?;
                        payload = payload.max(count.leaves);
                        expanded = add(expanded, add(1, count.expanded_nodes)?)?;
                        retained = add(retained, add(1, count.layout_nodes)?)?;
                        variants.push(Variant {
                            name: tree.text(*variant, "name")?.into(),
                            fields,
                            leaves: count.leaves,
                        });
                    }
                    (
                        LayoutNode::Enum {
                            id,
                            variants,
                            payload,
                        },
                        Counts {
                            leaves: add(1, payload)?,
                            expanded_nodes: expanded,
                            layout_nodes: retained,
                        },
                    )
                }
                _ => bail!("unsupported aggregate layout kind"),
            };
            ensure!(
                nodes.len() < MAX_NODES,
                "aggregate retained layout limit exceeded"
            );
            let index = nodes.len();
            nodes.push(node);
            measures.push(counts.check()?);
            register_declaration(&nodes, index, &mut declarations)?;
            mapping.insert(raw, index);
        }
        let root = mapping[&raw_root];
        let count_index = tree.field(tree.root, "counts")?;
        tree.exact(count_index, &["leaves", "expandedNodes", "layoutNodes"])?;
        let claimed = Counts {
            leaves: tree.natural(count_index, "leaves")?,
            expanded_nodes: tree.natural(count_index, "expandedNodes")?,
            layout_nodes: tree.natural(count_index, "layoutNodes")?,
        };
        ensure!(
            claimed == measures[root],
            "aggregate checked-layout count mismatch"
        );
        // Validate nominal references/cycles independently of expanded-tree order.
        for start in declarations.keys() {
            let mut seen = BTreeSet::new();
            let mut work: Vec<_> = declarations[start].references.iter().cloned().collect();
            while let Some(id) = work.pop() {
                ensure!(id != *start, "recursive aggregate nominal definition");
                if !seen.insert(id.clone()) {
                    continue;
                }
                let declaration = declarations
                    .get(&id)
                    .ok_or_else(|| anyhow!("undefined aggregate nominal reference"))?;
                work.extend(declaration.references.iter().cloned());
            }
        }
        let mut fingerprint = format!(
            "NoctiumCompositeTypeV1;{}NoctiumCompositeLayoutV1;{};",
            type_encoding(&nodes, root)?,
            declarations.values().filter(|d| !d.is_enum).count()
        );
        for declaration in declarations.values().filter(|d| !d.is_enum) {
            fingerprint.push_str(&declaration.encoding);
        }
        fingerprint.push_str(&format!(
            "{};",
            declarations.values().filter(|d| d.is_enum).count()
        ));
        for declaration in declarations.values().filter(|d| d.is_enum) {
            fingerprint.push_str(&declaration.encoding);
        }
        ensure!(
            fingerprint.len() <= MAX_TRANSPORT_BYTES
                && fingerprint == tree.text(tree.root, "typeFingerprint")?,
            "aggregate type fingerprint mismatch"
        );
        Ok(Self {
            nodes,
            measures,
            root,
            fingerprint,
        })
    }
    pub fn fingerprint(&self) -> &str {
        &self.fingerprint
    }
    pub fn counts(&self) -> Counts {
        self.measures[self.root]
    }

    fn fab_hash_field(&self, layout: usize) -> Result<FabHashField> {
        match &self.nodes[layout] {
            LayoutNode::Scalar(Leaf::Native) => Ok(FabHashField::Native),
            LayoutNode::Scalar(Leaf::Bool) => Ok(FabHashField::Bool),
            LayoutNode::Scalar(Leaf::UInt(maximum)) => {
                let width = maximum.bits();
                ensure!(
                    width > 0
                        && width <= crate::scalars::MAX_UINT_BITS as u64
                        && maximum + 1u8 == (BigUint::from(1u8) << width as usize),
                    "FAB unsigned field maximum is outside the supported bit widths"
                );
                Ok(FabHashField::UInt(maximum.clone()))
            }
            LayoutNode::Bytes { length } => {
                ensure!(
                    (1..=32).contains(length),
                    "FAB byte field length is outside the supported range"
                );
                Ok(FabHashField::Bytes(*length))
            }
            LayoutNode::Enum { id, variants, .. } => {
                ensure!(
                    !variants.is_empty()
                        && variants.len() <= 256
                        && variants.iter().all(|variant| variant.fields.is_empty()),
                    "FAB hash supports only one-byte fieldless enums"
                );
                Ok(FabHashField::EnumTag {
                    id: id.clone(),
                    maximum: BigUint::from(variants.len() - 1),
                })
            }
            _ => bail!("FAB hash supports only flat scalar and byte fields"),
        }
    }

    /// Return fields for the bounded flat-structure or flat-tuple FAB subset.
    /// Enum payloads need branch-dependent field expressions, so this helper
    /// accepts only one-byte fieldless enums and exposes their tag as a field.
    pub(crate) fn fab_hash_fields(&self) -> Result<Vec<FabHashField>> {
        let layouts: Vec<_> = match &self.nodes[self.root] {
            LayoutNode::Struct { fields, .. } => fields.iter().map(|field| field.layout).collect(),
            LayoutNode::Tuple(items) => items.clone(),
            _ => bail!("FAB hash requires a flat structure or tuple"),
        };
        ensure!(
            (1..=32).contains(&layouts.len()),
            "FAB hash field count is outside the supported range"
        );

        layouts
            .iter()
            .map(|layout| self.fab_hash_field(*layout))
            .collect()
    }

    /// Flatten a checked layout for transient hashing in struct, tuple, and
    /// fixed-vector order. Unit contributes no input fields.
    pub(crate) fn transient_hash_fields(&self) -> Result<Vec<FabHashField>> {
        let mut pending = vec![self.root];
        let mut fields =
            Vec::with_capacity(self.counts().leaves.min(crate::MAX_TRANSIENT_HASH_FIELDS));
        let mut encoded_fields = 0usize;
        let mut visited = 0usize;
        while let Some(layout) = pending.pop() {
            visited = add(visited, 1)?;
            ensure!(
                visited <= self.counts().expanded_nodes,
                "FAB transient hash layout traversal limit exceeded"
            );
            match &self.nodes[layout] {
                LayoutNode::Unit => {}
                LayoutNode::Tuple(items) => pending.extend(items.iter().rev().copied()),
                LayoutNode::Struct { fields, .. } => {
                    pending.extend(fields.iter().rev().map(|field| field.layout));
                }
                LayoutNode::Vector { length, element } => {
                    pending.extend(std::iter::repeat_n(*element, *length));
                }
                _ => {
                    let field = self.fab_hash_field(layout)?;
                    encoded_fields = add(encoded_fields, field.encoded_field_count())?;
                    ensure!(
                        encoded_fields <= crate::MAX_TRANSIENT_HASH_FIELDS,
                        "FAB transient hash field vector exceeds compiler limit"
                    );
                    fields.push(field);
                }
            }
        }
        Ok(fields)
    }

    fn flatten_value(&self, json: &[u8]) -> Result<Vec<BigUint>> {
        let tree = JsonTree::parse(json)?;
        enum Task {
            Visit(usize, usize),
            Pad(usize),
        }
        let mut pending = vec![Task::Visit(self.root, tree.root)];
        let mut leaves = vec![];
        while let Some(task) = pending.pop() {
            match task {
                Task::Pad(count) => leaves.extend((0..count).map(|_| BigUint::from(0u8))),
                Task::Visit(layout, raw) => match &self.nodes[layout] {
                    LayoutNode::Unit => {
                        tree.exact(raw, &["kind"])?;
                        ensure!(
                            tree.text(raw, "kind")? == "unit",
                            "aggregate value kind mismatch"
                        );
                    }
                    LayoutNode::Scalar(leaf) => {
                        let number = match leaf {
                            Leaf::Native => {
                                tree.exact(raw, &["kind", "value"])?;
                                ensure!(
                                    tree.text(raw, "kind")? == "native",
                                    "aggregate scalar kind mismatch"
                                );
                                decimal(tree.text(raw, "value")?)?
                            }
                            Leaf::Bool => {
                                tree.exact(raw, &["kind", "value"])?;
                                ensure!(
                                    tree.text(raw, "kind")? == "bool",
                                    "aggregate scalar kind mismatch"
                                );
                                match tree.nodes.get(tree.field(raw, "value")?) {
                                    Some(JsonNode::Bool(value)) => BigUint::from(u8::from(*value)),
                                    _ => bail!("aggregate Boolean is not a JSON boolean"),
                                }
                            }
                            Leaf::UInt(maximum) => {
                                tree.exact(raw, &["kind", "maximum", "value"])?;
                                ensure!(
                                    tree.text(raw, "kind")? == "uint"
                                        && decimal(tree.text(raw, "maximum")?)? == *maximum,
                                    "aggregate unsigned type mismatch"
                                );
                                decimal(tree.text(raw, "value")?)?
                            }
                        };
                        ensure!(
                            number <= scalar_maximum(leaf),
                            "aggregate scalar outside declared range"
                        );
                        leaves.push(number);
                    }
                    LayoutNode::Curve(ty) => leaves.extend(curve_from_tree(&tree, raw, ty)?),
                    LayoutNode::Tuple(items) => {
                        tree.exact(raw, &["kind", "items"])?;
                        ensure!(
                            tree.text(raw, "kind")? == "tuple",
                            "aggregate value kind mismatch"
                        );
                        let values = tree.items(raw, "items")?;
                        ensure!(
                            values.len() == items.len(),
                            "aggregate tuple arity mismatch"
                        );
                        pending.extend(
                            items
                                .iter()
                                .zip(values)
                                .rev()
                                .map(|(layout, value)| Task::Visit(*layout, *value)),
                        );
                    }
                    LayoutNode::Struct { id, fields } => {
                        tree.exact(raw, &["kind", "id", "fields"])?;
                        ensure!(
                            tree.text(raw, "kind")? == "struct" && tree.text(raw, "id")? == id,
                            "aggregate nominal type mismatch"
                        );
                        let values = value_fields(&tree, raw, fields)?;
                        pending.extend(
                            fields
                                .iter()
                                .zip(values)
                                .rev()
                                .map(|(field, value)| Task::Visit(field.layout, value)),
                        );
                    }
                    LayoutNode::Vector { length, element } => {
                        tree.exact(raw, &["kind", "items"])?;
                        ensure!(
                            tree.text(raw, "kind")? == "vector",
                            "aggregate value kind mismatch"
                        );
                        let values = tree.items(raw, "items")?;
                        ensure!(values.len() == *length, "aggregate vector length mismatch");
                        pending.extend(
                            values
                                .iter()
                                .rev()
                                .map(|value| Task::Visit(*element, *value)),
                        );
                    }
                    LayoutNode::Bytes { length } => {
                        tree.exact(raw, &["kind", "values"])?;
                        ensure!(
                            tree.text(raw, "kind")? == "bytes",
                            "aggregate value kind mismatch"
                        );
                        let values = tree.items(raw, "values")?;
                        ensure!(values.len() == *length, "aggregate byte length mismatch");
                        for value in values {
                            let value = tree.number(*value)?;
                            ensure!(value <= 255, "aggregate byte out of range");
                            leaves.push(value.into());
                        }
                    }
                    LayoutNode::Enum {
                        id,
                        variants,
                        payload,
                    } => {
                        tree.exact(raw, &["kind", "id", "variant", "fields"])?;
                        ensure!(
                            tree.text(raw, "kind")? == "enum" && tree.text(raw, "id")? == id,
                            "aggregate nominal type mismatch"
                        );
                        let tag = variants
                            .iter()
                            .position(|variant| {
                                variant.name == tree.text(raw, "variant").unwrap_or("")
                            })
                            .ok_or_else(|| anyhow!("unknown aggregate enum variant"))?;
                        let variant = &variants[tag];
                        let values = value_fields(&tree, raw, &variant.fields)?;
                        leaves.push(tag.into());
                        pending.push(Task::Pad(payload - variant.leaves));
                        pending.extend(
                            variant
                                .fields
                                .iter()
                                .zip(values)
                                .rev()
                                .map(|(field, value)| Task::Visit(field.layout, value)),
                        );
                    }
                },
            }
            ensure!(
                leaves.len() <= self.counts().leaves,
                "aggregate flattening count mismatch"
            );
        }
        ensure!(
            leaves.len() == self.counts().leaves,
            "aggregate flattening count mismatch"
        );
        Ok(leaves)
    }

    /// Hash a checked structured value using the ledger's FAB leaf encoding.
    pub(crate) fn merkle_leaf_hash(&self, json: &[u8]) -> Result<[u8; 32]> {
        use transient_crypto::merkle_tree::LEAF_HASH_DOMAIN_SEP;

        let mut leaves = self.flatten_value(json)?.into_iter();
        let mut preimage = zeroize::Zeroizing::new(LEAF_HASH_DOMAIN_SEP.to_vec());
        let mut append = |width: usize| -> Result<()> {
            let end = preimage.len() + width;
            ensure!(
                end <= MAX_SEQUENCE,
                "Merkle leaf preimage exceeds the source byte limit"
            );
            let leaf = leaves
                .next()
                .ok_or_else(|| anyhow!("Merkle leaf count mismatch"))?;
            let bytes = zeroize::Zeroizing::new(leaf.to_bytes_le());
            ensure!(
                bytes.len() <= width,
                "Merkle leaf value exceeds its FAB width"
            );
            preimage.extend_from_slice(&bytes);
            preimage.resize(end, 0);
            Ok(())
        };

        let mut pending = vec![self.root];
        while let Some(index) = pending.pop() {
            match &self.nodes[index] {
                LayoutNode::Unit => {}
                LayoutNode::Scalar(Leaf::Native) => append(32)?,
                LayoutNode::Scalar(Leaf::Bool) => append(1)?,
                LayoutNode::Scalar(Leaf::UInt(maximum)) => {
                    append(maximum.bits().div_ceil(8).max(1) as usize)?;
                }
                LayoutNode::Curve(ty) => {
                    let widths = curve_merkle_widths(ty)?;
                    ensure!(
                        widths.len() == curve_width(ty)?,
                        "aggregate curve Merkle alignment width mismatch"
                    );
                    for width in widths {
                        append(width)?;
                    }
                }
                LayoutNode::Tuple(items) => pending.extend(items.iter().rev().copied()),
                LayoutNode::Struct { fields, .. } => {
                    pending.extend(fields.iter().rev().map(|field| field.layout));
                }
                LayoutNode::Vector { length, element } => {
                    pending.extend(std::iter::repeat_n(*element, *length));
                }
                LayoutNode::Bytes { length } => {
                    for _ in 0..*length {
                        append(1)?;
                    }
                }
                LayoutNode::Enum { variants, .. } => {
                    ensure!(
                        variants.iter().all(|variant| variant.fields.is_empty()),
                        "Merkle leaf requires fieldless enum variants"
                    );
                    let width = (usize::BITS - (variants.len() - 1).leading_zeros()).div_ceil(8);
                    append(width.max(1) as usize)?;
                }
            }
        }
        ensure!(leaves.next().is_none(), "Merkle leaf count mismatch");
        Ok(base_crypto::hash::persistent_hash(&preimage).0)
    }

    pub fn validate_value_json(&self, json: &[u8]) -> Result<()> {
        self.flatten_value(json).map(|_| ())
    }

    pub fn native_field_only(&self) -> bool {
        self.nodes.iter().all(|node| {
            matches!(
                node,
                LayoutNode::Scalar(Leaf::Native)
                    | LayoutNode::Tuple(_)
                    | LayoutNode::Struct { .. }
                    | LayoutNode::Vector { .. }
            )
        })
    }

    pub fn leaf_types(&self) -> Result<Vec<String>> {
        let mut pending = vec![self.root];
        let mut result = Vec::with_capacity(self.counts().leaves);
        while let Some(index) = pending.pop() {
            ensure!(
                pending.len() <= MAX_NODES * 2,
                "aggregate type traversal limit exceeded"
            );
            match &self.nodes[index] {
                LayoutNode::Unit => {}
                LayoutNode::Scalar(Leaf::Native) => result.push("Native".to_owned()),
                LayoutNode::Scalar(Leaf::Bool) => result.push("Bool".to_owned()),
                LayoutNode::Scalar(Leaf::UInt(maximum)) => {
                    result.push(format!("UIntRange<{}>", maximum + BigUint::from(1u8)))
                }
                LayoutNode::Curve(ty) => {
                    result.extend(std::iter::repeat_n("Native".to_owned(), curve_width(ty)?));
                }
                LayoutNode::Tuple(items) => pending.extend(items.iter().rev().copied()),
                LayoutNode::Struct { fields, .. } => {
                    pending.extend(fields.iter().rev().map(|field| field.layout));
                }
                LayoutNode::Vector { length, element } => {
                    ensure!(
                        *length <= MAX_LEAVES,
                        "aggregate vector leaf limit exceeded"
                    );
                    for _ in 0..*length {
                        pending.push(*element);
                    }
                }
                LayoutNode::Bytes { length } => {
                    ensure!(
                        result
                            .len()
                            .checked_add(*length)
                            .is_some_and(|count| count <= MAX_LEAVES),
                        "aggregate leaf type limit exceeded"
                    );
                    result.extend(std::iter::repeat_n("Native".to_owned(), *length));
                }
                LayoutNode::Enum { payload, .. } => {
                    ensure!(
                        result
                            .len()
                            .checked_add(1 + *payload)
                            .is_some_and(|count| count <= MAX_LEAVES),
                        "aggregate leaf type limit exceeded"
                    );
                    result.extend(std::iter::repeat_n("Native".to_owned(), 1 + *payload));
                }
            }
            ensure!(
                result.len() <= MAX_LEAVES,
                "aggregate leaf type limit exceeded"
            );
        }
        ensure!(
            result.len() == self.counts().leaves,
            "aggregate leaf type count mismatch"
        );
        Ok(result)
    }

    fn source_leaf_specs(&self) -> Result<Vec<SourceLeaf>> {
        let mut pending = vec![self.root];
        let mut result = Vec::new();
        let mut physical_leaves = 0usize;
        let mut append = |type_name: String,
                          physical_width: usize,
                          curve_type: Option<crate::ScalarType>|
         -> Result<()> {
            ensure!(
                result.len() < MAX_LEAVES,
                "aggregate source leaf type limit exceeded"
            );
            physical_leaves = add(physical_leaves, physical_width)?;
            ensure!(
                physical_leaves <= MAX_LEAVES,
                "aggregate leaf type limit exceeded"
            );
            result.push(SourceLeaf {
                type_name,
                physical_width,
                curve_type,
            });
            Ok(())
        };
        while let Some(index) = pending.pop() {
            ensure!(
                pending.len() <= MAX_NODES * 2,
                "aggregate source leaf traversal limit exceeded"
            );
            match &self.nodes[index] {
                LayoutNode::Unit => {}
                LayoutNode::Scalar(Leaf::Native) => append("Native".into(), 1, None)?,
                LayoutNode::Scalar(Leaf::Bool) => append("Bool".into(), 1, None)?,
                LayoutNode::Scalar(Leaf::UInt(maximum)) => append(
                    format!("UIntRange<{}>", maximum + BigUint::from(1u8)),
                    1,
                    None,
                )?,
                LayoutNode::Curve(ty) => {
                    append(curve_source_name(ty)?, curve_width(ty)?, Some(ty.clone()))?;
                }
                LayoutNode::Tuple(items) => pending.extend(items.iter().rev().copied()),
                LayoutNode::Struct { fields, .. } => {
                    pending.extend(fields.iter().rev().map(|field| field.layout));
                }
                LayoutNode::Vector { length, element } => {
                    for _ in 0..*length {
                        pending.push(*element);
                    }
                }
                LayoutNode::Bytes { length } => {
                    for _ in 0..*length {
                        append("Native".into(), 1, None)?;
                    }
                }
                LayoutNode::Enum { payload, .. } => {
                    for _ in 0..=*payload {
                        append("Native".into(), 1, None)?;
                    }
                }
            }
        }
        ensure!(
            physical_leaves == self.counts().leaves,
            "aggregate source leaf physical count mismatch"
        );
        Ok(result)
    }

    pub(crate) fn source_leaf_types(&self) -> Result<Vec<String>> {
        Ok(self
            .source_leaf_specs()?
            .into_iter()
            .map(|leaf| leaf.type_name)
            .collect())
    }

    pub(crate) fn source_leaf_widths(&self) -> Result<Vec<usize>> {
        Ok(self
            .source_leaf_specs()?
            .into_iter()
            .map(|leaf| leaf.physical_width)
            .collect())
    }

    pub(crate) fn expand_source_leaves_json(
        &self,
        leaves: &[serde_json::Value],
    ) -> Result<Vec<serde_json::Value>> {
        let specs = self.source_leaf_specs()?;
        ensure!(
            leaves.len() == specs.len(),
            "aggregate source leaf count mismatch"
        );
        let mut expanded = Vec::with_capacity(self.counts().leaves);
        for (leaf, spec) in leaves.iter().zip(specs) {
            if let Some(ty) = spec.curve_type {
                ensure!(
                    curve_source_name(&ty)? == spec.type_name,
                    "aggregate curve source type mismatch"
                );
                let value = crate::input_value(&spec.type_name, leaf)?;
                let fields = crate::typed_scalar_fields(&value)?;
                ensure!(
                    fields.len() == spec.physical_width,
                    "aggregate curve encoding width mismatch"
                );
                expanded.extend(
                    fields
                        .into_iter()
                        .map(|field| serde_json::Value::String(crate::field_decimal(field))),
                );
            } else {
                ensure!(
                    spec.physical_width == 1,
                    "non-curve source leaf width mismatch"
                );
                expanded.push(leaf.clone());
            }
        }
        ensure!(
            expanded.len() == self.counts().leaves,
            "aggregate expanded source leaf count mismatch"
        );
        Ok(expanded)
    }

    pub fn flatten_leaves_json(&self, json: &[u8]) -> Result<Vec<serde_json::Value>> {
        let numbers = self.flatten_value(json)?;
        let types = self.leaf_types()?;
        ensure!(
            numbers.len() == types.len(),
            "aggregate leaf type count mismatch"
        );
        numbers
            .into_iter()
            .zip(types)
            .map(|(number, ty)| match ty.as_str() {
                "Native" => Ok(serde_json::Value::String(number.to_str_radix(10))),
                "Bool" => {
                    ensure!(
                        number <= BigUint::from(1u8),
                        "noncanonical aggregate Boolean"
                    );
                    Ok(serde_json::Value::Bool(number == BigUint::from(1u8)))
                }
                _ => Ok(serde_json::Value::String(number.to_str_radix(10))),
            })
            .collect()
    }

    pub fn from_leaf_json(&self, leaves: &[serde_json::Value]) -> Result<Vec<u8>> {
        let types = self.leaf_types()?;
        ensure!(leaves.len() == types.len(), "aggregate leaf count mismatch");
        let modulus = decimal(crate::MODULUS)?;
        let wire_capacity = MAGIC
            .len()
            .checked_add(8)
            .and_then(|size| size.checked_add(self.fingerprint.len()))
            .and_then(|size| size.checked_add(leaves.len().checked_mul(32)?))
            .ok_or_else(|| anyhow!("aggregate wire size overflow"))?;
        ensure!(
            wire_capacity <= MAX_TRANSPORT_BYTES,
            "aggregate wire transport limit exceeded"
        );
        let mut wire = zeroize::Zeroizing::new(Vec::with_capacity(wire_capacity));
        wire.extend_from_slice(MAGIC);
        wire.extend_from_slice(
            &u32::try_from(self.fingerprint.len())
                .map_err(|_| anyhow!("aggregate fingerprint length overflow"))?
                .to_le_bytes(),
        );
        wire.extend_from_slice(self.fingerprint.as_bytes());
        wire.extend_from_slice(
            &u32::try_from(leaves.len())
                .map_err(|_| anyhow!("aggregate leaf count overflow"))?
                .to_le_bytes(),
        );
        for (leaf, ty) in leaves.iter().zip(types) {
            let number = match ty.as_str() {
                "Bool" => BigUint::from(u8::from(
                    leaf.as_bool()
                        .ok_or_else(|| anyhow!("expected aggregate Boolean leaf"))?,
                )),
                _ => {
                    let text = leaf
                        .as_str()
                        .ok_or_else(|| anyhow!("expected aggregate decimal leaf"))?;
                    decimal(text)?
                }
            };
            ensure!(number < modulus, "aggregate leaf outside the native field");
            let mut bytes = zeroize::Zeroizing::new(number.to_bytes_le());
            ensure!(bytes.len() <= 32, "aggregate field leaf too large");
            bytes.resize(32, 0);
            wire.extend_from_slice(&bytes);
        }
        ensure!(
            wire.len() <= MAX_TRANSPORT_BYTES,
            "aggregate wire transport limit exceeded"
        );
        self.decode_wire(&wire)
    }

    pub fn from_native_leaves_json(&self, native_leaves: &[serde_json::Value]) -> Result<Vec<u8>> {
        let types = self.leaf_types()?;
        ensure!(
            native_leaves.len() == types.len(),
            "aggregate native leaf count mismatch"
        );
        let modulus = decimal(crate::MODULUS)?;
        let mut leaves = Vec::with_capacity(types.len());
        for (value, ty) in native_leaves.iter().zip(types) {
            let Some(text) = value.as_str() else {
                leaves.iter_mut().for_each(wipe_leaf_json);
                bail!("expected canonical Native return decimal");
            };
            let number = match decimal(text) {
                Ok(number) if number < modulus => number,
                Ok(_) => {
                    leaves.iter_mut().for_each(wipe_leaf_json);
                    bail!("Native return outside the field");
                }
                Err(error) => {
                    leaves.iter_mut().for_each(wipe_leaf_json);
                    return Err(error);
                }
            };
            if ty == "Bool" {
                if number > BigUint::from(1u8) {
                    leaves.iter_mut().for_each(wipe_leaf_json);
                    bail!("noncanonical aggregate Boolean return");
                }
                leaves.push(serde_json::Value::Bool(number == BigUint::from(1u8)));
            } else {
                leaves.push(serde_json::Value::String(text.to_owned()));
            }
        }
        let rendered = self.from_leaf_json(&leaves);
        leaves.iter_mut().for_each(wipe_leaf_json);
        rendered
    }

    fn node_type_key(&self, root: usize) -> Result<String> {
        enum Task {
            Node(usize),
            Text(String),
        }
        let mut pending = vec![Task::Node(root)];
        let mut output = String::new();
        let mut visits = 0usize;
        while let Some(task) = pending.pop() {
            visits = visits
                .checked_add(1)
                .ok_or_else(|| anyhow!("aggregate type key overflow"))?;
            ensure!(
                visits <= MAX_NODES * 4,
                "aggregate type key traversal limit exceeded"
            );
            match task {
                Task::Text(text) => output.push_str(&text),
                Task::Node(index) => match &self.nodes[index] {
                    LayoutNode::Unit => output.push('u'),
                    LayoutNode::Scalar(Leaf::Native) => output.push_str("sN"),
                    LayoutNode::Scalar(Leaf::Bool) => output.push_str("sB"),
                    LayoutNode::Scalar(Leaf::UInt(maximum)) => {
                        output.push_str(&format!("sU{};", maximum.to_str_radix(10)));
                    }
                    LayoutNode::Curve(ty) => output.push_str(&curve_type_key(ty)?),
                    LayoutNode::Tuple(items) => {
                        output.push_str(&format!("T{}[", items.len()));
                        pending.push(Task::Text("]".to_owned()));
                        for (index, item) in items.iter().enumerate().rev() {
                            pending.push(Task::Node(*item));
                            if index != 0 {
                                pending.push(Task::Text(",".to_owned()));
                            }
                        }
                    }
                    LayoutNode::Struct { id, fields } => {
                        output.push_str(&format!("S{}:{}{{", id.len(), id));
                        pending.push(Task::Text("}".to_owned()));
                        for (index, field) in fields.iter().enumerate().rev() {
                            pending.push(Task::Node(field.layout));
                            pending.push(Task::Text(format!(
                                "{}:{}=",
                                field.name.len(),
                                field.name
                            )));
                            if index != 0 {
                                pending.push(Task::Text(",".to_owned()));
                            }
                        }
                    }
                    LayoutNode::Vector { length, element } => {
                        output.push_str(&format!("V{length}["));
                        pending.push(Task::Node(*element));
                        pending.push(Task::Text("]".to_owned()));
                    }
                    LayoutNode::Bytes { length } => output.push_str(&format!("B{length}")),
                    LayoutNode::Enum {
                        id,
                        variants,
                        payload,
                    } => {
                        output.push_str(&format!("E{}:{}:{payload}{{", id.len(), id));
                        pending.push(Task::Text("}".to_owned()));
                        for (variant_index, variant) in variants.iter().enumerate().rev() {
                            pending.push(Task::Text("}".to_owned()));
                            for (field_index, field) in variant.fields.iter().enumerate().rev() {
                                pending.push(Task::Node(field.layout));
                                pending.push(Task::Text(format!(
                                    "{}:{}=",
                                    field.name.len(),
                                    field.name
                                )));
                                if field_index != 0 {
                                    pending.push(Task::Text(",".to_owned()));
                                }
                            }
                            pending.push(Task::Text(format!(
                                "{}:{}{{",
                                variant.name.len(),
                                variant.name
                            )));
                            if variant_index != 0 {
                                pending.push(Task::Text(",".to_owned()));
                            }
                        }
                    }
                },
            }
            ensure!(
                output.len() <= MAX_TRANSPORT_BYTES,
                "aggregate type key exceeds transport limit"
            );
        }
        Ok(output)
    }

    fn projection_node(&self, projection: &Projection) -> Result<(Option<usize>, usize, String)> {
        let root = &self.nodes[self.root];
        match (projection.kind.as_str(), root) {
            ("tupleIndex", LayoutNode::Tuple(items)) => {
                let index = projection
                    .index
                    .ok_or_else(|| anyhow!("missing aggregate tuple index"))?;
                let child = *items
                    .get(index)
                    .ok_or_else(|| anyhow!("aggregate tuple index out of bounds"))?;
                let offset = items[..index]
                    .iter()
                    .map(|item| self.measures[*item].leaves)
                    .sum();
                Ok((Some(child), offset, self.node_type_key(child)?))
            }
            ("field", LayoutNode::Struct { fields, .. }) => {
                let name = projection
                    .name
                    .as_deref()
                    .ok_or_else(|| anyhow!("missing aggregate field name"))?;
                let index = fields
                    .iter()
                    .position(|field| field.name == name)
                    .ok_or_else(|| anyhow!("unknown aggregate struct field"))?;
                let child = fields[index].layout;
                let offset = fields[..index]
                    .iter()
                    .map(|field| self.measures[field.layout].leaves)
                    .sum();
                Ok((Some(child), offset, self.node_type_key(child)?))
            }
            ("vectorIndex", LayoutNode::Vector { length, element }) => {
                let index = projection
                    .index
                    .ok_or_else(|| anyhow!("missing aggregate vector index"))?;
                ensure!(index < *length, "aggregate vector index out of bounds");
                let offset = index
                    .checked_mul(self.measures[*element].leaves)
                    .ok_or_else(|| anyhow!("aggregate vector offset overflow"))?;
                Ok((Some(*element), offset, self.node_type_key(*element)?))
            }
            ("byteIndex", LayoutNode::Bytes { length }) => {
                let index = projection
                    .index
                    .ok_or_else(|| anyhow!("missing aggregate byte index"))?;
                ensure!(index < *length, "aggregate byte index out of bounds");
                Ok((None, index, "sU255;".to_owned()))
            }
            ("enumTag", LayoutNode::Enum { .. }) => Ok((None, 0, "sN".to_owned())),
            ("enumField", LayoutNode::Enum { variants, .. }) => {
                let variant_name = projection
                    .variant
                    .as_deref()
                    .ok_or_else(|| anyhow!("missing aggregate enum variant"))?;
                let field_name = projection
                    .name
                    .as_deref()
                    .ok_or_else(|| anyhow!("missing aggregate enum field"))?;
                let variant = variants
                    .iter()
                    .find(|variant| variant.name == variant_name)
                    .ok_or_else(|| anyhow!("unknown aggregate enum variant"))?;
                let index = variant
                    .fields
                    .iter()
                    .position(|field| field.name == field_name)
                    .ok_or_else(|| anyhow!("unknown aggregate enum field"))?;
                let child = variant.fields[index].layout;
                let offset = 1 + variant.fields[..index]
                    .iter()
                    .map(|field| self.measures[field.layout].leaves)
                    .sum::<usize>();
                Ok((Some(child), offset, self.node_type_key(child)?))
            }
            _ => bail!("aggregate projection kind and source type mismatch"),
        }
    }

    fn projection_descriptor(&self, projection: &Projection) -> Result<(usize, usize, String)> {
        let (node, start, key) = self.projection_node(projection)?;
        Ok((node.map_or(usize::MAX, |index| index), start, key))
    }

    pub fn projection_type(
        &self,
        projection: &Projection,
    ) -> Result<(String, std::ops::Range<usize>)> {
        let (node, start, key) = self.projection_descriptor(projection)?;
        let count = if node == usize::MAX {
            1
        } else {
            self.measures[node].leaves
        };
        Ok((key, start..start + count))
    }

    pub fn index_projection(&self, index: usize) -> Result<Projection> {
        let kind = match self.nodes[self.root] {
            LayoutNode::Vector { .. } => "vectorIndex",
            LayoutNode::Bytes { .. } => "byteIndex",
            _ => bail!("aggregate indexing requires a vector or bytes"),
        };
        Ok(Projection {
            kind: kind.to_owned(),
            index: Some(index),
            name: None,
            variant: None,
        })
    }

    pub fn indexed_type_key(&self) -> Result<String> {
        match self.nodes[self.root] {
            LayoutNode::Vector { element, .. } => self.node_type_key(element),
            LayoutNode::Bytes { .. } => Ok("sU255;".to_owned()),
            _ => bail!("aggregate indexing requires a vector or bytes"),
        }
    }

    pub fn root_type_key(&self) -> Result<String> {
        self.node_type_key(self.root)
    }

    pub(crate) fn can_widen_to(&self, target: &Self) -> Result<bool> {
        let mut pending = vec![(self.root, target.root)];
        let mut discovered = BTreeSet::from([(self.root, target.root)]);
        while let Some((source, destination)) = pending.pop() {
            ensure!(
                discovered.len() <= MAX_NODES,
                "aggregate widening comparison limit exceeded"
            );
            let compatible = match (&self.nodes[source], &target.nodes[destination]) {
                (LayoutNode::Unit, LayoutNode::Unit)
                | (LayoutNode::Scalar(Leaf::Native), LayoutNode::Scalar(Leaf::Native))
                | (LayoutNode::Scalar(Leaf::Bool), LayoutNode::Scalar(Leaf::Bool)) => true,
                (
                    LayoutNode::Scalar(Leaf::UInt(source)),
                    LayoutNode::Scalar(Leaf::UInt(target)),
                ) => source <= target,
                (LayoutNode::Scalar(Leaf::UInt(_)), LayoutNode::Scalar(Leaf::Native)) => true,
                (LayoutNode::Tuple(source), LayoutNode::Tuple(target))
                    if source.len() == target.len() =>
                {
                    for pair in source.iter().copied().zip(target.iter().copied()) {
                        if discovered.insert(pair) {
                            ensure!(
                                discovered.len() <= MAX_NODES,
                                "aggregate widening comparison limit exceeded"
                            );
                            pending.push(pair);
                        }
                    }
                    true
                }
                (
                    LayoutNode::Vector {
                        length: source_length,
                        element: source_element,
                    },
                    LayoutNode::Vector {
                        length: target_length,
                        element: target_element,
                    },
                ) if source_length == target_length => {
                    let pair = (*source_element, *target_element);
                    if discovered.insert(pair) {
                        ensure!(
                            discovered.len() <= MAX_NODES,
                            "aggregate widening comparison limit exceeded"
                        );
                        pending.push(pair);
                    }
                    true
                }
                (
                    LayoutNode::Bytes {
                        length: source_length,
                    },
                    LayoutNode::Bytes {
                        length: target_length,
                    },
                ) => source_length == target_length,
                (LayoutNode::Struct { .. }, LayoutNode::Struct { .. })
                | (LayoutNode::Enum { .. }, LayoutNode::Enum { .. }) => {
                    self.node_type_key(source)? == target.node_type_key(destination)?
                }
                (LayoutNode::Curve(source), LayoutNode::Curve(target)) => {
                    curve_type_key(source)? == curve_type_key(target)?
                }
                _ => false,
            };
            if !compatible {
                return Ok(false);
            }
        }
        Ok(self.measures[self.root].leaves == target.measures[target.root].leaves)
    }

    pub fn projection_value_json(
        &self,
        json: &[u8],
        projection: &Projection,
    ) -> Result<ProjectedValue> {
        self.project_value_json(json, projection)
    }

    pub fn project_value_json(
        &self,
        json: &[u8],
        projection: &Projection,
    ) -> Result<ProjectedValue> {
        let leaves = self.flatten_value(json)?;
        let (child, start, type_key) = self.projection_node(projection)?;
        let leaf_count = child.map_or(1, |index| self.measures[index].leaves);
        ensure!(
            start
                .checked_add(leaf_count)
                .is_some_and(|end| end <= leaves.len()),
            "aggregate projection range outside value"
        );
        let selected_json = if projection.kind == "enumTag" {
            let tag = leaves
                .get(start)
                .ok_or_else(|| anyhow!("missing aggregate enum tag"))?;
            serde_json::json!({"kind":"native","value":tag.to_str_radix(10)})
        } else if projection.kind == "byteIndex" {
            let value: serde_json::Value = serde_json::from_slice(json)?;
            let index = projection
                .index
                .ok_or_else(|| anyhow!("missing aggregate byte index"))?;
            let number = value
                .get("values")
                .and_then(serde_json::Value::as_array)
                .and_then(|items| items.get(index))
                .and_then(serde_json::Value::as_u64)
                .ok_or_else(|| anyhow!("invalid aggregate byte value"))?;
            serde_json::json!({"kind":"uint","maximum":"255","value":number.to_string()})
        } else {
            let value: serde_json::Value = serde_json::from_slice(json)?;
            let index = projection.index;
            match projection.kind.as_str() {
                "tupleIndex" => {
                    let index = index.ok_or_else(|| anyhow!("missing tuple index"))?;
                    value
                        .get("items")
                        .and_then(serde_json::Value::as_array)
                        .and_then(|items| items.get(index))
                        .cloned()
                        .ok_or_else(|| anyhow!("invalid aggregate tuple value"))?
                }
                "vectorIndex" => {
                    let index = index.ok_or_else(|| anyhow!("missing vector index"))?;
                    value
                        .get("items")
                        .and_then(serde_json::Value::as_array)
                        .and_then(|items| items.get(index))
                        .cloned()
                        .ok_or_else(|| anyhow!("invalid aggregate vector value"))?
                }
                "field" | "enumField" => {
                    let fields = value
                        .get("fields")
                        .and_then(serde_json::Value::as_array)
                        .ok_or_else(|| anyhow!("invalid aggregate fields"))?;
                    let name = projection
                        .name
                        .as_deref()
                        .ok_or_else(|| anyhow!("missing field name"))?;
                    if projection.kind == "enumField" {
                        ensure!(
                            value.get("variant").and_then(serde_json::Value::as_str)
                                == projection.variant.as_deref(),
                            "aggregate enum variant mismatch"
                        );
                    }
                    fields
                        .iter()
                        .find(|field| {
                            field.get("name").and_then(serde_json::Value::as_str) == Some(name)
                        })
                        .and_then(|field| field.get("value"))
                        .cloned()
                        .ok_or_else(|| anyhow!("unknown aggregate field value"))?
                }
                _ => bail!("unsupported aggregate projection"),
            }
        };
        let encoded = serde_json::to_vec(&selected_json)?;
        Ok(ProjectedValue {
            value: encoded,
            leaf_range: start..start + leaf_count,
            type_key,
        })
    }
    pub fn encode_json_value(&self, json: &[u8]) -> Result<Vec<u8>> {
        let leaves = self.flatten_value(json)?;
        let mut output =
            Vec::with_capacity(MAGIC.len() + 8 + self.fingerprint.len() + leaves.len() * 32);
        output.extend_from_slice(MAGIC);
        output.extend_from_slice(&(self.fingerprint.len() as u32).to_le_bytes());
        output.extend_from_slice(self.fingerprint.as_bytes());
        output.extend_from_slice(&(leaves.len() as u32).to_le_bytes());
        for leaf in leaves {
            let mut bytes = leaf.to_bytes_le();
            bytes.resize(32, 0);
            output.extend_from_slice(&bytes);
            bytes.zeroize();
        }
        ensure!(
            output.len() <= MAX_TRANSPORT_BYTES,
            "aggregate wire transport limit exceeded"
        );
        Ok(output)
    }
    pub fn decode_wire(&self, wire: &[u8]) -> Result<Vec<u8>> {
        ensure!(
            wire.len() <= MAX_TRANSPORT_BYTES && wire.starts_with(MAGIC),
            "invalid aggregate wire header"
        );
        let mut at = MAGIC.len();
        let fingerprint_length = read_u32(wire, &mut at)?;
        let end = at
            .checked_add(fingerprint_length)
            .ok_or_else(|| anyhow!("aggregate wire length overflow"))?;
        ensure!(
            wire.get(at..end) == Some(self.fingerprint.as_bytes()),
            "aggregate wire type fingerprint mismatch"
        );
        at = end;
        let count = read_u32(wire, &mut at)?;
        ensure!(
            count == self.counts().leaves && count <= MAX_LEAVES,
            "aggregate wire leaf count mismatch"
        );
        ensure!(
            wire.len() == add(at, mul(count, 32)?)?,
            "truncated or trailing aggregate wire data"
        );
        let modulus = decimal(crate::MODULUS)?;
        let mut leaves = Vec::with_capacity(count);
        for chunk in wire[at..].chunks_exact(32) {
            let number = BigUint::from_bytes_le(chunk);
            ensure!(number < modulus, "noncanonical aggregate field bytes");
            leaves.push(number);
        }
        self.render_value(&leaves)
    }
    fn render_value(&self, leaves: &[BigUint]) -> Result<Vec<u8>> {
        enum Task {
            Visit(usize),
            Text(String),
            Pad(usize),
        }
        let mut pending = vec![Task::Visit(self.root)];
        let mut output = Vec::new();
        let mut cursor = 0;
        while let Some(task) = pending.pop() {
            match task {
                Task::Text(text) => output.extend_from_slice(text.as_bytes()),
                Task::Pad(count) => {
                    let end = add(cursor, count)?;
                    ensure!(
                        leaves.get(cursor..end).is_some_and(|values| values
                            .iter()
                            .all(|value| *value == BigUint::from(0u8))),
                        "nonzero inactive aggregate enum padding"
                    );
                    cursor = end;
                }
                Task::Visit(layout) => match &self.nodes[layout] {
                    LayoutNode::Unit => output.extend_from_slice(b"{\"kind\":\"unit\"}"),
                    LayoutNode::Scalar(leaf) => {
                        let number = leaves
                            .get(cursor)
                            .ok_or_else(|| anyhow!("truncated aggregate leaves"))?;
                        cursor += 1;
                        ensure!(
                            *number <= scalar_maximum(leaf),
                            "aggregate scalar outside declared range"
                        );
                        let text = match leaf {
                            Leaf::Native => format!(
                                "{{\"kind\":\"native\",\"value\":\"{}\"}}",
                                number.to_str_radix(10)
                            ),
                            Leaf::Bool => format!(
                                "{{\"kind\":\"bool\",\"value\":{}}}",
                                *number == BigUint::from(1u8)
                            ),
                            Leaf::UInt(maximum) => format!(
                                "{{\"kind\":\"uint\",\"maximum\":\"{}\",\"value\":\"{}\"}}",
                                maximum.to_str_radix(10),
                                number.to_str_radix(10)
                            ),
                        };
                        output.extend_from_slice(text.as_bytes());
                    }
                    LayoutNode::Curve(ty) => {
                        let width = curve_width(ty)?;
                        let end = add(cursor, width)?;
                        let fields = leaves
                            .get(cursor..end)
                            .ok_or_else(|| anyhow!("truncated aggregate curve leaves"))?
                            .iter()
                            .map(|number| crate::canonical_field(&number.to_str_radix(10)))
                            .collect::<Result<Vec<_>>>()?;
                        let value = crate::decode_typed_scalar(ty, &fields)?;
                        cursor = end;
                        output.extend_from_slice(&serde_json::to_vec(&value.public_json())?);
                    }
                    LayoutNode::Tuple(items) => {
                        output.extend_from_slice(b"{\"kind\":\"tuple\",\"items\":[");
                        pending.push(Task::Text("]}".into()));
                        for (index, child) in items.iter().enumerate().rev() {
                            pending.push(Task::Visit(*child));
                            if index != 0 {
                                pending.push(Task::Text(",".into()));
                            }
                        }
                    }
                    LayoutNode::Struct { id, fields } => {
                        output.extend_from_slice(
                            format!("{{\"kind\":\"struct\",\"id\":{},\"fields\":[", quoted(id)?)
                                .as_bytes(),
                        );
                        push_fields(
                            &mut pending,
                            fields,
                            |text| Task::Text(text),
                            |layout| Task::Visit(layout),
                        )?;
                    }
                    LayoutNode::Vector { length, element } => {
                        output.extend_from_slice(b"{\"kind\":\"vector\",\"items\":[");
                        pending.push(Task::Text("]}".into()));
                        for index in (0..*length).rev() {
                            pending.push(Task::Visit(*element));
                            if index != 0 {
                                pending.push(Task::Text(",".into()));
                            }
                        }
                    }
                    LayoutNode::Bytes { length } => {
                        output.extend_from_slice(b"{\"kind\":\"bytes\",\"values\":[");
                        for index in 0..*length {
                            if index != 0 {
                                output.push(b',');
                            }
                            let number = leaves
                                .get(cursor)
                                .ok_or_else(|| anyhow!("truncated aggregate byte leaves"))?;
                            ensure!(
                                *number <= BigUint::from(255u16),
                                "aggregate byte out of range"
                            );
                            cursor += 1;
                            output.extend_from_slice(number.to_str_radix(10).as_bytes());
                        }
                        output.extend_from_slice(b"]}");
                    }
                    LayoutNode::Enum {
                        id,
                        variants,
                        payload,
                    } => {
                        let number = leaves
                            .get(cursor)
                            .ok_or_else(|| anyhow!("missing aggregate enum tag"))?;
                        cursor += 1;
                        let tag = number.to_u64_digits();
                        ensure!(tag.len() <= 1, "aggregate enum tag out of range");
                        let tag = tag.first().copied().unwrap_or(0);
                        let variant = variants
                            .get(
                                usize::try_from(tag)
                                    .map_err(|_| anyhow!("aggregate enum tag out of range"))?,
                            )
                            .ok_or_else(|| anyhow!("aggregate enum tag out of range"))?;
                        output.extend_from_slice(
                            format!(
                                "{{\"kind\":\"enum\",\"id\":{},\"variant\":{},\"fields\":[",
                                quoted(id)?,
                                quoted(&variant.name)?
                            )
                            .as_bytes(),
                        );
                        pending.push(Task::Pad(payload - variant.leaves));
                        push_fields(
                            &mut pending,
                            &variant.fields,
                            |text| Task::Text(text),
                            |layout| Task::Visit(layout),
                        )?;
                    }
                },
            }
            ensure!(
                output.len() <= MAX_TRANSPORT_BYTES,
                "aggregate JSON output transport limit exceeded"
            );
        }
        ensure!(
            cursor == leaves.len(),
            "aggregate decoded leaf count mismatch"
        );
        Ok(output)
    }
}

fn wipe_leaf_json(value: &mut serde_json::Value) {
    match value {
        serde_json::Value::String(value) => value.zeroize(),
        serde_json::Value::Bool(value) => *value = false,
        _ => {}
    }
}
fn value_fields(tree: &JsonTree, raw: usize, fields: &[Field]) -> Result<Vec<usize>> {
    let values = tree.items(raw, "fields")?;
    ensure!(
        values.len() == fields.len(),
        "aggregate field arity mismatch"
    );
    values
        .iter()
        .zip(fields)
        .map(|(value, field)| {
            tree.exact(*value, &["name", "value"])?;
            ensure!(
                tree.text(*value, "name")? == field.name,
                "aggregate field name/order mismatch"
            );
            tree.field(*value, "value")
        })
        .collect()
}
fn quoted(value: &str) -> Result<String> {
    serde_json::to_string(value).map_err(|_| anyhow!("aggregate string encoding failed"))
}
fn push_fields<T>(
    pending: &mut Vec<T>,
    fields: &[Field],
    text: impl Fn(String) -> T,
    visit: impl Fn(usize) -> T,
) -> Result<()> {
    pending.push(text("]}".into()));
    for (index, field) in fields.iter().enumerate().rev() {
        pending.push(text("}".into()));
        pending.push(visit(field.layout));
        pending.push(text(format!(
            "{{\"name\":{},\"value\":",
            quoted(&field.name)?
        )));
        if index != 0 {
            pending.push(text(",".into()));
        }
    }
    Ok(())
}
fn read_u32(bytes: &[u8], at: &mut usize) -> Result<usize> {
    let end = add(*at, 4)?;
    let part: [u8; 4] = bytes
        .get(*at..end)
        .ok_or_else(|| anyhow!("truncated aggregate wire header"))?
        .try_into()
        .map_err(|_| anyhow!("truncated aggregate wire header"))?;
    *at = end;
    Ok(u32::from_le_bytes(part) as usize)
}

// This buffer namespace is independent from session/public/private runtime tokens.
// Returned bytes contain caller values and must not be logged or published.
const OK: i32 = 0;
const INVALID_ARGUMENT: i32 = 1;
const INVALID_HANDLE: i32 = 2;
const LIMIT: i32 = 5;
const INTERNAL: i32 = 6;
const BUFFER_TOO_SMALL: i32 = 7;
const MAX_BUFFERS: usize = 64;
struct Buffers {
    next: u64,
    data: BTreeMap<u64, Vec<u8>>,
}
static BUFFERS: OnceLock<Mutex<Buffers>> = OnceLock::new();
fn buffers() -> std::sync::MutexGuard<'static, Buffers> {
    BUFFERS
        .get_or_init(|| {
            Mutex::new(Buffers {
                next: 0x4147_0000_0000_0001,
                data: BTreeMap::new(),
            })
        })
        .lock()
        .unwrap_or_else(|poison| poison.into_inner())
}
fn guard(operation: impl FnOnce() -> std::result::Result<(), i32>) -> i32 {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(operation)) {
        Ok(Ok(())) => OK,
        Ok(Err(code)) => code,
        Err(_) => INTERNAL,
    }
}
unsafe fn bytes<'a>(pointer: *const u8, length: usize) -> std::result::Result<&'a [u8], i32> {
    if pointer.is_null() || length == 0 {
        return Err(INVALID_ARGUMENT);
    }
    if length > MAX_TRANSPORT_BYTES {
        return Err(LIMIT);
    }
    Ok(unsafe { std::slice::from_raw_parts(pointer, length) })
}
unsafe fn clear<T: Default>(pointer: *mut T) -> std::result::Result<(), i32> {
    if pointer.is_null() {
        return Err(INVALID_ARGUMENT);
    }
    unsafe {
        pointer.write(T::default());
    }
    Ok(())
}
fn store(mut value: Vec<u8>) -> std::result::Result<u64, i32> {
    let mut registry = buffers();
    if registry.data.len() >= MAX_BUFFERS {
        value.zeroize();
        return Err(LIMIT);
    }
    let token = registry.next;
    let Some(next) = registry.next.checked_add(1) else {
        value.zeroize();
        return Err(LIMIT);
    };
    registry.next = next;
    registry.data.insert(token, value);
    Ok(token)
}
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub extern "C" fn noctium_aggregate_abi_version() -> u32 {
    1
}
/// # Safety
/// Borrowed inputs must be readable and output must be aligned writable storage, without overlap.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_aggregate_encode(
    schema: *const u8,
    schema_length: usize,
    value: *const u8,
    value_length: usize,
    out_buffer: *mut u64,
) -> i32 {
    guard(|| {
        unsafe {
            clear(out_buffer)?;
        }
        let schema = Schema::from_json(unsafe { bytes(schema, schema_length)? })
            .map_err(|_| INVALID_ARGUMENT)?;
        let wire = schema
            .encode_json_value(unsafe { bytes(value, value_length)? })
            .map_err(|_| INVALID_ARGUMENT)?;
        let token = store(wire)?;
        unsafe {
            out_buffer.write(token);
        }
        Ok(())
    })
}
/// # Safety
/// Borrowed inputs must be readable and output must be aligned writable storage, without overlap.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_aggregate_decode(
    schema: *const u8,
    schema_length: usize,
    wire: *const u8,
    wire_length: usize,
    out_buffer: *mut u64,
) -> i32 {
    guard(|| {
        unsafe {
            clear(out_buffer)?;
        }
        let schema = Schema::from_json(unsafe { bytes(schema, schema_length)? })
            .map_err(|_| INVALID_ARGUMENT)?;
        let json = schema
            .decode_wire(unsafe { bytes(wire, wire_length)? })
            .map_err(|_| INVALID_ARGUMENT)?;
        let token = store(json)?;
        unsafe {
            out_buffer.write(token);
        }
        Ok(())
    })
}
/// # Safety
/// out_length must be aligned writable storage for one size_t.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_aggregate_buffer_length(
    token: u64,
    out_length: *mut usize,
) -> i32 {
    guard(|| {
        unsafe {
            clear(out_length)?;
        }
        let registry = buffers();
        let value = registry.data.get(&token).ok_or(INVALID_HANDLE)?;
        unsafe {
            out_length.write(value.len());
        }
        Ok(())
    })
}
/// # Safety
/// Output storage must be writable, aligned and nonoverlapping. No partial copies are performed.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_aggregate_buffer_copy(
    token: u64,
    destination: *mut u8,
    capacity: usize,
    out_written: *mut usize,
) -> i32 {
    guard(|| {
        unsafe {
            clear(out_written)?;
        }
        let registry = buffers();
        let value = registry.data.get(&token).ok_or(INVALID_HANDLE)?;
        if capacity < value.len() {
            return Err(BUFFER_TOO_SMALL);
        }
        if destination.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        unsafe {
            std::ptr::copy_nonoverlapping(value.as_ptr(), destination, value.len());
            out_written.write(value.len());
        }
        Ok(())
    })
}
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub extern "C" fn noctium_aggregate_buffer_free(token: u64) -> i32 {
    guard(|| {
        let mut value = buffers().data.remove(&token).ok_or(INVALID_HANDLE)?;
        value.zeroize();
        Ok(())
    })
}

#[cfg(test)]
mod tests {
    use super::Schema;
    use serde_json::{Value as Json, json};

    #[test]
    fn native_returns_reconstruct_typed_aggregate_and_reject_invalid_leaves() {
        let schema = Schema::from_json(
            br#"{"schemaVersion":1,"typeFingerprint":"NoctiumCompositeTypeV1;t2;[sBsU10;]NoctiumCompositeLayoutV1;0;0;","layout":{"kind":"tuple","items":[{"kind":"scalar","leaf":{"kind":"bool"}},{"kind":"scalar","leaf":{"kind":"uint","maximum":"10"}}]},"counts":{"leaves":2,"expandedNodes":3,"layoutNodes":3}}"#,
        )
        .unwrap();
        let rendered = schema
            .from_native_leaves_json(&[json!("1"), json!("8")])
            .unwrap();
        let value: Json = serde_json::from_slice(&rendered).unwrap();
        assert_eq!(
            value,
            json!({"kind":"tuple","items":[
                {"kind":"bool","value":true},
                {"kind":"uint","maximum":"10","value":"8"}
            ]})
        );
        assert!(
            schema
                .from_native_leaves_json(&[json!("2"), json!("8")])
                .is_err()
        );
        assert!(
            schema
                .from_native_leaves_json(&[json!("1"), json!("11")])
                .is_err()
        );

        for (schema_json, expected) in [
            (
                br#"{"schemaVersion":1,"typeFingerprint":"NoctiumCompositeTypeV1;uNoctiumCompositeLayoutV1;0;0;","layout":{"kind":"unit"},"counts":{"leaves":0,"expandedNodes":1,"layoutNodes":1}}"#.as_slice(),
                json!({"kind":"unit"}),
            ),
            (
                br#"{"schemaVersion":1,"typeFingerprint":"NoctiumCompositeTypeV1;t0;[]NoctiumCompositeLayoutV1;0;0;","layout":{"kind":"tuple","items":[]},"counts":{"leaves":0,"expandedNodes":1,"layoutNodes":1}}"#.as_slice(),
                json!({"kind":"tuple","items":[]}),
            ),
        ] {
            let schema = Schema::from_json(schema_json).unwrap();
            let rendered = schema.from_native_leaves_json(&[]).unwrap();
            let value: Json = serde_json::from_slice(&rendered).unwrap();
            assert_eq!(value, expected);
        }
    }

    #[test]
    fn typed_curves_flatten_reconstruct_and_reject_invalid_encodings() {
        let schema = Schema::from_json(
            br#"{"schemaVersion":1,"typeFingerprint":"NoctiumCompositeTypeV1;t2;[sJSsJP]NoctiumCompositeLayoutV1;0;0;","layout":{"kind":"tuple","items":[{"kind":"curve","type":"JubjubScalar"},{"kind":"curve","type":"JubjubPoint"}]},"counts":{"leaves":3,"expandedNodes":6,"layoutNodes":3}}"#,
        )
        .unwrap();
        assert_eq!(
            schema.leaf_types().unwrap(),
            vec![
                "Native".to_owned(),
                "Native".to_owned(),
                "Native".to_owned()
            ]
        );
        let value = json!({
            "kind":"tuple",
            "items":[
                {"kind":"jubjubScalar","value":"7"},
                {"kind":"jubjubPoint","x":"0","y":"1"}
            ]
        });
        let json = serde_json::to_vec(&value).unwrap();
        assert_eq!(
            schema.flatten_leaves_json(&json).unwrap(),
            vec![json!("7"), json!("0"), json!("1")]
        );
        let wire = schema.encode_json_value(&json).unwrap();
        let decoded: Json = serde_json::from_slice(&schema.decode_wire(&wire).unwrap()).unwrap();
        assert_eq!(decoded, value);
        let from_native: Json = serde_json::from_slice(
            &schema
                .from_native_leaves_json(&[json!("7"), json!("0"), json!("1")])
                .unwrap(),
        )
        .unwrap();
        assert_eq!(from_native, value);

        let invalid_point = json!({
            "kind":"tuple",
            "items":[
                {"kind":"jubjubScalar","value":"7"},
                {"kind":"jubjubPoint","x":"0","y":"0"}
            ]
        });
        assert!(
            schema
                .validate_value_json(&serde_json::to_vec(&invalid_point).unwrap())
                .is_err()
        );
        let mut invalid_wire = wire;
        let last_field = invalid_wire.len() - 32;
        invalid_wire[last_field..].fill(0);
        assert!(schema.decode_wire(&invalid_wire).is_err());

        let wrong_curve_type = br#"{"schemaVersion":1,"typeFingerprint":"NoctiumCompositeTypeV1;sNNoctiumCompositeLayoutV1;0;0;","layout":{"kind":"curve","type":"Native"},"counts":{"leaves":1,"expandedNodes":2,"layoutNodes":1}}"#;
        assert!(Schema::from_json(wrong_curve_type).is_err());
    }
}
