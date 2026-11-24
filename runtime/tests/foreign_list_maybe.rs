#![cfg(feature = "zkir-321")]

use anyhow::{Context, Result};
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::foreign::{
    ForeignFamily, ForeignRole, ForeignType, ForeignUnaryOp, ForeignValue,
};
use noctium_runtime::{Expr, Plan, Value, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};

#[derive(Clone, Copy)]
struct ForeignListCase {
    input: &'static str,
    maybe: &'static str,
    type_name: &'static str,
    ty: ForeignType,
}

const CASES: [ForeignListCase; 9] = [
    ForeignListCase {
        input: "secp256k1Base",
        maybe: "maybeSecp256k1Base",
        type_name: "Secp256k1Base",
        ty: ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Base),
    },
    ForeignListCase {
        input: "secp256k1Scalar",
        maybe: "maybeSecp256k1Scalar",
        type_name: "Secp256k1Scalar",
        ty: ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Scalar),
    },
    ForeignListCase {
        input: "secp256k1Point",
        maybe: "maybeSecp256k1Point",
        type_name: "Secp256k1Point",
        ty: ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Point),
    },
    ForeignListCase {
        input: "secp256r1Base",
        maybe: "maybeSecp256r1Base",
        type_name: "Secp256r1Base",
        ty: ForeignType::new(ForeignFamily::Secp256r1, ForeignRole::Base),
    },
    ForeignListCase {
        input: "secp256r1Scalar",
        maybe: "maybeSecp256r1Scalar",
        type_name: "Secp256r1Scalar",
        ty: ForeignType::new(ForeignFamily::Secp256r1, ForeignRole::Scalar),
    },
    ForeignListCase {
        input: "secp256r1Point",
        maybe: "maybeSecp256r1Point",
        type_name: "Secp256r1Point",
        ty: ForeignType::new(ForeignFamily::Secp256r1, ForeignRole::Point),
    },
    ForeignListCase {
        input: "curve25519Base",
        maybe: "maybeCurve25519Base",
        type_name: "Curve25519Base",
        ty: ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Base),
    },
    ForeignListCase {
        input: "curve25519Scalar",
        maybe: "maybeCurve25519Scalar",
        type_name: "Curve25519Scalar",
        ty: ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Scalar),
    },
    ForeignListCase {
        input: "curve25519Point",
        maybe: "maybeCurve25519Point",
        type_name: "Curve25519Point",
        ty: ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Point),
    },
];

fn value(case: ForeignListCase) -> Result<ForeignValue> {
    match case.ty.role() {
        ForeignRole::Base | ForeignRole::Scalar => {
            let mut bytes = vec![0; case.ty.byte_len()];
            bytes[0] = 7;
            Ok(ForeignValue::from_bytes(case.ty, &bytes)?)
        }
        ForeignRole::Point => {
            let scalar_type = ForeignType::new(case.ty.family(), ForeignRole::Scalar);
            ForeignValue::from_bytes_reducing(scalar_type, &[1])?
                .unary(ForeignUnaryOp::MulGenerator)
        }
    }
}

fn alternate_value(case: ForeignListCase) -> Result<ForeignValue> {
    match case.ty.role() {
        ForeignRole::Base | ForeignRole::Scalar => {
            Ok(ForeignValue::from_bytes_reducing(case.ty, &[8])?)
        }
        ForeignRole::Point => {
            let scalar_type = ForeignType::new(case.ty.family(), ForeignRole::Scalar);
            ForeignValue::from_bytes_reducing(scalar_type, &[2])?
                .unary(ForeignUnaryOp::MulGenerator)
        }
    }
}

fn inputs(values: &BTreeMap<&'static str, ForeignValue>) -> BTreeMap<String, Json> {
    CASES
        .iter()
        .map(|case| {
            (
                case.input.to_owned(),
                Value::Foreign(values[case.input].clone()).public_json(),
            )
        })
        .collect()
}

fn maybe_fields(present: bool, value: Json) -> Json {
    json!([
        {"name":"is_some", "value":{"kind":"bool", "value":present}},
        {"name":"value", "value":value},
    ])
}

fn assert_maybe(
    returns: &BTreeMap<String, Json>,
    case: ForeignListCase,
    present: bool,
    value: Json,
) {
    assert_eq!(
        returns[case.maybe]["fields"],
        maybe_fields(present, value),
        "wrong typed Maybe result for {}",
        case.type_name,
    );
}

fn load(directory: &PathBuf, entry: &str) -> Result<(Plan, IrSource)> {
    let stem = format!("ForeignListMaybe.{entry}");
    Ok((
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json")))?)?,
        IrSource::load(fs::File::open(directory.join(format!("{stem}.zkir")))?)?,
    ))
}

#[test]
#[ignore = "requires fresh ForeignListMaybe artifacts in NOCTIUM_FOREIGN_LIST_MAYBE_DIR"]
fn foreign_list_heads_return_typed_maybe_for_every_kind() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_FOREIGN_LIST_MAYBE_DIR")?);
    let (head, head_circuit) = load(&directory, "head")?;
    let (push, push_circuit) = load(&directory, "push")?;
    let (pop, pop_circuit) = load(&directory, "pop")?;
    let initial_values: BTreeMap<_, _> = head
        .state
        .iter()
        .map(|decl| (decl.name.clone(), json!([])))
        .collect();
    let empty = create_state(&head, &initial_values)?;
    let address = ContractAddress::default();
    let values: BTreeMap<_, _> = CASES
        .iter()
        .map(|case| Ok((case.input, value(*case)?)))
        .collect::<Result<_>>()?;
    let private_inputs = inputs(&values);

    let absent = prepare(
        &head,
        &BTreeMap::new(),
        &empty,
        &INITIAL_PARAMETERS,
        address,
    )
    .context("preparing absent foreign List heads")?;
    check(&absent, &head_circuit).context("checking absent foreign List heads")?;
    let absent_returns = absent.returns_json();
    for case in CASES {
        let zero = Value::Foreign(ForeignValue::zero(case.ty)?).public_json();
        assert_maybe(&absent_returns, case, false, zero);
    }

    let pushed = prepare(&push, &private_inputs, &empty, &INITIAL_PARAMETERS, address)
        .context("preparing foreign List pushes")?;
    check(&pushed, &push_circuit).context("checking foreign List pushes")?;
    let present = prepare(
        &head,
        &BTreeMap::new(),
        &pushed.after.state,
        &INITIAL_PARAMETERS,
        address,
    )
    .context("preparing present foreign List heads")?;
    check(&present, &head_circuit).context("checking present foreign List heads")?;
    let present_returns = present.returns_json();
    for case in CASES {
        assert_maybe(
            &present_returns,
            case,
            true,
            Value::Foreign(values[case.input].clone()).public_json(),
        );

        let mut changed_head = head.clone();
        let output_prefix = format!("{}_value_", case.maybe);
        let encoded = alternate_value(case)?
            .encode()?
            .into_iter()
            .map(noctium_runtime::field_decimal);
        let mut encoded = encoded;
        for output in changed_head
            .returns
            .iter_mut()
            .filter(|output| output.name.starts_with(&output_prefix))
        {
            output.expression = Expr::Constant {
                value: encoded
                    .next()
                    .expect("foreign Maybe has one output per encoded field"),
            };
        }
        assert!(
            encoded.next().is_none(),
            "foreign Maybe has exactly one output per encoded field"
        );
        let changed = prepare(
            &changed_head,
            &BTreeMap::new(),
            &pushed.after.state,
            &INITIAL_PARAMETERS,
            address,
        )
        .context("preparing changed foreign return")?;
        assert!(
            check(&changed, &head_circuit).is_err(),
            "native relation accepted a changed field for {}",
            case.type_name,
        );
    }

    let identity_values: BTreeMap<_, _> = CASES
        .iter()
        .map(|case| {
            let value = if case.ty.role() == ForeignRole::Point {
                ForeignValue::zero(case.ty)?
            } else {
                values[case.input].clone()
            };
            Ok((case.input, value))
        })
        .collect::<Result<_>>()?;
    let identity_push = prepare(
        &push,
        &inputs(&identity_values),
        &empty,
        &INITIAL_PARAMETERS,
        address,
    )
    .context("preparing foreign identity List pushes")?;
    check(&identity_push, &push_circuit).context("checking foreign identity List pushes")?;
    let identity_present = prepare(
        &head,
        &BTreeMap::new(),
        &identity_push.after.state,
        &INITIAL_PARAMETERS,
        address,
    )
    .context("preparing present foreign point identities")?;
    check(&identity_present, &head_circuit).context("checking present foreign point identities")?;
    let identity_returns = identity_present.returns_json();
    for case in CASES
        .into_iter()
        .filter(|case| case.ty.role() == ForeignRole::Point)
    {
        assert_maybe(
            &identity_returns,
            case,
            true,
            Value::Foreign(identity_values[case.input].clone()).public_json(),
        );
    }

    let removed = prepare(
        &pop,
        &BTreeMap::new(),
        &pushed.after.state,
        &INITIAL_PARAMETERS,
        address,
    )
    .context("preparing foreign List pops")?;
    check(&removed, &pop_circuit).context("checking foreign List pops")?;
    let post_pop = prepare(
        &head,
        &BTreeMap::new(),
        &removed.after.state,
        &INITIAL_PARAMETERS,
        address,
    )
    .context("preparing absent heads after pop")?;
    check(&post_pop, &head_circuit).context("checking absent foreign List heads after pop")?;
    let post_pop_returns = post_pop.returns_json();
    for case in CASES {
        let zero = Value::Foreign(ForeignValue::zero(case.ty)?).public_json();
        assert_maybe(&post_pop_returns, case, false, zero);
    }

    Ok(())
}
