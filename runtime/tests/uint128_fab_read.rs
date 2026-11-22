#![cfg(feature = "zkir-321")]

use anyhow::Result;
use base_crypto::fab::AlignedValue;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    Db, Expr, Instruction, Plan, Program, check, constructor::construct_state, create_state,
    field_value, prepare, zkir::IrSource,
};
use onchain_runtime::{
    context::QueryContext,
    error::TranscriptRejected,
    ops::Op,
    state::{ChargedState, StateValue},
    vm_error::OnchainProgramError,
};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use storage::arena::Sp;
use transient_crypto::{curve::Fr, fab::AlignmentExt};

#[test]
fn ledger_popeq_binds_the_full_uint128_atom() {
    let max_uint = Fr::from(u128::MAX);
    let oversized_uint = max_uint + Fr::from(1u64);
    let expected = AlignedValue::from(u128::MAX);
    assert_eq!(
        expected.alignment.parse_field_repr(&[max_uint]),
        Some(expected.clone())
    );
    assert!(
        expected
            .alignment
            .parse_field_repr(&[oversized_uint])
            .is_none()
    );

    let program: Program = vec![
        Op::Dup { n: 0 },
        Op::Popeq {
            cached: false,
            result: expected.clone(),
        },
    ];
    let check = |value| {
        let state = ChargedState::<Db>::new(StateValue::Cell(Sp::new(value)));
        QueryContext::new(state, ContractAddress::default()).query(
            &program,
            None,
            &INITIAL_PARAMETERS.cost_model.runtime_cost_model,
        )
    };
    assert!(check(expected).is_ok());
    for invalid in [field_value(max_uint), field_value(oversized_uint)] {
        assert!(matches!(
            check(invalid),
            Err(TranscriptRejected::Execution(
                OnchainProgramError::ReadMismatch { .. }
            ))
        ));
    }
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_BYTE_ALIGNED_UINT128_CELL_DIR"]
fn source_uint128_cell_uses_one_sixteen_byte_atom() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_BYTE_ALIGNED_UINT128_CELL_DIR")?);
    let stem = "ByteAlignedUInt128Cell.update";
    let plan: Plan =
        serde_json::from_reader(File::open(directory.join(format!("{stem}.impact.json")))?)?;
    let circuit = IrSource::load(File::open(directory.join(format!("{stem}.zkir")))?)?;
    assert_eq!(plan.state[0].name, "totalSupply");
    assert_eq!(plan.state[0].cell_alignment.as_deref(), Some("u128"));
    assert_eq!(plan.state[1].name, "ordinary");
    assert!(plan.state[1].cell_alignment.is_none());

    let assert_cells = |state: &ChargedState<Db>, supply: u128, ordinary: Fr| {
        let StateValue::Array(cells) = state.get_ref() else {
            panic!("expected the contract state array");
        };
        for (slot, expected) in [AlignedValue::from(supply), field_value(ordinary)]
            .iter()
            .enumerate()
        {
            let StateValue::Cell(actual) = cells.get(slot).unwrap() else {
                panic!("expected direct Cell");
            };
            assert_eq!(&**actual, expected);
        }
    };
    let initial = construct_state(&plan, &BTreeMap::new())?;
    assert_cells(&initial, 0, Fr::from(0u64));
    let explicit = create_state(
        &plan,
        &BTreeMap::from([
            ("totalSupply".into(), json!(u128::MAX.to_string())),
            ("ordinary".into(), json!("9")),
        ]),
    )?;
    assert_cells(&explicit, u128::MAX, Fr::from(9u64));

    let address = ContractAddress::default();
    let mut state = initial;
    for (previous, amount) in [(0u128, u128::MAX), (u128::MAX, 0u128)] {
        let execution = prepare(
            &plan,
            &BTreeMap::from([
                ("amount".into(), json!(amount.to_string())),
                ("enabled".into(), json!(true)),
            ]),
            &state,
            &INITIAL_PARAMETERS,
            address,
        )?;
        check(&execution, &circuit)?;
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([
                ("previousAmount".into(), json!(previous.to_string())),
                ("currentAmount".into(), json!(amount.to_string())),
            ])
        );
        assert_cells(&execution.after.state, amount, Fr::from(0u64));
        state = execution.after.state;
    }

    let inactive = prepare(
        &plan,
        &BTreeMap::from([
            ("amount".into(), json!("7")),
            ("enabled".into(), json!(false)),
        ]),
        &explicit,
        &INITIAL_PARAMETERS,
        address,
    )?;
    check(&inactive, &circuit)?;
    assert_eq!(
        inactive.returns_json(),
        BTreeMap::from([
            ("previousAmount".into(), json!(u128::MAX.to_string())),
            ("currentAmount".into(), json!("0")),
        ])
    );
    assert_cells(&inactive.after.state, u128::MAX, Fr::from(9u64));

    let mut forged = plan.clone();
    let push = forged
        .operations
        .iter_mut()
        .find_map(|operation| match operation {
            Instruction::Guarded { operation, .. } => match operation.as_mut() {
                Instruction::Push {
                    storage: true,
                    alignment,
                    ..
                } if alignment == "u128" => Some(operation.as_mut()),
                _ => None,
            },
            _ => None,
        })
        .expect("guarded u128 storage push");
    *push = Instruction::PushFields {
        storage: true,
        expressions: vec![Expr::Constant { value: "7".into() }],
        schema: json!("JubjubScalar"),
    };
    let rejected = prepare(
        &forged,
        &BTreeMap::from([
            ("amount".into(), json!("7")),
            ("enabled".into(), json!(true)),
        ]),
        &explicit,
        &INITIAL_PARAMETERS,
        address,
    );
    assert!(matches!(rejected, Err(error)
        if error.to_string().contains("byte-aligned UInt128 Cell requires a scalar u128 push")));
    Ok(())
}
