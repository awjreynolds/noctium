#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{Db, Plan, check, create_state, field_decimal, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str = include_str!("fixtures/structured-maps/321/StructuredMaps.update.impact.json");
const CIRCUIT: &[u8] = include_bytes!("fixtures/structured-maps/321/StructuredMaps.update.zkir");

fn inputs(enabled: bool, account: &[u8; 32], amount: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("enabled".into(), json!(enabled)),
        (
            "account".into(),
            json!({"kind":"bytes", "values":account.as_slice()}),
        ),
        ("amount".into(), json!(amount.to_string())),
    ])
}

fn assert_balance(
    state: &ChargedState<Db>,
    account: &[u8; 32],
    expected: Option<&str>,
    expected_size: usize,
) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array");
    };
    let StateValue::Map(map) = &*array.get(0).expect("balances map exists") else {
        panic!("expected balances map");
    };
    assert_eq!(map.size(), expected_size);
    let key: AlignedValue = (*account).into();
    match (map.get(&key), expected) {
        (None, None) => {}
        (Some(value), Some(expected)) => {
            let StateValue::Cell(cell) = &*value else {
                panic!("expected balance cell");
            };
            let mut fields = Vec::new();
            cell.value_only_field_repr(&mut fields);
            assert_eq!(fields.len(), 1);
            assert_eq!(field_decimal(fields[0]), expected);
        }
        _ => panic!("map state differs from the expected entry"),
    }
}

fn assert_result(execution: &noctium_runtime::Execution, expected: u64) {
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([("result".into(), json!(expected.to_string()))])
    );
}

fn load_entrypoint(directory: &std::path::Path, stem: &str) -> anyhow::Result<(Plan, IrSource)> {
    Ok((
        serde_json::from_slice(&std::fs::read(
            directory.join(format!("{stem}.impact.json")),
        )?)?,
        IrSource::load(std::fs::File::open(directory.join(format!("{stem}.zkir")))?)?,
    ))
}

#[test]
#[ignore = "requires fresh RecordMapDefaults outputs in NOCTIUM_RECORD_MAP_DEFAULTS_DIR"]
fn guarded_record_map_defaults_insert_replace_and_preserve_siblings() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(std::env::var("NOCTIUM_RECORD_MAP_DEFAULTS_DIR")?);
    let seed = load_entrypoint(&directory, "RecordMapDefaults.seedRecordMaps")?;
    let default = load_entrypoint(&directory, "RecordMapDefaults.defaultRecordMaps")?;
    let config = seed
        .0
        .state
        .iter()
        .map(|declaration| (declaration.name.clone(), json!([])))
        .collect();
    let initial = create_state(&seed.0, &config)?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let seed_args = |active, nonce: u16, amount: u16, accepted, receipt_amount: u16| {
        BTreeMap::from([
            ("active".into(), json!(active)),
            ("nonce".into(), json!(nonce.to_string())),
            ("amount".into(), json!(amount.to_string())),
            ("accepted".into(), json!(accepted)),
            ("receiptAmount".into(), json!(receipt_amount.to_string())),
        ])
    };
    let default_args = |active, nonce: u16, enabled| {
        BTreeMap::from([
            ("active".into(), json!(active)),
            ("nonce".into(), json!(nonce.to_string())),
            ("enabled".into(), json!(enabled)),
        ])
    };
    let run = |operation: &(Plan, IrSource), args: &BTreeMap<String, Json>, state: &ChargedState<Db>| {
        let execution = prepare(&operation.0, args, state, parameters, address)?;
        assert_eq!(
            check(&execution, &operation.1)?,
            execution.activity_schedule
        );
        Ok::<_, anyhow::Error>(execution)
    };

    let sibling = run(
        &seed,
        &seed_args(false, 513, 22, false, 42),
        &initial,
    )?;

    let expected = run(
        &seed,
        &seed_args(true, 513, 0, false, 0),
        &sibling.after.state,
    )?;
    let inserted = run(
        &default,
        &default_args(true, 513, true),
        &sibling.after.state,
    )?;
    assert_eq!(inserted.after.state.get_ref(), expected.after.state.get_ref());

    let replaced = run(
        &seed,
        &seed_args(true, 513, 19, true, 91),
        &inserted.after.state,
    )?;
    let reset = run(
        &default,
        &default_args(true, 513, true),
        &replaced.after.state,
    )?;
    assert_eq!(reset.after.state.get_ref(), expected.after.state.get_ref());

    let disabled = run(
        &default,
        &default_args(true, 513, false),
        &replaced.after.state,
    )?;
    assert_eq!(disabled.after.state, replaced.after.state);
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_RECORD_MAP_KEYS_DIR"]
fn record_map_keys_preserve_strict_lookup_and_distinct_members() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(std::env::var("NOCTIUM_RECORD_MAP_KEYS_DIR")?);
    let load = |entry| load_entrypoint(&directory, &format!("RecordMapKeys.{entry}"));
    let (update, update_relation) = load("update")?;
    let (lookup, lookup_relation) = load("lookup")?;
    let (remove, remove_relation) = load("removeMemo")?;
    let mut state = create_state(&update, &BTreeMap::from([("memos".into(), json!([]))]))?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let key = |active, amount: u32| {
        BTreeMap::from([
            ("active".into(), json!(active)),
            ("amount".into(), json!(amount.to_string())),
        ])
    };
    let update_args = |active, amount, value: u16| {
        let mut arguments = key(active, amount);
        arguments.insert("value".into(), json!(value.to_string()));
        arguments
    };
    let remove_args = |active, amount, removing| {
        let mut arguments = key(active, amount);
        arguments.insert("removing".into(), json!(removing));
        arguments
    };
    let read = |active, amount, state: &ChargedState<Db>| -> anyhow::Result<Json> {
        let execution = prepare(&lookup, &key(active, amount), state, parameters, address)?;
        assert_eq!(
            check(&execution, &lookup_relation)?,
            execution.activity_schedule
        );
        Ok(execution.returns_json()["storedValue"].clone())
    };

    assert!(read(true, 513, &state).is_err());
    let records = [(true, 513, 11u16), (false, 513, 22u16), (true, 514, 33u16)];
    for (active, amount, value) in records {
        let arguments = update_args(active, amount, value);
        let execution = prepare(&update, &arguments, &state, parameters, address)?;
        assert_eq!(
            check(&execution, &update_relation)?,
            execution.activity_schedule
        );
        assert_eq!(execution.returns_json()["presentBefore"], json!(false));
        assert_eq!(execution.returns_json()["presentAfter"], json!(true));
        state = execution.after.state;
    }
    for (active, amount, value) in records {
        assert_eq!(read(active, amount, &state)?, json!(value.to_string()));
    }

    let inactive_remove = prepare(
        &remove,
        &remove_args(true, 513, false),
        &state,
        parameters,
        address,
    )?;
    assert_eq!(
        check(&inactive_remove, &remove_relation)?,
        inactive_remove.activity_schedule
    );
    assert_eq!(inactive_remove.returns_json()["presentBefore"], json!(true));
    assert_eq!(inactive_remove.returns_json()["presentAfter"], json!(true));
    assert_eq!(inactive_remove.after.state, state);
    assert_eq!(read(true, 513, &inactive_remove.after.state)?, json!("11"));
    assert_eq!(read(false, 513, &inactive_remove.after.state)?, json!("22"));
    assert_eq!(read(true, 514, &inactive_remove.after.state)?, json!("33"));

    let removed = prepare(
        &remove,
        &remove_args(true, 513, true),
        &inactive_remove.after.state,
        parameters,
        address,
    )?;
    assert_eq!(
        check(&removed, &remove_relation)?,
        removed.activity_schedule
    );
    assert_eq!(removed.returns_json()["presentBefore"], json!(true));
    assert_eq!(removed.returns_json()["presentAfter"], json!(false));
    state = removed.after.state;
    assert!(read(true, 513, &state).is_err());
    assert_eq!(read(false, 513, &state)?, json!("22"));
    assert_eq!(read(true, 514, &state)?, json!("33"));
    assert!(read(true, 65536, &state).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_RECORD_MAP_COMPOSITION_DIR"]
fn record_map_composes_typed_keys_and_values() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(std::env::var("NOCTIUM_RECORD_MAP_COMPOSITION_DIR")?);
    let load = |entry| load_entrypoint(&directory, &format!("RecordMapComposition.{entry}"));
    let put = load("put")?;
    let lookup = load("lookup")?;
    let member = load("contains")?;
    let remove = load("deleteMemo")?;
    let mut state = create_state(&put.0, &BTreeMap::from([("receipts".into(), json!([]))]))?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let key = |active, amount: u32| {
        BTreeMap::from([
            ("active".into(), json!(active)),
            ("amount".into(), json!(amount.to_string())),
        ])
    };
    let put_args = |active, amount, accepted, code: u32| {
        let mut arguments = key(active, amount);
        arguments.insert("accepted".into(), json!(accepted));
        arguments.insert("code".into(), json!(code.to_string()));
        arguments
    };
    let run =
        |operation: &(Plan, IrSource), args: &BTreeMap<String, Json>, state: &ChargedState<Db>| {
            let result = prepare(&operation.0, args, state, parameters, address)?;
            assert_eq!(check(&result, &operation.1)?, result.activity_schedule);
            Ok::<_, anyhow::Error>(result)
        };
    let read = |active, amount, state: &ChargedState<Db>| -> anyhow::Result<(Json, Json)> {
        let returns = run(&lookup, &key(active, amount), state)?.returns_json();
        Ok((
            returns["storedAccepted"].clone(),
            returns["storedCode"].clone(),
        ))
    };
    assert_eq!(
        run(&member, &key(true, 513), &state)?.returns_json()["isFound"],
        json!(false)
    );
    for (active, accepted, code) in [(true, false, 7), (false, false, 22), (true, true, 41)] {
        state = run(&put, &put_args(active, 513, accepted, code), &state)?
            .after
            .state;
        assert_eq!(
            read(active, 513, &state)?,
            (json!(accepted), json!(code.to_string()))
        );
    }
    for (active, amount, present) in [(true, 513, true), (false, 513, true), (true, 514, false)] {
        let result = run(&member, &key(active, amount), &state)?;
        assert_eq!(result.returns_json()["isFound"], json!(present));
    }
    let StateValue::Array(slots) = state.get_ref() else {
        anyhow::bail!("expected a state array");
    };
    let Some(StateValue::Map(entries)) = slots.get(0) else {
        anyhow::bail!("expected a Map of records");
    };
    assert_eq!(entries.size(), 2);
    let removed = run(&remove, &key(true, 513), &state)?;
    assert_eq!(removed.returns_json()["presentBefore"], json!(true));
    assert_eq!(removed.returns_json()["presentAfter"], json!(false));
    state = removed.after.state;
    assert!(read(true, 513, &state).is_err());
    assert_eq!(read(false, 513, &state)?, (json!(false), json!("22")));
    assert!(run(&put, &put_args(true, 65536, false, 7), &state).is_err());
    assert!(run(&put, &put_args(true, 513, false, 65536), &state).is_err());
    let mut wrong_value_plan = lookup.0.clone();
    wrong_value_plan.state[0].kind["tree"]["map"][1]["composite"]["fields"]
        .as_array_mut()
        .expect("composed Map value fields")
        .swap(0, 1);
    assert!(
        prepare(
            &wrong_value_plan,
            &key(false, 513),
            &state,
            parameters,
            address
        )
        .is_err()
    );
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_RECORD_MAP_COLLECTIONS_DIR"]
fn record_key_maps_report_size_and_reset_to_constructor_state() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(std::env::var("NOCTIUM_RECORD_MAP_COLLECTIONS_DIR")?);
    let (plan, relation) = load_entrypoint(&directory, "RecordMapCollections.update")?;
    let initial = create_state(
        &plan,
        &BTreeMap::from([("scalars".into(), json!([])), ("records".into(), json!([]))]),
    )?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let mut state = initial.clone();
    for (active, adding, clear, size) in [
        (true, false, false, 0),
        (true, true, false, 1),
        (true, true, false, 1),
        (false, true, false, 2),
        (false, false, false, 2),
        (true, false, true, 0),
    ] {
        let inputs = BTreeMap::from([
            ("active".into(), json!(active)),
            ("amount".into(), json!("513")),
            ("adding".into(), json!(adding)),
            ("clear".into(), json!(clear)),
        ]);
        let step = prepare(&plan, &inputs, &state, parameters, address)?;
        assert_eq!(check(&step, &relation)?, step.activity_schedule);
        let returns = step.returns_json();
        assert_eq!(returns["scalarSize"], json!(size.to_string()));
        assert_eq!(returns["recordSize"], json!(size.to_string()));
        assert_eq!(returns["scalarEmpty"], json!(size == 0));
        assert_eq!(returns["recordEmpty"], json!(size == 0));
        if !adding && !clear {
            assert_eq!(step.after.state.get_ref(), state.get_ref());
        }
        state = step.after.state;
    }
    assert_eq!(state.get_ref(), initial.get_ref());
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_NESTED_RECORD_MAP_DIR"]
fn nested_record_key_map_reads_inserts_and_guarded_removes() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(std::env::var("NOCTIUM_NESTED_RECORD_MAP_DIR")?);
    let load = |entry| load_entrypoint(&directory, &format!("NestedRecordMap.{entry}"));
    let (initialize, initialize_relation) = load("initializeOwner")?;
    let (upsert, upsert_relation) = load("upsert")?;
    let (lookup, lookup_relation) = load("lookup")?;
    let (remove, remove_relation) = load("removeMemo")?;
    let mut state = create_state(&upsert, &BTreeMap::from([("memos".into(), json!([]))]))?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let owner = |byte: u8| json!({"kind":"bytes", "values":vec![byte; 32]});
    let owner_args = |owner_byte| BTreeMap::from([("owner".into(), owner(owner_byte))]);
    for owner_byte in [1, 2] {
        let step = prepare(
            &initialize,
            &owner_args(owner_byte),
            &state,
            parameters,
            address,
        )?;
        assert_eq!(
            check(&step, &initialize_relation)
                .map_err(|error| anyhow::anyhow!("initializeOwner check: {error}"))?,
            step.activity_schedule
        );
        state = step.after.state;
    }
    let key_args = |owner_byte, active, amount: u16| {
        BTreeMap::from([
            ("owner".into(), owner(owner_byte)),
            ("active".into(), json!(active)),
            ("amount".into(), json!(amount.to_string())),
        ])
    };
    for (owner_byte, active, value) in [(1, true, 11u16), (1, false, 22), (2, true, 99)] {
        let mut args = key_args(owner_byte, active, 513);
        args.insert("value".into(), json!(value.to_string()));
        let step = prepare(&upsert, &args, &state, parameters, address)?;
        assert_eq!(
            check(&step, &upsert_relation).map_err(|error| {
                anyhow::anyhow!("upsert owner={owner_byte} active={active}: {error}")
            })?,
            step.activity_schedule
        );
        let returns = step.returns_json();
        assert_eq!(returns["presentBefore"], json!(false));
        assert_eq!(returns["presentAfter"], json!(true));
        assert_eq!(returns["storedValue"], json!(value.to_string()));
        state = step.after.state;
    }

    let mut overwrite_args = key_args(1, true, 513);
    overwrite_args.insert("value".into(), json!("33"));
    let overwrite = prepare(&upsert, &overwrite_args, &state, parameters, address)?;
    assert_eq!(
        check(&overwrite, &upsert_relation)
            .map_err(|error| anyhow::anyhow!("overwrite check: {error}"))?,
        overwrite.activity_schedule
    );
    assert_eq!(overwrite.returns_json()["presentBefore"], json!(true));
    assert_eq!(overwrite.returns_json()["presentAfter"], json!(true));
    assert_eq!(overwrite.returns_json()["storedValue"], json!("33"));
    state = overwrite.after.state;

    let lookup_args = |owner_byte, active, amount: u16, should_read| {
        let mut args = key_args(owner_byte, active, amount);
        args.insert("shouldRead".into(), json!(should_read));
        args
    };
    let found = prepare(
        &lookup,
        &lookup_args(1, true, 513, true),
        &state,
        parameters,
        address,
    )?;
    assert_eq!(
        check(&found, &lookup_relation)
            .map_err(|error| anyhow::anyhow!("found lookup check: {error}"))?,
        found.activity_schedule
    );
    assert_eq!(found.returns_json()["present"], json!(true));
    assert_eq!(found.returns_json()["storedValue"], json!("33"));

    let miss_args = lookup_args(1, true, 514, false);
    let miss = prepare(&lookup, &miss_args, &state, parameters, address)?;
    assert_eq!(
        check(&miss, &lookup_relation)
            .map_err(|error| anyhow::anyhow!("missing lookup check: {error}"))?,
        miss.activity_schedule
    );
    assert_eq!(miss.returns_json()["present"], json!(false));
    assert_eq!(miss.returns_json()["storedValue"], json!("0"));
    let mut invalid_miss_args = miss_args;
    invalid_miss_args.insert("shouldRead".into(), json!(true));
    assert!(prepare(&lookup, &invalid_miss_args, &state, parameters, address).is_err());

    let mut inactive_args = key_args(1, false, 513);
    inactive_args.insert("removeIt".into(), json!(false));
    let inactive = prepare(&remove, &inactive_args, &state, parameters, address)?;
    assert_eq!(
        check(&inactive, &remove_relation)
            .map_err(|error| anyhow::anyhow!("inactive remove check: {error}"))?,
        inactive.activity_schedule
    );
    assert_eq!(inactive.returns_json()["presentBefore"], json!(true));
    assert_eq!(inactive.returns_json()["presentAfter"], json!(true));
    assert_eq!(inactive.after.state.get_ref(), state.get_ref());

    let mut active_args = key_args(1, false, 513);
    active_args.insert("removeIt".into(), json!(true));
    let removed = prepare(
        &remove,
        &active_args,
        &inactive.after.state,
        parameters,
        address,
    )?;
    assert_eq!(
        check(&removed, &remove_relation)
            .map_err(|error| anyhow::anyhow!("active remove check: {error}"))?,
        removed.activity_schedule
    );
    assert_eq!(removed.returns_json()["presentBefore"], json!(true));
    assert_eq!(removed.returns_json()["presentAfter"], json!(false));
    for (owner_byte, active, value) in [(1, true, 33u16), (2, true, 99)] {
        let step = prepare(
            &lookup,
            &lookup_args(owner_byte, active, 513, true),
            &removed.after.state,
            parameters,
            address,
        )?;
        assert_eq!(
            check(&step, &lookup_relation)
                .map_err(|error| anyhow::anyhow!("retained lookup check: {error}"))?,
            step.activity_schedule
        );
        assert_eq!(step.returns_json()["present"], json!(true));
        assert_eq!(step.returns_json()["storedValue"], json!(value.to_string()));
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_NESTED_RECORD_MAP_RECORDS_DIR"]
fn nested_record_key_map_reads_and_writes_typed_record_values() -> anyhow::Result<()> {
    let directory = std::path::PathBuf::from(std::env::var(
        "NOCTIUM_NESTED_RECORD_MAP_RECORDS_DIR",
    )?);
    let load = |entry| load_entrypoint(&directory, &format!("NestedRecordMapRecords.{entry}"));
    let (initialize, initialize_relation) = load("initializeOwner")?;
    let upsert = load("upsert")?;
    let lookup = load("lookup")?;
    let remove = load("removeMemo")?;
    let mut state = create_state(&upsert.0, &BTreeMap::from([("memos".into(), json!([]))]))?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let owner = |byte: u8| json!({"kind":"bytes", "values":vec![byte; 32]});
    let owner_args = |owner_byte| BTreeMap::from([("owner".into(), owner(owner_byte))]);
    for owner_byte in [1, 2] {
        let step = prepare(
            &initialize,
            &owner_args(owner_byte),
            &state,
            parameters,
            address,
        )?;
        assert_eq!(check(&step, &initialize_relation)?, step.activity_schedule);
        state = step.after.state;
    }
    let key_args = |owner_byte, active, amount: u16| {
        BTreeMap::from([
            ("owner".into(), owner(owner_byte)),
            ("active".into(), json!(active)),
            ("amount".into(), json!(amount.to_string())),
        ])
    };
    let run = |operation: &(Plan, IrSource), args: &BTreeMap<String, Json>, state: &ChargedState<Db>| {
        let execution = prepare(&operation.0, args, state, parameters, address)?;
        assert_eq!(check(&execution, &operation.1)?, execution.activity_schedule);
        Ok::<_, anyhow::Error>(execution)
    };

    for (owner_byte, active, accepted, code) in [
        (1, true, false, 7u16),
        (1, false, false, 22),
        (2, true, true, 99),
    ] {
        let mut args = key_args(owner_byte, active, 513);
        args.insert("accepted".into(), json!(accepted));
        args.insert("code".into(), json!(code.to_string()));
        let step = run(&upsert, &args, &state)?;
        let returns = step.returns_json();
        assert_eq!(returns["presentBefore"], json!(false));
        assert_eq!(returns["presentAfter"], json!(true));
        assert_eq!(returns["storedAccepted"], json!(accepted));
        assert_eq!(returns["storedCode"], json!(code.to_string()));
        state = step.after.state;
    }

    let mut overwrite_args = key_args(1, true, 513);
    overwrite_args.insert("accepted".into(), json!(true));
    overwrite_args.insert("code".into(), json!("41"));
    let overwrite = run(&upsert, &overwrite_args, &state)?;
    assert_eq!(overwrite.returns_json()["presentBefore"], json!(true));
    assert_eq!(overwrite.returns_json()["presentAfter"], json!(true));
    assert_eq!(overwrite.returns_json()["storedAccepted"], json!(true));
    assert_eq!(overwrite.returns_json()["storedCode"], json!("41"));
    state = overwrite.after.state;

    let lookup_args = |owner_byte, active, amount: u16, should_read| {
        let mut args = key_args(owner_byte, active, amount);
        args.insert("shouldRead".into(), json!(should_read));
        args
    };
    for (owner_byte, active, accepted, code) in [
        (1, true, true, 41u16),
        (1, false, false, 22),
        (2, true, true, 99),
    ] {
        let step = run(
            &lookup,
            &lookup_args(owner_byte, active, 513, true),
            &state,
        )?;
        assert_eq!(step.returns_json()["present"], json!(true));
        assert_eq!(step.returns_json()["storedAccepted"], json!(accepted));
        assert_eq!(step.returns_json()["storedCode"], json!(code.to_string()));
    }

    let mut remove_args = key_args(1, false, 513);
    remove_args.insert("removeIt".into(), json!(true));
    let removed = run(&remove, &remove_args, &state)?;
    assert_eq!(removed.returns_json()["presentBefore"], json!(true));
    assert_eq!(removed.returns_json()["presentAfter"], json!(false));
    state = removed.after.state;
    let absent = run(
        &lookup,
        &lookup_args(1, false, 513, false),
        &state,
    )?;
    assert_eq!(absent.returns_json()["present"], json!(false));
    assert_eq!(absent.returns_json()["storedAccepted"], json!(false));
    assert_eq!(absent.returns_json()["storedCode"], json!("0"));
    for (owner_byte, accepted, code) in [(1, true, 41u16), (2, true, 99)] {
        let retained = run(
            &lookup,
            &lookup_args(owner_byte, true, 513, true),
            &state,
        )?;
        assert_eq!(retained.returns_json()["present"], json!(true));
        assert_eq!(retained.returns_json()["storedAccepted"], json!(accepted));
        assert_eq!(retained.returns_json()["storedCode"], json!(code.to_string()));
    }

    let miss = lookup_args(1, true, 514, false);
    let absent = run(&lookup, &miss, &state)?;
    assert_eq!(absent.returns_json()["present"], json!(false));
    assert_eq!(absent.returns_json()["storedAccepted"], json!(false));
    assert_eq!(absent.returns_json()["storedCode"], json!("0"));
    let mut invalid_miss = miss;
    invalid_miss.insert("shouldRead".into(), json!(true));
    assert!(prepare(&lookup.0, &invalid_miss, &state, parameters, address).is_err());
    Ok(())
}

#[test]
fn structured_helper_binds_guarded_bytes32_map_effects_and_returns() {
    let plan: Plan = serde_json::from_str(PLAN).expect("source map plan parses");
    let circuit = IrSource::load(CIRCUIT).expect("source ZKIR parses");
    let initial = create_state(&plan, &BTreeMap::from([("balances".into(), json!([]))]))
        .expect("empty balances map creates");
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let account = [0x42; 32];

    let disabled_empty = prepare(
        &plan,
        &inputs(false, &account, 8),
        &initial,
        params,
        address,
    )
    .expect("disabled call skips narrowing and map writes");
    check(&disabled_empty, &circuit).expect("disabled call relation checks");
    assert_eq!(disabled_empty.after.state, initial);
    assert_balance(&disabled_empty.after.state, &account, None, 0);
    assert_result(&disabled_empty, 0);

    let first = prepare(&plan, &inputs(true, &account, 7), &initial, params, address)
        .expect("active call inserts a missing balance");
    check(&first, &circuit).expect("insert call relation checks");
    assert_balance(&first.after.state, &account, Some("7"), 1);
    assert_result(&first, 7);

    let second = prepare(
        &plan,
        &inputs(true, &account, 2),
        &first.after.state,
        params,
        address,
    )
    .expect("active call reads and increments an existing balance");
    check(&second, &circuit).expect("increment call relation checks");
    assert_balance(&second.after.state, &account, Some("9"), 1);
    assert_result(&second, 9);

    let disabled_existing = prepare(
        &plan,
        &inputs(false, &account, 8),
        &second.after.state,
        params,
        address,
    )
    .expect("disabled call preserves an existing balance");
    check(&disabled_existing, &circuit).expect("disabled existing call relation checks");
    assert_eq!(disabled_existing.after.state, second.after.state);
    assert_balance(&disabled_existing.after.state, &account, Some("9"), 1);
    assert_result(&disabled_existing, 9);

    if let Ok(invalid_active) = prepare(
        &plan,
        &inputs(true, &account, 8),
        &second.after.state,
        params,
        address,
    ) {
        assert!(check(&invalid_active, &circuit).is_err());
    }

    let mut altered_guard = prepare(
        &plan,
        &inputs(false, &account, 8),
        &second.after.state,
        params,
        address,
    )
    .expect("disabled call prepares for guard tampering");
    assert_eq!(altered_guard.preimage.private_transcript.len(), 1);
    altered_guard.preimage.private_transcript[0] = Fr::from(1u64);
    assert!(check(&altered_guard, &circuit).is_err());
}
