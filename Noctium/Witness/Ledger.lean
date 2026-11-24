import Noctium.Helpers

namespace Noctium.Witness.Ledger
open Noctium.Helpers

structure LedgerCall where
  site : String
  name : String
  kind : String
  state : String
  keyTy : Option Ty := none
  valueTy : Ty
  deriving Repr

structure Transformed where
  host : Program
  native : Program
  calls : List LedgerCall
  deriving Repr

private structure BuildState where
  source : String
  nominalUIntCells : List (String × NominalUIntType) := []
  nominalUIntMaps : List (String × NominalUIntMap) := []
  nominalFieldMapKeys : List (String × String) := []
  next : Nat := 0
  reserved : List String := []
  calls : List LedgerCall := []
  signatures : List WitnessSignature := []

private abbrev BuildM := StateT BuildState (Except Diagnostic)

private def fresh (stem : String) : BuildM String := do
  let state ← get
  let mut result : Option (Nat × String) := none
  let mut offset := 0
  let bound := (({} : Helpers.Limits).maxSourceNodes) * 8
  while offset < bound && result.isNone do
    let index := state.next + offset
    let candidate := s!"noctium_ledger_{stem}_{index}"
    if !state.reserved.contains candidate &&
        (state.source.splitOn candidate).length == 1 then
      result := some (index, candidate)
    offset := offset + 1
  let some (index, name) := result
    | throw {span := {}, message := "could not allocate a fresh ledger witness identity"}
  modify fun state => {state with next := index + 1, reserved := name :: state.reserved}
  pure name

private def isRead : String → Bool
  | "readCell" | "readMap" | "readMember" => true
  | _ => false

private def signatureResult (kind : String) (valueTy : Ty) : ResultType :=
  if kind == "writeCell" || kind == "writeMap" then .unit
  else .scalar (if kind == "readMember" then .bool else valueTy)

private def registerCall (kind stateName : String) (keyTy : Option Ty) (valueTy : Ty)
    (parameters : List WitnessParameter) (resultNominal : Option String := none) :
    BuildM (String × String) := do
  let site ← fresh "site"
  let name ← fresh "signature"
  let signature : WitnessSignature := {
    name,
    operation := if isRead kind then "noctium.ledger.read.v1" else "noctium.ledger.write.v1",
    capability := "noctium.ledger",
    parameters,
    result := signatureResult kind valueTy,
    resultNominal}
  modify fun current => {current with
    calls := current.calls ++ [{site, name, kind, state := stateName, keyTy, valueTy}]
    signatures := current.signatures ++ [signature]}
  pure (site, name)

private def scalarParameter (name : String) (ty : Ty)
    (sourceNominal : Option String := none)
    (sourceNominalField : Option String := none) : WitnessParameter :=
  {name, type := .scalar ty, sourceNominal, sourceNominalField}

private def callTerm (site name : String) (arguments : List Term) : Term :=
  .witnessCall site name arguments

private def transformStatement (statement : Statement) : BuildM (List Statement × List Statement) := do
  match statement with
  | .readCell state destination ty => do
    let actual ← fresh "read"
    let nominalUInt? := (← get).nominalUIntCells.lookup state
    let (site, name) ← registerCall "readCell" state none ty []
      (nominalUInt?.map (·.name))
    -- Native equality ties the disclosed provider value to the public ledger read.
    let bindResult := Statement.bind destination (.scalar ty)
      (.disclose {} (callTerm site name []))
    pure ([bindResult], [.readCell state actual ty, bindResult,
      .assert (.eq (.ref destination) (.ref actual))])
  | .readMap state destination keyTy valueTy key
  | .readMember state destination keyTy valueTy key => do
    let kind := match statement with
      | .readMember .. => "readMember"
      | _ => "readMap"
    let resultTy := if kind == "readMember" then .bool else valueTy
    let keyName ← fresh "key"
    let actual ← fresh "read"
    let nominalMap := ((← get).nominalUIntMaps.lookup state).getD {}
    let keyNominal := nominalMap.key.map (·.name)
    let keyNominalField := (← get).nominalFieldMapKeys.lookup state
    let resultNominal := if kind == "readMember" then none else nominalMap.value.map (·.name)
    let (site, name) ← registerCall kind state (some keyTy) valueTy
      [scalarParameter "key" keyTy keyNominal keyNominalField] resultNominal
    let bindKey := Statement.bind keyName (.scalar keyTy) key
    -- Native equality ties the disclosed provider value to the public ledger read.
    let bindResult := Statement.bind destination (.scalar resultTy)
      (.disclose {} (callTerm site name [.ref keyName]))
    let nativeRead := if kind == "readMember" then
      Statement.readMember state actual keyTy valueTy (.ref keyName)
      else Statement.readMap state actual keyTy valueTy (.ref keyName)
    pure ([bindKey, bindResult], [bindKey, nativeRead, bindResult,
      .assert (.eq (.ref destination) (.ref actual))])
  | .writeCell state ty value => do
    let valueName ← fresh "value"
    let nominalUInt? := (← get).nominalUIntCells.lookup state
    let (site, name) ← registerCall "writeCell" state none ty
      [scalarParameter "value" ty (nominalUInt?.map (·.name))]
    let bindValue := Statement.bind valueName (.scalar ty) value
    let notify := Statement.evaluate (callTerm site name [.ref valueName])
    pure ([bindValue, notify], [bindValue, .writeCell state ty (.ref valueName), notify])
  | .writeMap state keyTy valueTy key value => do
    let keyName ← fresh "key"
    let valueName ← fresh "value"
    let nominalMap := ((← get).nominalUIntMaps.lookup state).getD {}
    let keyNominalField := (← get).nominalFieldMapKeys.lookup state
    let (site, name) ← registerCall "writeMap" state (some keyTy) valueTy
      [scalarParameter "key" keyTy (nominalMap.key.map (·.name)) keyNominalField,
        scalarParameter "value" valueTy (nominalMap.value.map (·.name))]
    let bindKey := Statement.bind keyName (.scalar keyTy) key
    let bindValue := Statement.bind valueName (.scalar valueTy) value
    let notify := Statement.evaluate (callTerm site name [.ref keyName, .ref valueName])
    pure ([bindKey, bindValue, notify],
      [bindKey, bindValue, .writeMap state keyTy valueTy (.ref keyName) (.ref valueName), notify])
  | .forRange .. => throw {span := {}, message := "unexpanded finite loop reached ledger witness transformation"}
  | other => pure ([other], [other])

private def transformBody : List Statement → BuildM (List Statement × List Statement)
  | [] => pure ([], [])
  | .branch condition yes no :: rest => do
    let (hostYes, nativeYes) ← transformBody yes
    let (hostNo, nativeNo) ← transformBody no
    let (hostRest, nativeRest) ← transformBody rest
    pure (.branch condition hostYes hostNo :: hostRest,
      .branch condition nativeYes nativeNo :: nativeRest)
  | statement :: rest => do
    let (hostHead, nativeHead) ← transformStatement statement
    let (hostRest, nativeRest) ← transformBody rest
    pure (hostHead ++ hostRest, nativeHead ++ nativeRest)
termination_by body => sizeOf body
decreasing_by all_goals simp_wf <;> omega

private def transformDeclarations : List Declaration → BuildM (List Declaration × List Declaration)
  | [] => pure ([], [])
  | declaration :: rest => do
    let (hostBody, nativeBody) ← transformBody declaration.body
    let (hostRest, nativeRest) ← transformDeclarations rest
    pure ({declaration with body := hostBody} :: hostRest,
      {declaration with body := nativeBody} :: nativeRest)
termination_by declarations => sizeOf declarations
decreasing_by all_goals simp_wf <;> omega

/-- Replace ledger statements with typed host calls while retaining the native
state effects and an equality check tying every disclosed read to ledger state. -/
def transform (program : Program) : Except Diagnostic Transformed := do
  let program ← Helpers.prepareProgramWithLimits {} program
  discard (Helpers.analyze program)
  let source := reprStr program
  let initial : BuildState := {
    source, nominalUIntCells := program.nominalUIntCells,
    nominalUIntMaps := program.nominalUIntMaps,
    nominalFieldMapKeys := program.nominalFieldMapKeys,
    reserved := program.witnesses.map (·.name)}
  let action : BuildM (List Declaration × List Declaration) := transformDeclarations program.declarations
  let ((hostDeclarations, nativeDeclarations), result) ← action.run initial
  let host : Program := {program with
    declarations := hostDeclarations
    witnesses := program.witnesses ++ result.signatures}
  let native : Program := {program with
    declarations := nativeDeclarations
    witnesses := program.witnesses ++ result.signatures}
  pure {host, native, calls := result.calls}

end Noctium.Witness.Ledger
