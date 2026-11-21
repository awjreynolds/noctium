import Noctium.IR

namespace Noctium.Disclosure

structure Origin where
  name : String
  kind : PrivateOriginKind
  span : SourceSpan
  deriving Repr, BEq

abbrev Origins := List Origin
abbrev Environment := List (String × Origins)

structure Sink where
  description : String
  span : SourceSpan

private def merge (left right : Origins) : Origins := (left ++ right).eraseDups

private def kindName : PrivateOriginKind → String
  | .parameter => "parameter"
  | .provider => "provider result"
  | .privateState => "private-state read"

private def location (span : SourceSpan) : String :=
  s!"{if span.file.isEmpty then "<typed-ir>" else span.file}:{span.line}:{span.column}"

/-- Payload disclosure never clears the separate, active control context.
Structured guards must pass their accumulated predicate origins here. -/
def checkSink (sink : Sink) (payload : Origins) (control : Origins := []) : Except Diagnostic Unit :=
  match control.head?, payload.head? with
  | some origin, _ => .error {span := sink.span, message :=
      s!"undisclosed private control from {kindName origin.kind} '{origin.name}' at {location origin.span} reaches {sink.description}; disclose the controlling value explicitly"}
  | none, some origin => .error {span := sink.span, message :=
      s!"undisclosed private {kindName origin.kind} '{origin.name}' at {location origin.span} reaches {sink.description}; use disclose(...) for the released value"}
  | none, none => .ok ()

/-- Every scalar/native constructor has an explicit rule. Hashing propagates
origins. Missing references fail closed instead of becoming public values. -/
def origins (env : Environment) : Expr ty → Except String Origins
  | .native _ | .bool _ | .uint _ _ => pure []
  | .bytesField value _ | .bytesAt value _ => origins env value
  | .opaqueBytesProjection value => origins env value
  | .bytesLiteral _ _ => pure []
  | .reverseBytes value | .sliceBytes value .. => origins env value
  | .concatBytes left right => do
    pure (merge (← origins env left) (← origins env right))
  | .sha256 value | .sha512 value | .keccak256 value
  | .keccak256Secp256k1Point value => origins env value
  | .reverseBytes32 value => origins env value
  | .persistentHash32 value => origins env value
  | .bytes32Literal _ => pure []
  | .persistentHashVector32 values => do
    let mut result : Origins := []
    for value in values do result := merge result (← origins env value)
    pure result
  | .persistentHashNative value => origins env value
  | .persistentHashNativeVector values | .transientHash values => do
    let mut result : Origins := []
    for value in values do result := merge result (← origins env value)
    pure result
  | .toBytes32 value => origins env value
  | .fromBytes32 value => origins env value
  | .fromBytes value => origins env value
  | .jubjubScalarFromNative value | .jubjubMulGenerator value => origins env value
  | .jubjubScalarToNative value | .jubjubNeg value => origins env value
  | .jubjubCoordinate value _ => origins env value
  | .jubjubMul point scalar => do
    pure (merge (← origins env point) (← origins env scalar))
  | .jubjubAdd left right => do
    pure (merge (← origins env left) (← origins env right))
  | .jubjubFromCoordinates x y => do
    pure (merge (← origins env x) (← origins env y))
  | .hashToCurve values => do
    let mut result : Origins := []
    for value in values do result := merge result (← origins env value)
    pure result
  | .foreignBase _ _ | .foreignScalar _ _ | .foreignPoint _ _ => pure []
  | .foreignEncodedField value _ => origins env value
  | .foreignUnary _ value | .foreignToBytes value => origins env value
  | .foreignBinary _ left right => do
    pure (merge (← origins env left) (← origins env right))
  | .foreignFromBytes _ value => origins env value
  | .boolAnd left right | .boolOr left right | .boolXor left right => do
    pure (merge (← origins env left) (← origins env right))
  | .ref name => match env.lookup name with
    | some result => pure result
    | none => .error s!"missing disclosure origin rule for reference '{name}'"
  | .add a b | .sub a b | .mul a b | .uadd a b | .usub a b | .umul a b
  | .eq a b | .poseidon2 _ a b => do
    pure (merge (← origins env a) (← origins env b))
  | .inv value => origins env value
  | .copyValue value | .cast _ value => origins env value
  | .select condition yes no => do
    pure (merge (← origins env condition) (merge (← origins env yes) (← origins env no)))
  | .letE name value body => do
    let value ← origins env value
    origins ((name, value) :: env) body
  | .assertE condition body => do
    discard (origins env condition)
    origins env body
  | .disclose _ value => do
    discard (origins env value)
    pure []

private def expression (env : Environment) (span : SourceSpan) (value : Expr ty) :
    Except Diagnostic Origins :=
  match origins env value with
  | .ok result => .ok result
  | .error message => .error {span, message}

private theorem expression_bool (env : Environment) (span : SourceSpan) (bit : Bool) :
    expression env span (.bool bit) = .ok [] := by
  unfold expression
  rw [origins.eq_2]
  rfl

private def pathExpression (env : Environment) (span : SourceSpan)
    (keys : List PathKey) : Except Diagnostic Origins := do
  let mut result : Origins := []
  for key in keys do
    match key with
    | .mk _ value => result := merge result (← expression env span value)
  pure result

def inputEnvironment (circuit : Circuit) : Except Diagnostic Environment := do
  if !uniqueNames (circuit.inputs.map (·.name)) then
    throw {span := circuit.span, message := "duplicate disclosure input"}
  if !uniqueNames (circuit.privateOrigins.map Prod.fst) then
    throw {span := circuit.span, message := "duplicate declared private origin"}
  for (name, _) in circuit.privateOrigins do
    unless circuit.inputs.any (·.name == name) do
      throw {span := circuit.span, message := s!"private origin '{name}' has no declared input"}
  circuit.inputs.mapM fun input => do
    let declared := circuit.privateOrigins.lookup input.name
    let privateValue := input.visibility == .«private» || declared.isSome
    let result := if privateValue then
      [{name := input.name, kind := declared.getD .parameter, span := input.span}]
      else []
    if input.visibility == .«public» then
      checkSink {description := s!"public input '{input.name}'", span := input.span} result
    pure (input.name, result)

def checkConstraints (env : Environment) (span : SourceSpan) :
    List (Expr .bool) → Except Diagnostic Unit
  | [] => pure ()
  | condition :: rest => do
    discard (expression env span condition)
    checkConstraints env span rest

theorem checkConstraints_literal (env : Environment) (span : SourceSpan) (bit : Bool)
    (rest : List (Expr .bool)) :
    checkConstraints env span (.bool bit :: rest) = checkConstraints env span rest := by
  change (do discard (expression env span (.bool bit)); checkConstraints env span rest) = _
  rw [expression_bool]
  simp [Except.map, Except.bind, Bind.bind, Functor.discard, Functor.mapConst]

def circuit (value : Circuit) (control : Origins := []) : Except Diagnostic Unit := do
  let env ← inputEnvironment value
  -- Assertions state the intended relation. This pass does not classify proof
  -- success, failure, or timing as ordinary public value-flow sinks.
  checkConstraints env value.span value.constraints
  for output in value.outputs do
    let payload ← expression env output.span output.value
    checkSink {description := s!"public output '{output.name}'", span := output.span} payload control

inductive LedgerTranscript where
  | stateRead | stateWrite | contextRead | call | asset | checkpoint | event
  deriving Repr, BEq

inductive LedgerGuard where
  | publicActivity | noSourceGuard
  deriving Repr, BEq

inductive LedgerOperand where
  | selector (name description : String) (value : Expr ty)
  | path (description : String) (keys : List PathKey)
  | payload (name description : String) (value : Expr ty)

/-- A proof constraint has no public operands or read bindings. Each ledger
effect states its public activity and operand roles explicitly. -/
inductive LedgerEffectDescriptor where
  | publicEffect (name : String) (transcript : LedgerTranscript) (guard : LedgerGuard)
      (guardSink : String) (operands : List LedgerOperand) (publicReads : List String)
  | proofConstraint (name : String) (predicate : Expr .bool)

/-- The compiler checks these operands before binding public ledger results. -/
def describeEffect : Effect → LedgerEffectDescriptor
  | .readCell state destination _ =>
    .publicEffect "readCell" .stateRead .publicActivity s!"public state read guard '{state}'"
      [] [destination]
  | .readMap state destination _ _ key =>
    .publicEffect "readMap" .stateRead .publicActivity s!"public map read guard '{state}'"
      [.selector "key" s!"public map read path '{state}'" key] [destination]
  | .readMember state destination _ _ key =>
    .publicEffect "readMember" .stateRead .publicActivity s!"public map membership guard '{state}'"
      [.selector "key" s!"public map membership path '{state}'" key] [destination]
  | .readContractAddress destination =>
    .publicEffect "readContractAddress" .contextRead .publicActivity "public contract address read guard"
      [] [destination]
  | .require condition => .proofConstraint "require" condition
  | .writeCell state _ value =>
    let sink := s!"public cell write '{state}'"
    .publicEffect "writeCell" .stateWrite .publicActivity sink [.payload "value" sink value] []
  | .writeMap state _ _ key value =>
    let sink := s!"public map write key '{state}'"
    .publicEffect "writeMap" .stateWrite .publicActivity sink
      [.selector "key" sink key, .payload "value" s!"public map write value '{state}'" value] []
  | .requireAbsent state _ key =>
    let sink := s!"public map query path '{state}'"
    .publicEffect "requireAbsent" .stateRead .noSourceGuard sink [.selector "key" sink key] []
  | .claimContractCall address entryPointHash commitment =>
    .publicEffect "claimContractCall" .call .publicActivity "contract-call claim address"
      [.selector "address" "contract-call claim address" address,
       .selector "entryPointHash" "contract-call claim entrypoint hash" entryPointHash,
       .payload "commitment" "contract-call claim commitment" commitment] []
  | .mintShielded domain amount =>
    let sink := "public shielded mint"
    .publicEffect "mintShielded" .asset .publicActivity sink
      [.selector "domain" sink domain, .payload "amount" sink amount] []
  | .receiveShieldedToMap _ nonce color amount selfAddress =>
    let sink := "public shielded coin receive"
    .publicEffect "receiveShieldedToMap" .asset .publicActivity sink
      [.selector "nonce" sink nonce, .selector "color" sink color,
       .payload "amount" sink amount, .selector "contractAddress" sink selfAddress] []
  | .insertShieldedCoinSet _ nonce color amount selfAddress =>
    let sink := "public qualified shielded coin Set insertion"
    .publicEffect "insertShieldedCoinSet" .stateWrite .publicActivity sink
      [.selector "nonce" sink nonce, .selector "color" sink color,
       .payload "amount" sink amount, .selector "contractAddress" sink selfAddress] []
  | .writeShieldedCoinCell _ nonce color amount selfAddress =>
    let sink := "public qualified shielded coin Cell write"
    .publicEffect "writeShieldedCoinCell" .stateWrite .publicActivity sink
      [.selector "nonce" sink nonce, .selector "color" sink color,
       .payload "amount" sink amount, .selector "contractAddress" sink selfAddress] []
  | .spendShieldedFromMap _ nonce color amount recipient selfAddress =>
    let sink := "public shielded coin spend"
    .publicEffect "spendShieldedFromMap" .asset .publicActivity sink
      [.selector "nonce" sink nonce, .selector "color" sink color,
       .payload "amount" sink amount, .selector "recipient" sink recipient,
       .selector "contractAddress" sink selfAddress] []
  | .sendShieldedFromMap _ nonce color inputAmount sendAmount recipient selfAddress =>
    let sink := "public partial shielded coin send"
    .publicEffect "sendShieldedFromMap" .asset .publicActivity sink
      [.selector "nonce" sink nonce, .selector "color" sink color,
       .payload "inputAmount" sink inputAmount, .payload "sendAmount" sink sendAmount,
       .selector "recipient" sink recipient,
       .selector "contractAddress" sink selfAddress] []
  | .relayShieldedImmediate nonce color amount recipient selfAddress =>
    let sink := "public immediate shielded contract relay"
    .publicEffect "relayShieldedImmediate" .asset .publicActivity sink
      [.selector "nonce" sink nonce, .selector "color" sink color,
       .payload "amount" sink amount, .selector "recipient" sink recipient,
       .selector "contractAddress" sink selfAddress] []
  | .mintUnshielded domain amount =>
    let sink := "public unshielded mint"
    .publicEffect "mintUnshielded" .asset .publicActivity sink
      [.selector "domain" sink domain, .payload "amount" sink amount] []
  | .incUnshieldedInputs color amount isUnshielded =>
    let sink := "public unshielded input"
    .publicEffect "incUnshieldedInputs" .asset .publicActivity sink
      [.selector "color" sink color, .payload "amount" sink amount,
       .selector "isUnshielded" sink isUnshielded] []
  | .incUnshieldedOutputs color amount isUnshielded =>
    let sink := "public unshielded output"
    .publicEffect "incUnshieldedOutputs" .asset .publicActivity sink
      [.selector "color" sink color, .payload "amount" sink amount,
       .selector "isUnshielded" sink isUnshielded] []
  | .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient =>
    let sink := "public unshielded spend claim"
    .publicEffect "claimUnshieldedCoinSpend" .asset .publicActivity sink
      [.selector "color" sink color, .payload "amount" sink amount,
       .selector "isUnshielded" sink isUnshielded, .selector "isContract" sink isContract,
       .selector "recipient" sink recipient] []
  | .requireContractCaller address =>
    let sink := "required contract caller"
    .publicEffect "requireContractCaller" .call .publicActivity sink [.selector "address" sink address] []
  | .checkpoint => .publicEffect "checkpoint" .checkpoint .publicActivity "public ledger checkpoint" [] []
  | .readCaller destinations =>
    .publicEffect "readCaller" .contextRead .publicActivity "public caller read guard"
      [] (destinations.types.map Prod.fst)
  | .readTokenBalance destination color isUnshielded query =>
    let sink := "public token balance read"
    let selectors : List LedgerOperand :=
      [.selector "color" sink color, .selector "isUnshielded" sink isUnshielded]
    let operands := match query with
      | .exact => selectors
      | .compare _ limit => selectors ++ [.selector "limit" sink limit]
    .publicEffect "readTokenBalance" .contextRead .publicActivity sink operands [destination]
  | .blockTimeCompare destination _ deadline =>
    let sink := "public block-time cutoff"
    .publicEffect "blockTimeCompare" .contextRead .publicActivity sink
      [.selector "deadline" sink deadline] [destination]
  | .emitEvent _ payload =>
    let sink := "public contract event"
    .publicEffect "emitEvent" .event .publicActivity sink [.payload "payload" sink payload] []
  | .readPath state destination keys _ =>
    .publicEffect "readPath" .stateRead .publicActivity s!"public nested map read guard '{state}'"
      [.path s!"public nested map read path '{state}'" keys] [destination]
  | .memberPath state destination keys =>
    .publicEffect "memberPath" .stateRead .publicActivity s!"public nested map membership guard '{state}'"
      [.path s!"public nested map membership path '{state}'" keys] [destination]
  | .mapIsEmpty state destination keys =>
    .publicEffect "mapIsEmpty" .stateRead .publicActivity s!"public map or set emptiness guard '{state}'"
      [.path s!"public map or set emptiness path '{state}'" keys] [destination]
  | .mapSize state destination keys =>
    .publicEffect "mapSize" .stateRead .publicActivity s!"public map or set size guard '{state}'"
      [.path s!"public map or set size path '{state}'" keys] [destination]
  | .counterRead state destination keys =>
    .publicEffect "counterRead" .stateRead .publicActivity s!"public Counter read guard '{state}'"
      [.path s!"public Counter read path '{state}'" keys] [destination]
  | .counterLessThan state destination keys threshold =>
    .publicEffect "counterLessThan" .stateRead .publicActivity s!"public Counter comparison guard '{state}'"
      [.path s!"public Counter comparison path '{state}'" keys,
       .selector "threshold" s!"public Counter comparison threshold '{state}'" threshold] [destination]
  | .counterAdjust state keys _ amount =>
    let sink := s!"public Counter mutation path '{state}'"
    .publicEffect "counterAdjust" .stateWrite .publicActivity sink
      [.path sink keys, .selector "amount" s!"public Counter adjustment amount '{state}'" amount] []
  | .counterReset state keys =>
    let sink := s!"public Counter mutation path '{state}'"
    .publicEffect "counterReset" .stateWrite .publicActivity sink [.path sink keys] []
  | .insertPath state keys _ payload =>
    let sink := s!"public nested map write path '{state}'"
    .publicEffect "insertPath" .stateWrite .publicActivity sink
      [.path sink keys, .payload "value" s!"public nested map write value '{state}'" payload] []
  | .writePath state keys _ payload =>
    let sink := s!"public nested map write path '{state}'"
    .publicEffect "writePath" .stateWrite .publicActivity sink
      [.path sink keys, .payload "value" s!"public nested map write value '{state}'" payload] []
  | .readCompositePath state _ keys _ destinations =>
    .publicEffect "readCompositePath" .stateRead .publicActivity s!"public nested composite read guard '{state}'"
      [.path s!"public nested composite read path '{state}'" keys] (destinations.map Prod.fst)
  | .writeCompositePath state keys _ payloads =>
    let sink := s!"public nested composite write path '{state}'"
    .publicEffect "writeCompositePath" .stateWrite .publicActivity sink
      (.path sink keys :: payloads.zipIdx.map (fun (payload, index) => match payload with
        | .mk _ value =>
          .payload "field" s!"public nested composite write field {index} of '{state}'" value)) []
  | .listLength state destination keys =>
    .publicEffect "listLength" .stateRead .publicActivity s!"public List length guard '{state}'"
      [.path s!"public List length path '{state}'" keys] [destination]
  | .listHead state _ keys _ destinations =>
    .publicEffect "listHead" .stateRead .publicActivity s!"public List head guard '{state}'"
      [.path s!"public List head path '{state}'" keys] (destinations.map Prod.fst)
  | .listPushFront state keys _ payloads =>
    let sink := s!"public List push path '{state}'"
    .publicEffect "listPushFront" .stateWrite .publicActivity sink
      (.path sink keys :: payloads.zipIdx.map (fun (payload, index) => match payload with
        | .mk _ value => .payload "field" s!"public List push field {index} of '{state}'" value)) []
  | .listPopFront state keys =>
    let sink := s!"public List mutation path '{state}'"
    .publicEffect "listPopFront" .stateWrite .publicActivity sink [.path sink keys] []
  | .listReset state keys =>
    let sink := s!"public List mutation path '{state}'"
    .publicEffect "listReset" .stateWrite .publicActivity sink [.path sink keys] []
  | .merkleTreeIsFull state destination =>
    .publicEffect "merkleTreeIsFull" .stateRead .publicActivity s!"public MerkleTree fullness guard '{state}'"
      [] [destination]
  | .merkleTreeCheckRoot state expected destination =>
    .publicEffect "merkleTreeCheckRoot" .stateRead .publicActivity s!"public MerkleTree root-check guard '{state}'"
      [.selector "expected" s!"public MerkleTree root comparison '{state}'" expected] [destination]
  | .merkleTreeInsertHash state hash =>
    let sink := s!"public MerkleTree inserted hash '{state}'"
    .publicEffect "merkleTreeInsertHash" .stateWrite .publicActivity sink [.payload "hash" sink hash] []
  | .merkleTreeInsertHashIndex state hash index =>
    let sink := s!"public MerkleTree indexed hash '{state}'"
    .publicEffect "merkleTreeInsertHashIndex" .stateWrite .publicActivity sink
      [.payload "hash" sink hash, .selector "index" s!"public MerkleTree index '{state}'" index] []
  | .merkleTreeReset state =>
    .publicEffect "merkleTreeReset" .stateWrite .publicActivity s!"public MerkleTree mutation guard '{state}'" [] []
  | .merkleTreeResetHistory state =>
    .publicEffect "merkleTreeResetHistory" .stateWrite .publicActivity s!"public MerkleTree mutation guard '{state}'" [] []
  | .merkleTreeIsFullAt state keys destination =>
    .publicEffect "merkleTreeIsFullAt" .stateRead .publicActivity s!"public nested MerkleTree fullness guard '{state}'"
      [.path s!"public nested MerkleTree path '{state}'" keys] [destination]
  | .merkleTreeCheckRootAt state keys expected destination =>
    .publicEffect "merkleTreeCheckRootAt" .stateRead .publicActivity s!"public nested MerkleTree root-check guard '{state}'"
      [.path s!"public nested MerkleTree path '{state}'" keys,
       .selector "expected" s!"public nested MerkleTree root comparison '{state}'" expected] [destination]
  | .merkleTreeInsertHashAt state keys hash =>
    let sink := s!"public nested MerkleTree path '{state}'"
    .publicEffect "merkleTreeInsertHashAt" .stateWrite .publicActivity sink
      [.path sink keys, .payload "hash" s!"public nested MerkleTree inserted hash '{state}'" hash] []
  | .merkleTreeInsertHashIndexAt state keys hash index =>
    let sink := s!"public nested MerkleTree path '{state}'"
    .publicEffect "merkleTreeInsertHashIndexAt" .stateWrite .publicActivity sink
      [.path sink keys, .payload "hash" s!"public nested MerkleTree indexed hash '{state}'" hash,
       .selector "index" s!"public nested MerkleTree index '{state}'" index] []
  | .merkleTreeResetAt state keys _ _ _ =>
    let sink := s!"public nested MerkleTree reset path '{state}'"
    .publicEffect "merkleTreeResetAt" .stateWrite .publicActivity sink [.path sink keys] []
  | .merkleTreeResetHistoryAt state keys =>
    let sink := s!"public nested HistoricMerkleTree history reset path '{state}'"
    .publicEffect "merkleTreeResetHistoryAt" .stateWrite .publicActivity sink [.path sink keys] []
  | .emptyMapPath state keys =>
    let sink := s!"public empty-map path '{state}'"
    .publicEffect "emptyMapPath" .stateWrite .publicActivity sink [.path sink keys] []
  | .setInsert state keys =>
    let sink := s!"public set insertion path '{state}'"
    .publicEffect "setInsert" .stateWrite .publicActivity sink [.path sink keys] []
  | .removePath state keys =>
    let sink := s!"public nested map removal path '{state}'"
    .publicEffect "removePath" .stateWrite .publicActivity sink [.path sink keys] []

def entrypoint (value : Entrypoint) (control : Origins := []) : Except Diagnostic Unit := do
  unless value.effectSpans.isEmpty || value.effectSpans.length == value.effects.length do
    throw {span := value.span, message := "effect source-span metadata length mismatch"}
  circuit value.circuit control
  let mut env ← inputEnvironment value.circuit
  for output in value.circuit.outputs do
    env := env ++ [(output.name, [])]
  for (effect, index) in value.effects.zipIdx do
    let span := value.effectSpans[index]?.getD value.span
    let guard := value.effectGuardAt index
    match describeEffect effect with
    | .proofConstraint _ predicate =>
      if let some guard := guard then discard (expression env span guard)
      discard (expression env span predicate)
    | .publicEffect _ _ guardPolicy guardSink operands reads =>
      let activeControl ← match guard, guardPolicy with
        | none, _ => pure control
        | some predicate, .publicActivity => pure (merge control (← expression env span predicate))
        | some _, .noSourceGuard =>
          throw {span, message := "native guards are supported only on ledger reads, writes, and require effects"}
      checkSink {description := guardSink, span} [] activeControl
      for operand in operands do
        match operand with
        | .selector _ description value | .payload _ description value =>
          checkSink {description, span} (← expression env span value)
        | .path description keys => checkSink {description, span} (← pathExpression env span keys)
      env := env ++ reads.map (fun name => (name, []))
  for output in value.returns do
    checkSink {description := s!"public entrypoint return '{output.name}'", span := output.span}
      (← expression env output.span output.value) control

def contract (value : Contract) : Except Diagnostic Unit := do
  for entry in value.entrypoints do entrypoint entry

theorem disclosed_value_origins (env : Environment) (span : SourceSpan) (value : Expr ty)
    (result : Origins) (h : origins env value = .ok result) :
    origins env (.disclose span value) = .ok [] := by
  simp [origins, h]
  rfl

theorem sink_accepts_iff (sink : Sink) (payload control : Origins) :
    checkSink sink payload control = .ok () ↔ payload = [] ∧ control = [] := by
  cases payload <;> cases control <;> simp [checkSink]

theorem payload_release_preserves_control_rejection (sink : Sink) (origin : Origin) (rest : Origins) :
    checkSink sink [] (origin :: rest) ≠ .ok () := by simp [checkSink]

end Noctium.Disclosure
