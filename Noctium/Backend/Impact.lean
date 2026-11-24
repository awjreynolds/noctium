import Noctium.IR
import Noctium.GuardedExpression
import Noctium.Field
import Noctium.Semantics
import Noctium.Disclosure
import Noctium.Types.ValueSchema
import Noctium.NativeExpression
import Noctium.Wire
import Lean

namespace Noctium.Backend.Impact

private def expressionCapabilities : Capabilities :=
  {poseidon2 := true, persistentHash32 := true, persistentHashVector32 := true,
    persistentHashNative := true, bytes32Conversions := true, sha512 := true, keccak256 := true, typedBoolean := true, hashToCurve := true, foreignValues := true, foreignArithmetic := true, foreignByteConversions := true, jubjub := true}

private def ledgerCapabilities : Capabilities :=
  {poseidon2 := true, persistentHash32 := true, persistentHashVector32 := true,
    persistentHashNative := true, bytes32Conversions := true, sha512 := true, keccak256 := true, typedBoolean := true, hashToCurve := true, foreignValues := true, foreignArithmetic := true, foreignByteConversions := true, jubjub := true,
    stateCells := true, stateMaps := true}

/-- Symbols in the ledger public-input sequence are source expressions, not
free transcript values. Each symbol must be computed or publicly read by ZKIR. -/
abbrev Scalar := Expr .native

inductive Aligned where
  | field (value : Scalar)
  | foreignKey (kind : Foreign.Kind) (value : Expr (.foreign kind))
  | bit (value : Bool)
  | bitExpr (value : Expr .bool)
  | bytes32 (value : Expr (.bytes 32))
  | bytes (length : Nat) (value : Expr (.bytes length))
  | compress (value : Expr .opaqueBytes)
  | compressString (value : Expr .opaqueString)
  | nativeFields (values : List Scalar)
  | counter (value : Expr (.uint (2 ^ 64 - 1)))
  | u128 (value : Expr (.uint (2 ^ 128 - 1)))
  deriving Repr

private def alignedByteChunkCount (length : Nat) : Nat := (length + 30) / 31

private def alignedByteChunkWidth (length chunkIndex : Nat) : Nat :=
  min 31 (length - chunkIndex * 31)

private def foreignNativeFields : (kind : Foreign.Kind) → Expr (.foreign kind) → List Scalar
  | kind, value => (List.range kind.encodedFieldCount).map fun index =>
      .foreignEncodedField value index

private def nativeFieldSequence (values : List Scalar) : List Scalar :=
  [.native values.length] ++ List.replicate values.length (.native (Field.modulus - 2)) ++ values

private def ledgerFieldAtomCount : LedgerFieldExpr → Nat
  | .mk .jubjubPoint _ => 2
  | .mk (.foreign kind) _ => kind.encodedFieldCount
  | _ => 1

private def ledgerFieldTags : LedgerFieldExpr → List Scalar
  | .mk (.bytes 0) value => [.letE "_noctium_empty_bytes" value (.native 0)]
  | .mk (.bytes length) _ => [.native length]
  | .mk .jubjubPoint _ => List.replicate 2 (.native (Field.modulus - 2))
  | .mk (.foreign kind) _ => List.replicate kind.encodedFieldCount (.native (Field.modulus - 2))
  | .mk _ _ => [.native (Field.modulus - 2)]

private def ledgerFieldPayloads : LedgerFieldExpr → List Scalar
  | .mk .native value => [value]
  | .mk .bool value => [.select value (.native 1) (.native 0)]
  | .mk (.uint _) value => [.cast .native value]
  | .mk (.bytes length) value =>
      (List.range (alignedByteChunkCount length)).map (.bytesField value)
  | .mk .opaqueBytes value => [.opaqueBytesProjection value]
  | .mk .opaqueString value => [.opaqueStringProjection value]
  | .mk .jubjubScalar value => [.jubjubScalarToNative value]
  | .mk .jubjubPoint value => [.jubjubCoordinate value 0, .jubjubCoordinate value 1]
  | .mk (.foreign kind) value => foreignNativeFields kind value

private def shieldedCoinReadTypes : List Ty :=
  [.bytes 32, .bytes 32, .uint (2 ^ 128 - 1), .uint (2 ^ 64 - 1)]

private def shieldedCoinRecordFieldNames : List String :=
  ["nonce", "color", "value", "mtIndex"]

private def asciiAlpha (character : Char) : Bool :=
  let code := character.toNat
  decide (65 ≤ code ∧ code ≤ 90) || decide (97 ≤ code ∧ code ≤ 122)

private def asciiDigit (character : Char) : Bool :=
  let code := character.toNat
  decide (48 ≤ code ∧ code ≤ 57)

private def qualifiedRecordIdentifierValid (identifier : String) : Bool :=
  let validSegment (segment : String) : Bool :=
    match segment.toList with
    | [] => false
    | first :: rest =>
        (first == '_' || asciiAlpha first) &&
          rest.all (fun character => character == '_' || asciiAlpha character || asciiDigit character)
  (identifier.splitOn ".").all validSegment

private def isShieldedCoinRecordSchema (schema : Lean.Json) : Bool :=
  match (schema.getObjVal? "id" >>= Lean.Json.getStr?).toOption with
  | none => false
  | some identifier =>
      qualifiedRecordIdentifierValid identifier &&
        schema == Lean.Json.mkObj [
          ("id", Lean.toJson identifier),
          ("fields", Lean.toJson (shieldedCoinRecordFieldNames.zip
            (shieldedCoinReadTypes.map Noctium.NativeExpression.typeName) |>.map fun (name, type) =>
              Lean.Json.mkObj [("name", Lean.toJson name), ("type", Lean.toJson type)]))]

private def shieldedCoinLedgerFieldSequence (values : List LedgerFieldExpr) : List Scalar :=
  [.native 4, .native 32, .native 32, .native 16, .native 8] ++
    values.flatMap ledgerFieldPayloads

private def ledgerFieldSequence (values : List LedgerFieldExpr) : List Scalar :=
  if values.all (fun value => value.ty == .native) then
    nativeFieldSequence (values.flatMap ledgerFieldPayloads)
  else
    [.native (values.foldl (fun count value => count + ledgerFieldAtomCount value) 0)] ++
      values.flatMap ledgerFieldTags ++ values.flatMap ledgerFieldPayloads

private def nativeFieldExpressions (values : List Scalar) : List LedgerFieldExpr :=
  values.map fun value => .mk .native value

private def refLedgerFieldExpr (name : String) (ty : Ty) : LedgerFieldExpr :=
  match ty with
  | .native => .mk .native (.ref name)
  | .bool => .mk .bool (.ref name)
  | .uint maximum => .mk (.uint maximum) (.ref name)
  | .bytes length => .mk (.bytes length) (.ref name)
  | .opaqueBytes => .mk .opaqueBytes (.ref name)
  | .opaqueString => .mk .opaqueString (.ref name)
  | .jubjubScalar => .mk .jubjubScalar (.ref name)
  | .jubjubPoint => .mk .jubjubPoint (.ref name)
  | .foreign kind => .mk (.foreign kind) (.ref name)

private def natBytes (n : Nat) : List Nat := if n == 0 then [] else go n (n.log2 / 8 + 1)
where
  go (n : Nat) : Nat → List Nat
    | 0 => []
    | fuel + 1 => n % 256 :: go (n / 256) fuel

inductive Op where
  | dup
  | index (slot : Nat) (pushPath : Bool := false)
  | mapIndex (slot : Nat) (key : Aligned)
  | indexRecordPath (slot : Nat) (schema : Lean.Json) (values : List LedgerFieldExpr)
      (keys : List Aligned)
  | indexPath (slot : Nat) (pushPath : Bool) (keys : List Aligned)
  | push (value : Aligned) (storage : Bool := false)
  | newMap
  | popeq (value : Aligned)
  | pushFields (schema : Lean.Json) (values : List LedgerFieldExpr) (storage : Bool := false)
  | popeqFields (schema : Lean.Json) (values : List LedgerFieldExpr)
  | member
  | insert (levels : Nat)
  | addImmediate (amount : Expr (.uint (2 ^ 32 - 1)))
  | subImmediate (amount : Expr (.uint (2 ^ 32 - 1)))
  | listLength (slot : Nat) (keys : List Aligned) (value : Expr (.uint (2 ^ 64 - 1)))
  | mapSize (slot : Nat) (keys : List Aligned) (value : Expr (.uint (2 ^ 64 - 1)))
  | mapIsEmpty (slot : Nat) (keys : List Aligned) (destination : String)
  | counterLessThan (slot : Nat) (keys : List Aligned)
      (threshold : Expr (.uint (2 ^ 64 - 1))) (destination : String)
  | merkleTreeIsFull (slot depth : Nat) (destination : String)
  | merkleTreeCheckRoot (slot depth : Nat) (expected : Expr .native) (destination : String)
  | merkleTreeInsertHash (slot depth : Nat) (hash : Expr (.bytes 32))
  | merkleTreeInsertHashIndex (slot depth : Nat) (hash : Expr (.bytes 32))
      (index : Expr (.uint (2 ^ 64 - 1)))
  | merkleTreeReset (slot depth : Nat)
  | historicMerkleTreeCheckRoot (slot depth : Nat) (expected : Expr .native)
      (destination : String)
  | historicMerkleTreeInsertHash (slot depth : Nat) (hash : Expr (.bytes 32))
  | historicMerkleTreeInsertHashIndex (slot depth : Nat) (hash : Expr (.bytes 32))
      (index : Expr (.uint (2 ^ 64 - 1)))
  | historicMerkleTreeReset (slot depth : Nat)
  | merkleTreeResetHistory (slot depth : Nat)
  | merkleTreeIsFullAt (slot depth : Nat) (keys : List Aligned) (destination : String)
  | merkleTreeCheckRootAt (slot depth : Nat) (historic : Bool) (keys : List Aligned)
      (expected : Expr .native) (destination : String)
  | merkleTreeInsertHashAt (slot depth : Nat) (historic : Bool) (keys : List Aligned)
      (hash : Expr (.bytes 32))
  | merkleTreeInsertHashIndexAt (slot depth : Nat) (historic : Bool) (keys : List Aligned)
      (hash : Expr (.bytes 32)) (index : Expr (.uint (2 ^ 64 - 1)))
  | merkleTreeResetAt (slot depth : Nat) (historic : Bool) (keys : List Aligned)
      (emptyHistory : Bool := false)
  | merkleTreeResetHistoryAt (slot depth : Nat) (keys : List Aligned)
  | listHead (slot : Nat) (keys : List Aligned) (schema : Lean.Json) (values : List LedgerFieldExpr)
  | listPushFront (slot : Nat) (keys : List Aligned) (schema : Lean.Json) (values : List LedgerFieldExpr)
  | listPushFrontCoin (slot : Nat) (keys : List Aligned) (schema : Lean.Json)
      (nonce color : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 128 - 1)))
      (commitment : Expr (.bytes 32))
  | listPushFrontCoinTo (slot : Nat) (keys : List Aligned) (schema : Lean.Json)
      (nonce color : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 128 - 1)))
      (isContract : Expr .bool) (recipient commitment : Expr (.bytes 32))
  | listPopFront (slot : Nat) (keys : List Aligned)
  | listReset (slot : Nat) (keys : List Aligned)
  | mapRemove (slot : Nat) (keys : List Aligned)
  | mapRemoveRecord (slot : Nat) (schema : Lean.Json) (keys : List Aligned)
      (values : List LedgerFieldExpr)
  | claimContractCall (address entryPointHash : Expr (.bytes 32)) (commitment : Scalar)
  | claimShielded (kind : ShieldedClaimKind) (digest : Expr (.bytes 32))
  | receiveShieldedToMap (slot : Nat) (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (commitment : Expr (.bytes 32))
  | insertShieldedCoinMap (slot : Nat) (key nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (isContract : Expr .bool)
      (recipient commitment : Expr (.bytes 32)) (keys : List Aligned)
  | insertShieldedCoinSet (slot : Nat) (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (commitment : Expr (.bytes 32))
      (keys : List Aligned)
  | insertShieldedCoinSetTo (slot : Nat) (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (isContract : Expr .bool)
      (recipient commitment : Expr (.bytes 32)) (keys : List Aligned)
  | writeShieldedCoinCell (slot : Nat) (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (commitment : Expr (.bytes 32))
  | writeShieldedCoinCellTo (slot : Nat) (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (isContract : Expr .bool)
      (recipient commitment : Expr (.bytes 32))
  | spendShieldedFromMap (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1))) (recipient nullifier outputCommitment : Expr (.bytes 32))
  | mergeShieldedFromMap
      (nonceA colorA : Expr (.bytes 32)) (amountA : Expr (.uint (2 ^ 128 - 1)))
      (nonceB colorB : Expr (.bytes 32)) (amountB : Expr (.uint (2 ^ 128 - 1)))
      (outputNonce outputColor : Expr (.bytes 32))
      (outputAmount : Expr (.uint (2 ^ 128 - 1)))
      (nullifierA nullifierB outputCommitment : Expr (.bytes 32))
      (stagedCommitment : Option (Expr (.bytes 32)))
  | sendShieldedFromMap (nonce color : Expr (.bytes 32))
      (inputAmount sendAmount : Expr (.uint (2 ^ 128 - 1)))
      (recipient nullifier outputCommitment changeCommitment : Expr (.bytes 32))
  | relayShieldedImmediate (nonce color : Expr (.bytes 32))
      (amount : Expr (.uint (2 ^ 128 - 1)))
      (recipient inputCommitment nullifier outputCommitment : Expr (.bytes 32))
  | mintShielded (domain : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 64 - 1)))
  | mintUnshielded (domain : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 64 - 1)))
  | incUnshieldedInputs (color : Expr (.bytes 32)) (amount : Expr (.uint balanceMaximum))
      (isUnshielded : Expr .bool)
  | incUnshieldedOutputs (color : Expr (.bytes 32)) (amount : Expr (.uint balanceMaximum))
      (isUnshielded : Expr .bool)
  | claimUnshieldedCoinSpend (color : Expr (.bytes 32)) (amount : Expr (.uint balanceMaximum))
      (isUnshielded isContract : Expr .bool) (recipient : Expr (.bytes 32))
  | requireContractCaller (address : Expr (.bytes 32))
  | checkpoint
  | readCaller (destinations : CallerBindings)
  | readContractAddress (destination : String)
  | readTokenBalance (destination : String) (color : Expr (.bytes 32))
      (isUnshielded : Expr .bool) (query : BalanceQuery)
  | blockTimeCompare (destination : String) (before : Bool)
      (deadline : Expr (.uint (2 ^ 64 - 1)))
  | emitEvent (kind : EventKind) (payload : Expr (.bytes kind.payloadSize))

private def claimContractCallFieldGroups
    (address entryPointHash : Expr (.bytes 32)) (commitment : Scalar) : List (List Scalar) :=
  [ [.native 0x40]
  , [.native 0x80, .native 1, .native 1, .native 3]
  , [.native 0x30]
  , [.native 0x04]
  , [.native 0x10, .native 1, .native 3, .native 32, .native 32,
      .native (Field.modulus - 2),
      .bytesField address 0, .bytesField address 1,
      .bytesField entryPointHash 0, .bytesField entryPointHash 1,
      commitment]
  , [.native 0x17, .native 160]
  , [.native 0x10, .native 0]
  , [.native 0xa2]
  , [.native 0x40]
  ]

private def accumulateTokenFields (slot : Nat) (key encodedAmount : List Scalar) :
    List (List Scalar) :=
  [[.native 0x40], [.native 0x80, .native 1, .native 1, .native slot],
    [.native 0x10, .native 1] ++ key, [.native 0x31], [.native 0x31], [.native 0x18],
    encodedAmount, [.native 0x40], [.native 0x08], [.native 0x12, .native 4],
    [.native 0x32], [.native 0x32], [.native 0x60, .native (Field.modulus - 1)],
    [.native 0x14], [.native 0xa2], [.native 0x40]]

/-- Field-representation vectors match ledger-9 onchain-vm/src/ops.rs and
transient-crypto/src/fab.rs. Map-key alignment follows the declared key type. -/
def Aligned.fields : Aligned → List Scalar
  | .field value => [.native 1, .native (Field.modulus - 2), value]
  | .foreignKey kind value => nativeFieldSequence (foreignNativeFields kind value)
  | .bit value => [.native 1, .native 1, .native (if value then 1 else 0)]
  | .bitExpr value => [.native 1, .native 1,
      .select value (.native 1) (.native 0)]
  | .bytes32 value => [.native 1, .native 32,
      .bytesField value 0, .bytesField value 1]
  | .bytes 0 value => [.native 1, .letE "_noctium_empty_bytes" value (.native 0)]
  | .bytes length value => [.native 1, .native length] ++
      (List.range (alignedByteChunkCount length)).map (.bytesField value)
  | .compress value => [.native 1, .native (Field.modulus - 1), .opaqueBytesProjection value]
  | .compressString value => [.native 1, .native (Field.modulus - 1), .opaqueStringProjection value]
  | .nativeFields values => nativeFieldSequence values
  | .counter value => [.native 1, .native 8, .cast .native value]
  | .u128 value => [.native 1, .native 16, .cast .native value]

private def mintFieldGroups (slot : Nat) (domain : Expr (.bytes 32))
    (amount : Expr (.uint (2 ^ 64 - 1))) : List (List Scalar) :=
  accumulateTokenFields slot (Aligned.bytes32 domain).fields
    ([.native 0x10, .native 1] ++ (Aligned.counter amount).fields)

private def shieldedCoinDigest (domainBytes : String) (tag : Nat) (nonce color : Expr (.bytes 32))
    (amount : Expr (.uint (2 ^ 128 - 1))) (address : Expr (.bytes 32)) : Expr (.bytes 32) :=
  let domain : Expr (.bytes 21) := .bytesLiteral 21 (domainBytes.toList.map Char.toNat)
  let amountBytes : Expr (.bytes 16) :=
    .sliceBytes (.toBytes32 (.cast .native amount)) 0 16
  let recipientTag : Expr (.bytes 1) := .bytesLiteral 1 [tag]
  let preimage : Expr (.bytes 134) :=
    .concatBytes domain (.concatBytes nonce (.concatBytes color
      (.concatBytes amountBytes (.concatBytes recipientTag address))))
  .sha256 preimage

private def shieldedCoinDigestForRecipient (domainBytes : String)
    (nonce color : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 128 - 1)))
    (isContract : Expr .bool) (recipient : Expr (.bytes 32)) : Expr (.bytes 32) :=
  let domain : Expr (.bytes 21) := .bytesLiteral 21 (domainBytes.toList.map Char.toNat)
  let amountBytes : Expr (.bytes 16) :=
    .sliceBytes (.toBytes32 (.cast .native amount)) 0 16
  let tagNative : Expr .native := .select isContract (.native 0) (.native 1)
  let recipientTag : Expr (.bytes 1) := .sliceBytes (.toBytes32 tagNative) 0 1
  let preimage : Expr (.bytes 134) :=
    .concatBytes domain (.concatBytes nonce (.concatBytes color
      (.concatBytes amountBytes (.concatBytes recipientTag recipient))))
  .sha256 preimage

private def spendShieldedOp (nonce color : Expr (.bytes 32))
    (amount : Expr (.uint (2 ^ 128 - 1))) (recipient selfAddress : Expr (.bytes 32)) : Op :=
  let evolved := Wire.shieldedOutputNonce nonce
  let nullifier := shieldedCoinDigest "midnight:zswap-cn[v1]" 0 nonce color amount selfAddress
  let output := shieldedCoinDigest "midnight:zswap-cc[v1]" 1 evolved color amount recipient
  .spendShieldedFromMap nonce color amount recipient nullifier output

private def mergeShieldedOp (nonceA colorA : Expr (.bytes 32))
    (amountA : Expr (.uint (2 ^ 128 - 1)))
    (nonceB colorB : Expr (.bytes 32))
    (amountB : Expr (.uint (2 ^ 128 - 1)))
    (selfAddress : Expr (.bytes 32)) (stagedInput : Bool) : Op :=
  let outputNonce := Wire.shieldedOutputNonce nonceA
  let outputColor := colorA
  let outputAmount : Expr (.uint (2 ^ 128 - 1)) :=
    .cast (.uint (2 ^ 128 - 1)) (.uadd amountA amountB)
  let nullifierA :=
    shieldedCoinDigest "midnight:zswap-cn[v1]" 0 nonceA colorA amountA selfAddress
  let nullifierB :=
    shieldedCoinDigest "midnight:zswap-cn[v1]" 0 nonceB colorB amountB selfAddress
  let outputCommitment := shieldedCoinDigest
    "midnight:zswap-cc[v1]" 0 outputNonce outputColor outputAmount selfAddress
  let stagedCommitment := if stagedInput then
    some (shieldedCoinDigest "midnight:zswap-cc[v1]" 0 nonceB colorB amountB selfAddress)
    else none
  .mergeShieldedFromMap nonceA colorA amountA nonceB colorB amountB
    outputNonce outputColor outputAmount nullifierA nullifierB outputCommitment stagedCommitment

private def sendShieldedOp (nonce color : Expr (.bytes 32))
    (inputAmount sendAmount : Expr (.uint (2 ^ 128 - 1)))
    (recipient selfAddress : Expr (.bytes 32)) : Op :=
  let nullifier := shieldedCoinDigest "midnight:zswap-cn[v1]" 0 nonce color inputAmount selfAddress
  let sentNonce := Wire.shieldedOutputNonce nonce
  let output := shieldedCoinDigest "midnight:zswap-cc[v1]" 1 sentNonce color sendAmount recipient
  let changeNonce := Wire.shieldedChangeNonce nonce
  let changeAmount : Expr (.uint (2 ^ 128 - 1)) := .usub inputAmount sendAmount
  let change := shieldedCoinDigest "midnight:zswap-cc[v1]" 0 changeNonce color changeAmount selfAddress
  .sendShieldedFromMap nonce color inputAmount sendAmount recipient nullifier output change

private def relayShieldedOp (nonce color : Expr (.bytes 32))
    (amount : Expr (.uint (2 ^ 128 - 1))) (recipient selfAddress : Expr (.bytes 32)) : Op :=
  let inputCommitment := shieldedCoinDigest "midnight:zswap-cc[v1]" 0 nonce color amount selfAddress
  let nullifier := shieldedCoinDigest "midnight:zswap-cn[v1]" 0 nonce color amount selfAddress
  let outputNonce := Wire.shieldedOutputNonce nonce
  let outputCommitment :=
    shieldedCoinDigest "midnight:zswap-cc[v1]" 0 outputNonce color amount recipient
  .relayShieldedImmediate nonce color amount recipient inputCommitment nullifier outputCommitment

private def shieldedClaimFieldGroups (effectSlot : Nat) (digest : Expr (.bytes 32)) :
    List (List Scalar) :=
  [[.native 0x40], [.native 0x80, .native 1, .native 1, .native effectSlot],
    [.native 0x10, .native 1, .native 1, .native 32,
      .bytesField digest 0, .bytesField digest 1],
    [.native 0x10, .native 0], [.native 0xa2], [.native 0x40]]

private def indexPathFields (slot : Nat) (pushPath : Bool) (keys : List Aligned) : List Scalar :=
  [.native ((if pushPath then 0x70 else 0x50) + keys.length)] ++
    (Aligned.field (.native slot)).fields ++ keys.flatMap Aligned.fields

private def shieldedCoinPushFields (nonce color : Expr (.bytes 32))
    (amount : Expr (.uint (2 ^ 128 - 1))) : List Scalar :=
  [.native 0x10, .native 1, .native 3, .native 32, .native 32, .native 16,
    .bytesField nonce 0, .bytesField nonce 1, .bytesField color 0, .bytesField color 1,
    .cast .native amount]

private def shieldedCoinCellFieldGroups (slot : Nat) (nonce color : Expr (.bytes 32))
    (amount : Expr (.uint (2 ^ 128 - 1))) (commitment : Expr (.bytes 32)) : List (List Scalar) :=
  [ [.native 0x10, .native 1, .native 1, .native 1, .native slot]
  , [.native 0x33]
  , [.native 0x10, .native 1] ++ (Aligned.bytes32 commitment).fields
  , [.native 0x61, .native 1, .native 1, .native 1, .native (Field.modulus - 1)]
  , shieldedCoinPushFields nonce color amount
  , [.native 0x40]
  , [.native 0x17, .native 91]
  , [.native 0x91]
  ]

private def shieldedCoinMapIndexPathFields (slot : Nat) (cached : Bool)
    (parents : List Aligned) : List Scalar :=
  [.native ((if cached then 0x60 else 0x50) + parents.length),
    .native 1, .native 1, .native slot] ++ parents.flatMap Aligned.fields

private def pushAlignedBytes32Fields (value : Aligned) : List Scalar :=
  [.native 0x10, .native 1] ++ value.fields

private def shieldedCoinMapParentRebuildFieldGroups (slot : Nat)
    (keys : List Aligned) : List (List Scalar) :=
  keys.reverse.zipIdx.flatMap fun (nextParent, reverseIndex) =>
    let parents := keys.take (keys.length - reverseIndex - 1)
    [[.native 0x31], shieldedCoinMapIndexPathFields slot true parents,
      pushAlignedBytes32Fields nextParent,
      [.native 0x40], [.native 0x41], [.native 0xa1]]

private def shieldedCoinSetFieldGroups (slot : Nat) (keys : List Aligned)
    (nonce color : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 128 - 1)))
    (commitment : Expr (.bytes 32)) : List (List Scalar) :=
  if keys.length ≤ 5 then
    [ [.native (0x70 + keys.length), .native 1, .native 1, .native slot] ++
        keys.flatMap Aligned.fields
    , [.native (0x34 + 2 * keys.length)]
    , [.native 0x10, .native 1] ++ (Aligned.bytes32 commitment).fields
    , [.native 0x61, .native 1, .native 1, .native 1, .native (Field.modulus - 1)]
    , shieldedCoinPushFields nonce color amount
    , [.native 0x40]
    , [.native 0x17, .native 91]
    , [.native 0x11, .native 0]
    , [.native 0x91]
    , [.native (0xa1 + keys.length)]
    ]
  else
    [ [.native 0x32]
    , [.native 0x10, .native 1] ++ (Aligned.bytes32 commitment).fields
    , [.native 0x61, .native 1, .native 1, .native 1, .native (Field.modulus - 1)]
    , shieldedCoinPushFields nonce color amount
    , [.native 0x40]
    , [.native 0x17, .native 91]
    , [.native 0x31]
    , shieldedCoinMapIndexPathFields slot false keys
    , [.native 0x40]
    , [.native 0x11, .native 0]
    , [.native 0x91]
    ] ++ shieldedCoinMapParentRebuildFieldGroups slot keys ++
    [[.native 0x10, .native 1, .native 1, .native 1, .native slot],
      [.native 0x40], [.native 0xa1]]

private def shieldedCoinMapInsertFieldGroups (slot : Nat) (keys : List Aligned)
    (key nonce color : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 128 - 1)))
    (commitment : Expr (.bytes 32)) : List (List Scalar) := Id.run do
  if keys.length ≤ 5 then
    return [[.native (0x70 + keys.length), .native 1, .native 1, .native slot] ++
        keys.flatMap Aligned.fields,
      [.native 0x10, .native 1] ++ (Aligned.bytes32 key).fields,
      [.native (0x35 + keys.length * 2)],
      [.native 0x10, .native 1] ++ (Aligned.bytes32 commitment).fields,
      [.native 0x61, .native 1, .native 1, .native 1, .native (Field.modulus - 1)],
      shieldedCoinPushFields nonce color amount,
      [.native 0x40], [.native 0x17, .native 91], [.native 0x91], [.native (0xa1 + keys.length)]]

  let parentGroups := shieldedCoinMapParentRebuildFieldGroups slot keys
  let groups :=
    [[.native 0x32], pushAlignedBytes32Fields (.bytes32 commitment),
      [.native 0x61, .native 1, .native 1, .native 1, .native (Field.modulus - 1)],
      shieldedCoinPushFields nonce color amount,
      [.native 0x40], [.native 0x17, .native 91],
      [.native 0x31], shieldedCoinMapIndexPathFields slot false keys,
      pushAlignedBytes32Fields (.bytes32 key),
      [.native 0x40], [.native 0x41], [.native 0x91]] ++
      parentGroups ++
      [[.native 0x10, .native 1, .native 1, .native 1, .native slot],
        [.native 0x40], [.native 0xa1]]
  return groups

private def receiveShieldedFieldGroups (slot : Nat) (nonce color : Expr (.bytes 32))
    (amount : Expr (.uint (2 ^ 128 - 1))) (commitment : Expr (.bytes 32)) : List (List Scalar) :=
  shieldedClaimFieldGroups 1 commitment ++
    shieldedCoinMapInsertFieldGroups slot [] nonce nonce color amount commitment

private def listIndexFields (index : Nat) : List Scalar :=
  [.native 0x50, .native 1, .native 1, .native index]

private def shieldedCoinInfoFields (nonce color : Expr (.bytes 32))
    (amount : Expr (.uint (2 ^ 128 - 1))) : List Scalar :=
  [.native 3, .native 32, .native 32, .native 16,
    .bytesField nonce 0, .bytesField nonce 1,
    .bytesField color 0, .bytesField color 1, .cast .native amount]

/-- Ledger 9 list prepend with a transaction-local qualified index. Paths up
to four parents retain the compact cached fragment. Deeper paths build the
List node and rebuild parent Maps with one-key Ins operations. -/
private def listPushFrontCoinFieldGroups (slot : Nat) (keys : List Aligned)
    (nonce color : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 128 - 1)))
    (commitment : Expr (.bytes 32)) : List (List Scalar) :=
  let pushU8 (value : Nat) : List Scalar :=
    [.native 0x10, .native 1, .native 1, .native 1, .native value]
  if keys.length ≤ 4 then
    [ [.native (0x70 + keys.length), .native 1, .native 1, .native slot] ++
        keys.flatMap Aligned.fields
    , [.native 0x30]
    , listIndexFields 2
    , [.native 0x0e, .native 1]
    , [.native 0x11, .native 51, .native 0, .native 0, .native 0]
    , pushU8 0
    , [.native (0x30 + 7 + keys.length * 2)]
    , [.native 0x10, .native 1] ++ (Aligned.bytes32 commitment).fields
    , [.native 0x61, .native 1, .native 1, .native 1, .native (Field.modulus - 1)]
    , [.native 0x10, .native 1] ++ shieldedCoinInfoFields nonce color amount
    , [.native 0x40]
    , [.native 0x17, .native 91]
    , [.native 0xa1]
    , [.native 0x40]
    , pushU8 2
    , [.native 0x40]
    , [.native 0xa1]
    , [.native 0x40]
    , pushU8 1
    , [.native 0x40]
    , [.native (0xa0 + keys.length + 2)]
    ]
  else
    let cachedIndexPath (parents : List Aligned) : List Scalar :=
      [.native (0x60 + parents.length), .native 1, .native 1, .native slot] ++
        parents.flatMap Aligned.fields
    let pushAlignedBytes32 (value : Aligned) : List Scalar :=
      [.native 0x10, .native 1] ++ value.fields
    let insertParentGroups (nextParent : Aligned) (parents : List Aligned) :
        List (List Scalar) :=
      [[.native 0x31], cachedIndexPath parents, pushAlignedBytes32 nextParent,
        [.native 0x40], [.native 0x41], [.native 0xa1]]
    let parentGroups := keys.reverse.zipIdx.flatMap fun (nextParent, reverseIndex) =>
      let parents := keys.take (keys.length - reverseIndex - 1)
      insertParentGroups nextParent parents
    [ [.native 0x32]
    , [.native 0x10, .native 1] ++ (Aligned.bytes32 commitment).fields
    , [.native 0x61, .native 1, .native 1, .native 1, .native (Field.modulus - 1)]
    , shieldedCoinPushFields nonce color amount
    , [.native 0x40]
    , [.native 0x17, .native 91]
    , [.native 0x31]
    , [.native (0x50 + keys.length), .native 1, .native 1, .native slot] ++
        keys.flatMap Aligned.fields
    , [.native 0x30]
    , listIndexFields 2
    , [.native 0x0e, .native 1]
    , [.native 0x11, .native 51, .native 0, .native 0, .native 0]
    , [.native 0x40]
    , pushU8 2
    , [.native 0x40]
    , [.native 0x91]
    , [.native 0x40]
    , pushU8 1
    , [.native 0x40]
    , [.native 0x91]
    , [.native 0x40]
    , pushU8 0
    , [.native 0x40]
    , [.native 0x91]
    ] ++ parentGroups ++
    [pushU8 slot, [.native 0x40], [.native 0xa1]]

private def mapIsEmptyFieldGroups (slot : Nat) (keys : List Aligned)
    (destination : String) : List (List Scalar) :=
  [[.native 0x30], indexPathFields slot false keys, [.native 0x04],
    [.native 0x10, .native 1] ++ (Aligned.counter (.uint (2 ^ 64 - 1) 0)).fields,
    [.native 0x02], [.native 0x0d] ++ (Aligned.bitExpr (.ref destination)).fields]

private def counterLessThanFieldGroups (slot : Nat) (keys : List Aligned)
    (threshold : Expr (.uint (2 ^ 64 - 1))) (destination : String) : List (List Scalar) :=
  [[.native 0x30], indexPathFields slot false keys,
    [.native 0x10, .native 1] ++ (Aligned.counter threshold).fields,
    [.native 0x01], [.native 0x0c] ++ (Aligned.bitExpr (.ref destination)).fields]

private def merkleTreeIndexFields (index : Nat) (pushPath : Bool) : List Scalar :=
  [.native (if pushPath then 0x70 else 0x50), .native 1, .native 1, .native index]

private def merkleTreeIsFullFieldGroups (slot depth : Nat) (destination : String) (keys : List Aligned := []) :
    List (List Scalar) :=
  let capacity : Expr (.uint (2 ^ 64 - 1)) := .uint (2 ^ 64 - 1) (2 ^ depth)
  [[.native 0x30], indexPathFields slot false keys, listIndexFields 1,
    [.native 0x10, .native 1] ++ (Aligned.counter capacity).fields,
    [.native 0x01], [.native 0x08],
    [.native 0x0d] ++ (Aligned.bitExpr (.ref destination)).fields]

private def merkleTreeCheckRootFieldGroups (slot : Nat) (expected : Expr .native)
    (destination : String) (keys : List Aligned := []) : List (List Scalar) :=
  [[.native 0x30], indexPathFields slot false keys, merkleTreeIndexFields 0 false,
    [.native 0x0a], [.native 0x10, .native 1] ++ (Aligned.field expected).fields,
    [.native 0x02], [.native 0x0d] ++ (Aligned.bitExpr (.ref destination)).fields]

private def historicMerkleTreeCheckRootFieldGroups (slot : Nat) (expected : Expr .native)
    (destination : String) (keys : List Aligned := []) : List (List Scalar) :=
  [ [.native 0x30]
  , indexPathFields slot false keys
  , merkleTreeIndexFields 2 false
  , [.native 0x10, .native 1] ++ (Aligned.field expected).fields
  , [.native 0x18]
  , [.native 0x0d] ++ (Aligned.bitExpr (.ref destination)).fields
  ]

-- Insert the current root into the history set, then write the tree state back.
private def recordHistoricRootFieldGroups (keys : List Aligned) : List (List Scalar) :=
  [ merkleTreeIndexFields 2 true
  , [.native 0x32]
  , merkleTreeIndexFields 0 false
  , [.native 0x0a]
  , [.native 0x11, .native 0]
  , [.native 0x91]
  , [.native (0xa2 + keys.length)]
  ]

private def merkleTreeInsertHashFieldGroups (slot : Nat) (hash : Expr (.bytes 32))
    (historic : Bool := false) (keys : List Aligned := []) : List (List Scalar) :=
  [ indexPathFields slot true keys
  , merkleTreeIndexFields 0 true
  , [.native 0x32]
  , listIndexFields 1
  , [.native 0x11, .native 1] ++ (Aligned.bytes32 hash).fields
  , [.native 0x91]
  , [.native 0xa1]
  , merkleTreeIndexFields 1 true
  , [.native 0x0e, .native 1]
  ] ++ (if historic then [[.native 0xa1]] ++ recordHistoricRootFieldGroups keys
    else [[.native (0xa2 + keys.length)]])

private def merkleTreeInsertHashIndexFieldGroups (slot : Nat)
    (hash : Expr (.bytes 32)) (index : Expr (.uint (2 ^ 64 - 1)))
    (historic : Bool := false) (keys : List Aligned := []) : List (List Scalar) :=
  [ indexPathFields slot true keys
  , merkleTreeIndexFields 0 true
  , [.native 0x10, .native 1] ++ (Aligned.counter index).fields
  , [.native 0x11, .native 1] ++ (Aligned.bytes32 hash).fields
  , [.native 0x92]
  , merkleTreeIndexFields 1 true
  , [.native 0x10, .native 1] ++ (Aligned.counter index).fields
  , [.native 0x0e, .native 1]
  , [.native 0x31]
  , [.native 0x31]
  , [.native 0x01]
  , [.native 0x12, .native 2]
  , [.native 0x0b]
  , [.native 0x13, .native 2]
  , [.native 0x40]
  , [.native 0x0b]
  , [.native 0x91]
  ] ++ (if historic then recordHistoricRootFieldGroups keys else [[.native (0xa1 + keys.length)]])

private def blankMerkleTreeFields (depth : Nat) (historic : Bool)
    (emptyHistory : Bool := false) : List Scalar :=
  let stateArrayTag := 3 + (if historic then 3 else 2) * 16
  let blankTreeTag := 4 + depth * 16
  let zeroCount : Expr (.uint (2 ^ 64 - 1)) := .uint (2 ^ 64 - 1) 0
  let history := if historic then
      if emptyHistory then [.native 2]
      else [.native (2 + 16)] ++ (Aligned.field (.native 0)).fields ++ [.native 0]
    else []
  [.native 0x11, .native stateArrayTag, .native blankTreeTag, .native 1] ++
    (Aligned.counter zeroCount).fields ++ history

private def merkleTreeResetFieldGroups (slot depth : Nat) (historic : Bool := false) :
    List (List Scalar) :=
  [ [.native 0x10, .native 1] ++ (Aligned.field (.native slot)).fields
  , blankMerkleTreeFields depth historic
  , [.native 0x91]
  ]

private def merkleTreeResetAtFieldGroups (slot depth : Nat) (historic : Bool)
    (keys : List Aligned) (emptyHistory : Bool := false) : List (List Scalar) :=
  match keys.getLast? with
  | none => []
  | some finalKey =>
    [ indexPathFields slot true (keys.take (keys.length - 1))
    , [.native 0x10, .native 1] ++ finalKey.fields
    , blankMerkleTreeFields depth historic emptyHistory
    , [.native (0x91 + keys.length)]
    ]

private def merkleTreeResetHistoryFieldGroups (slot : Nat) (keys : List Aligned := []) :
    List (List Scalar) :=
  [ indexPathFields slot true keys
  , [.native 0x10, .native 1, .native 1, .native 1, .native 2]
  , [.native 0x11, .native 2]
  , [.native 0x32]
  , merkleTreeIndexFields 0 false
  , [.native 0x0a]
  , [.native 0x11, .native 0]
  , [.native (0xa3 + keys.length)]
  ]

private def requireContractCallerFieldGroups (address : Expr (.bytes 32)) : List (List Scalar) :=
  -- Query context is two stack slots down. Context slot six holds the tagged caller.
  [[.native 0x32], listIndexFields 6,
    [.native 0x0c, .native 3, .native 1, .native 32, .native 32,
      .native 1, .bytesField address 0, .bytesField address 1, .native 0, .native 0]]

private def contractAddressFieldGroups (destination : String) : List (List Scalar) :=
  -- Query context is two stack slots down. Context slot zero holds this contract's address.
  [[.native 0x32], listIndexFields 0,
    [.native 0x0c] ++ (Aligned.bytes32 (.ref destination)).fields]

private def blockTimeFieldGroups (destination : String) (before : Bool)
    (deadline : Expr (.uint (2 ^ 64 - 1))) : List (List Scalar) :=
  let push := [.native 0x10, .native 1] ++ (Aligned.counter deadline).fields
  let comparison := [[.native 0x01], [.native 0x0c] ++ (Aligned.bitExpr (.ref destination)).fields]
  let operands := if before then [[.native 0x32], listIndexFields 2, push]
    else [push, [.native 0x33], listIndexFields 2]
  operands ++ comparison

private def listU8CellPushFields (index : Nat) : List Scalar :=
  [.native 0x10, .native 1, .native 1, .native 1, .native index]

private def callerFieldGroups (names : CallerBindings) : List (List Scalar) :=
  -- Slot 6 holds either Null or an aligned public address. Normalize it to one cell.
  let layout : List Scalar := [.native 4, .native 1, .native 1, .native 32, .native 32]
  let contract : Expr (.bytes 32) := .ref names.contractAddress
  let user : Expr (.bytes 32) := .ref names.userAddress
  let result := [.native 0x0c] ++ layout ++ [
    .select (.ref names.present) (.native 1) (.native 0),
    .select (.ref names.isContract) (.native 1) (.native 0),
    .bytesField contract 0, .bytesField contract 1, .bytesField user 0, .bytesField user 1]
  [[.native 0x32], listIndexFields 6, [.native 0x30], [.native 0x03],
    listU8CellPushFields 1, [.native 0x02], [.native 0x12, .native 4],
    listU8CellPushFields 1, [.native 0x40], [.native 0x16, .native 66], [.native 0x13, .native 2],
    [.native 0x0b], [.native 0x10, .native 1] ++ layout ++ List.replicate 6 (.native 0),
    result]

private def listRecordNodePushFields (values : List LedgerFieldExpr) : List Scalar :=
  [.native 0x11, .native 51, .native 1] ++ ledgerFieldSequence values ++
    [.native 0, .native 0]

private def emptyListPushFields : List Scalar :=
  [.native 0x11, .native 51, .native 0, .native 0,
    .native 1, .native 1, .native 8, .native 0]

private def eventFieldGroups (kind : EventKind)
    (payload : Expr (.bytes kind.payloadSize)) : List (List Scalar) :=
  -- Push a three-cell array containing version (u32), tag (u8) and data.
  let data := if kind.payloadSize == 0 then
      [.native 1, .letE "_noctium_empty_event" payload (.native 0)]
    else (Aligned.bytes kind.payloadSize payload).fields
  [[.native 0x10, .native 0x33, .native 1, .native 1, .native 4, .native 1,
    .native 1, .native 1, .native 1, .native kind.tag, .native 1] ++ data, [.native 0x09]]

private def tokenChoiceValues (color : Expr (.bytes 32)) (isUnshielded : Expr .bool) :
    List Scalar :=
  [.select isUnshielded (.native 1) (.native 0),
    .select isUnshielded (.bytesField color 0) (.native 0),
    .select isUnshielded (.bytesField color 1) (.native 0),
    .select isUnshielded (.native 0) (.bytesField color 0),
    .select isUnshielded (.native 0) (.bytesField color 1)]

private def balanceAmountFields (value : Expr (.uint balanceMaximum)) : List Scalar :=
  [.native 1, .native 16, .cast .native value]

private def pushBalanceAmount (value : Expr (.uint balanceMaximum)) : List Scalar :=
  [.native 0x10, .native 1] ++ balanceAmountFields value

private def balanceFieldGroupsForToken (destination : String) (token : List Scalar)
    (query : BalanceQuery) : List (List Scalar) :=
  let load depth := [[.native (0x30 + depth)], listIndexFields 5,
    [.native 0x30], [.native 0x10, .native 1] ++ token,
    [.native 0x18], [.native 0x12, .native 3], [.native 0x0b],
    pushBalanceAmount (.uint balanceMaximum 0), [.native 0x13, .native 1], [.native 0x50] ++ token]
  match query with
  | .exact => load 2 ++ [[.native 0x0c] ++ balanceAmountFields (.ref destination)]
  | .compare less limit =>
    let operands := if less then load 2 ++ [pushBalanceAmount limit]
      else pushBalanceAmount limit :: load 3
    operands ++ [[.native 0x01], [.native 0x0c] ++ (Aligned.bitExpr (.ref destination)).fields]

private def taggedBalanceFieldGroups (destination : String) (color : Expr (.bytes 32))
    (isUnshielded : Expr .bool) (query : BalanceQuery) : List (List Scalar) :=
  let token := [.native 3, .native 1, .native 32, .native 32] ++
    tokenChoiceValues color isUnshielded
  balanceFieldGroupsForToken destination token query

private def pushAmount (value : Expr (.uint balanceMaximum)) : List Scalar :=
  [.native 0x10, .native 1] ++ balanceAmountFields value

private def standaloneSpendClaimFieldGroups (color : Expr (.bytes 32))
    (amount : Expr (.uint balanceMaximum)) (isUnshielded isContract : Expr .bool)
    (recipient : Expr (.bytes 32)) : List (List Scalar) :=
  let lo : Scalar := .bytesField recipient 0
  let hi : Scalar := .bytesField recipient 1
  let address := [.select isContract (.native 1) (.native 0),
    .select isContract lo (.native 0), .select isContract hi (.native 0),
    .select isContract (.native 0) lo, .select isContract (.native 0) hi]
  let tokenValues := tokenChoiceValues color isUnshielded
  let claimKey := [.native 6, .native 1, .native 32, .native 32,
    .native 1, .native 32, .native 32] ++ tokenValues ++ address
  accumulateTokenFields 8 claimKey (pushAmount amount)

private def standaloneOutputFieldGroups (color : Expr (.bytes 32))
    (amount : Expr (.uint balanceMaximum)) (isUnshielded : Expr .bool) : List (List Scalar) :=
  accumulateTokenFields 7
    ([.native 3, .native 1, .native 32, .native 32] ++ tokenChoiceValues color isUnshielded)
    (pushAmount amount)

private def standaloneInputFieldGroups (color : Expr (.bytes 32))
    (amount : Expr (.uint balanceMaximum)) (isUnshielded : Expr .bool) : List (List Scalar) :=
  accumulateTokenFields 6
    ([.native 3, .native 1, .native 32, .native 32] ++ tokenChoiceValues color isUnshielded)
    (pushAmount amount)

def Op.fields : Op → List Scalar
  | .dup => [.native 0x30]
  | .index slot pushPath => [.native (if pushPath then 0x70 else 0x50)] ++
      (Aligned.field (.native slot)).fields
  | .mapIndex slot key => [.native 0x51] ++
      (Aligned.field (.native slot)).fields ++ key.fields
  | .indexRecordPath slot _ values keys => [.native (0x51 + keys.length)] ++
      (Aligned.field (.native slot)).fields ++ keys.flatMap Aligned.fields ++
      ledgerFieldSequence values
  | .indexPath slot pushPath keys => indexPathFields slot pushPath keys
  | .push value storage => [.native (if storage then 0x11 else 0x10), .native 1] ++ value.fields
  | .newMap => [.native 0x05]
  | .popeq value => [.native 0x0c] ++ value.fields
  | .pushFields schema values storage =>
      [.native (if storage then 0x11 else 0x10), .native 1] ++
        (if isShieldedCoinRecordSchema schema && values.map (·.ty) == shieldedCoinReadTypes then
          shieldedCoinLedgerFieldSequence values
        else ledgerFieldSequence values)
  | .popeqFields schema values =>
      if isShieldedCoinRecordSchema schema && values.map (·.ty) == shieldedCoinReadTypes then
        [.native 0x0c] ++ shieldedCoinLedgerFieldSequence values
      else [.native 0x0c] ++ ledgerFieldSequence values
  | .member => [.native 0x18]
  | .insert levels => [.native (0x90 + levels)]
  | .addImmediate amount => [.native 0x0e, .cast .native amount]
  | .subImmediate amount => [.native 0x0f, .cast .native amount]
  | .listLength slot keys value =>
      [.native 0x30] ++ indexPathFields slot false keys ++
      listIndexFields 2 ++ [.native 0x0c] ++ (Aligned.counter value).fields
  | .mapSize slot keys value =>
      [.native 0x30] ++ indexPathFields slot false keys ++
      [.native 0x04, .native 0x0c] ++ (Aligned.counter value).fields
  | .mapIsEmpty slot keys destination =>
      (mapIsEmptyFieldGroups slot keys destination).flatten
  | .counterLessThan slot keys threshold destination =>
      (counterLessThanFieldGroups slot keys threshold destination).flatten

  | .merkleTreeIsFull slot depth destination =>
      (merkleTreeIsFullFieldGroups slot depth destination).flatten
  | .merkleTreeCheckRoot slot _ expected destination =>
      (merkleTreeCheckRootFieldGroups slot expected destination).flatten
  | .merkleTreeInsertHash slot _ hash =>
      (merkleTreeInsertHashFieldGroups slot hash).flatten
  | .merkleTreeInsertHashIndex slot _ hash idx =>
      (merkleTreeInsertHashIndexFieldGroups slot hash idx).flatten
  | .merkleTreeReset slot depth =>
      (merkleTreeResetFieldGroups slot depth).flatten
  | .historicMerkleTreeCheckRoot slot _ expected destination =>
      (historicMerkleTreeCheckRootFieldGroups slot expected destination).flatten
  | .historicMerkleTreeInsertHash slot _ hash =>
      (merkleTreeInsertHashFieldGroups slot hash true).flatten
  | .historicMerkleTreeInsertHashIndex slot _ hash idx =>
      (merkleTreeInsertHashIndexFieldGroups slot hash idx true).flatten
  | .historicMerkleTreeReset slot depth =>
      (merkleTreeResetFieldGroups slot depth true).flatten
  | .merkleTreeResetHistory slot _ =>
      (merkleTreeResetHistoryFieldGroups slot).flatten
  | .merkleTreeIsFullAt slot depth keys destination =>
      (merkleTreeIsFullFieldGroups slot depth destination keys).flatten
  | .merkleTreeCheckRootAt slot _ historic keys expected destination =>
      (if historic then historicMerkleTreeCheckRootFieldGroups slot expected destination keys
        else merkleTreeCheckRootFieldGroups slot expected destination keys).flatten
  | .merkleTreeInsertHashAt slot _ historic keys hash =>
      (merkleTreeInsertHashFieldGroups slot hash historic keys).flatten
  | .merkleTreeInsertHashIndexAt slot _ historic keys hash idx =>
      (merkleTreeInsertHashIndexFieldGroups slot hash idx historic keys).flatten
  | .merkleTreeResetAt slot depth historic keys emptyHistory =>
      (merkleTreeResetAtFieldGroups slot depth historic keys emptyHistory).flatten
  | .merkleTreeResetHistoryAt slot _ keys =>
      (merkleTreeResetHistoryFieldGroups slot keys).flatten
  | .listHead slot keys _schema values =>
      [.native 0x30] ++ indexPathFields slot false keys ++ listIndexFields 0 ++
      [.native 0x0c] ++ ledgerFieldSequence values
  | .listPushFront slot keys _ values =>
      indexPathFields slot true keys ++ [.native 0x30] ++ listIndexFields 2 ++
      [.native 0x0e, .native 1] ++ listRecordNodePushFields values ++
      [.native 0x40, .native 0x10, .native 1, .native 1, .native 1, .native 2] ++
      [.native 0x40, .native 0x91, .native 0x40, .native 0x10, .native 1,
        .native 1, .native 1, .native 1, .native 0x40, .native (0x90 + keys.length + 2)]
  | .listPushFrontCoin slot keys _ nonce color amount commitment =>
      (listPushFrontCoinFieldGroups slot keys nonce color amount commitment).flatten
  | .listPushFrontCoinTo slot keys _ nonce color amount _isContract _recipient commitment =>
      (listPushFrontCoinFieldGroups slot keys nonce color amount commitment).flatten
  | .listPopFront slot keys =>
      indexPathFields slot true keys ++ [.native 0x30] ++ listIndexFields 2 ++
      [.native 0x0b] ++ listIndexFields 1 ++
      [.native (0x90 + keys.length + 1)]
  | .listReset slot keys =>
      match keys with
      | [] => [.native 0x10, .native 1] ++ (Aligned.field (.native slot)).fields ++
          emptyListPushFields ++ [.native 0x91]
      | _ => match keys.getLast? with
        | none => []
        | some finalKey =>
          let parents := keys.take (keys.length - 1)
          indexPathFields slot true parents ++ [.native 0x10, .native 1] ++
            finalKey.fields ++ emptyListPushFields ++ [.native (0x90 + keys.length + 1)]
  | .mapRemove slot keys =>
      match keys.getLast? with
      | none => []
      | some finalKey =>
        let parents := keys.take (keys.length - 1)
        indexPathFields slot true parents ++ [.native 0x10, .native 1] ++
          finalKey.fields ++ [.native 0x19, .native (0x90 + keys.length)]
  | .mapRemoveRecord slot _schema keys values =>
      indexPathFields slot true keys ++ [.native 0x10, .native 1] ++
        ledgerFieldSequence values ++ [.native 0x19, .native (0x91 + keys.length)]
  | .claimContractCall address entryPointHash commitment =>
      (claimContractCallFieldGroups address entryPointHash commitment).flatten
  | .claimShielded kind digest => (shieldedClaimFieldGroups kind.slot digest).flatten
  | .insertShieldedCoinSet slot nonce color amount commitment keys =>
      (shieldedCoinSetFieldGroups slot keys nonce color amount commitment).flatten
  | .insertShieldedCoinSetTo slot nonce color amount _isContract _recipient commitment keys =>
      (shieldedCoinSetFieldGroups slot keys nonce color amount commitment).flatten
  | .writeShieldedCoinCell slot nonce color amount commitment =>
      (shieldedCoinCellFieldGroups slot nonce color amount commitment).flatten
  | .writeShieldedCoinCellTo slot nonce color amount _isContract _recipient commitment =>
      (shieldedCoinCellFieldGroups slot nonce color amount commitment).flatten
  | .receiveShieldedToMap slot nonce color amount commitment =>
      (receiveShieldedFieldGroups slot nonce color amount commitment).flatten
  | .insertShieldedCoinMap slot key nonce color amount _ _ commitment keys =>
      (shieldedCoinMapInsertFieldGroups slot keys key nonce color amount commitment).flatten
  | .spendShieldedFromMap _ _ _ _ nullifier output =>
      (shieldedClaimFieldGroups 0 nullifier ++ shieldedClaimFieldGroups 2 output).flatten
  | .mergeShieldedFromMap _ _ _ _ _ _ _ _ _ nullifierA nullifierB output staged =>
      ((staged.map (shieldedClaimFieldGroups 1)).getD [] ++ shieldedClaimFieldGroups 0 nullifierA ++ shieldedClaimFieldGroups 0 nullifierB ++
        shieldedClaimFieldGroups 2 output).flatten
  | .sendShieldedFromMap _ _ _ _ _ nullifier output change =>
      (shieldedClaimFieldGroups 0 nullifier ++ shieldedClaimFieldGroups 2 output ++
        shieldedClaimFieldGroups 2 change).flatten
  | .relayShieldedImmediate _ _ _ _ inputCommitment nullifier outputCommitment =>
      (shieldedClaimFieldGroups 1 inputCommitment ++ shieldedClaimFieldGroups 0 nullifier ++
        shieldedClaimFieldGroups 2 outputCommitment).flatten
  | .mintShielded domain amount => (mintFieldGroups 4 domain amount).flatten
  | .mintUnshielded domain amount => (mintFieldGroups 5 domain amount).flatten
  | .incUnshieldedInputs color amount isUnshielded =>
      (standaloneInputFieldGroups color amount isUnshielded).flatten
  | .incUnshieldedOutputs color amount isUnshielded =>
      (standaloneOutputFieldGroups color amount isUnshielded).flatten
  | .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient =>
      (standaloneSpendClaimFieldGroups color amount isUnshielded isContract recipient).flatten
  | .requireContractCaller address => (requireContractCallerFieldGroups address).flatten
  | .checkpoint => [.native 0xff]
  | .readCaller destinations => (callerFieldGroups destinations).flatten
  | .readContractAddress destination => (contractAddressFieldGroups destination).flatten
  | .readTokenBalance destination color isUnshielded query =>
      (taggedBalanceFieldGroups destination color isUnshielded query).flatten
  | .blockTimeCompare destination before deadline =>
      (blockTimeFieldGroups destination before deadline).flatten
  | .emitEvent kind payload => (eventFieldGroups kind payload).flatten

/-- Native transcript groups correspond one-to-one with VM operations. List
macros remain one typed source effect, but their field vectors split at each
elementary opcode so activity schedules match the ledger VM. -/
def Op.fieldGroups : Op → List (List Scalar)
  | .listLength slot keys value =>
      [[.native 0x30], indexPathFields slot false keys, listIndexFields 2,
        [.native 0x0c] ++ (Aligned.counter value).fields]
  | .mapSize slot keys value =>
      [[.native 0x30], indexPathFields slot false keys, [.native 0x04],
        [.native 0x0c] ++ (Aligned.counter value).fields]
  | .mapIsEmpty slot keys destination =>
      mapIsEmptyFieldGroups slot keys destination
  | .counterLessThan slot keys threshold destination =>
      counterLessThanFieldGroups slot keys threshold destination

  | .merkleTreeIsFull slot depth destination =>
      merkleTreeIsFullFieldGroups slot depth destination
  | .merkleTreeCheckRoot slot _ expected destination =>
      merkleTreeCheckRootFieldGroups slot expected destination
  | .merkleTreeInsertHash slot _ hash =>
      merkleTreeInsertHashFieldGroups slot hash
  | .merkleTreeInsertHashIndex slot _ hash idx =>
      merkleTreeInsertHashIndexFieldGroups slot hash idx
  | .merkleTreeReset slot depth =>
      merkleTreeResetFieldGroups slot depth
  | .historicMerkleTreeCheckRoot slot _ expected destination =>
      historicMerkleTreeCheckRootFieldGroups slot expected destination
  | .historicMerkleTreeInsertHash slot _ hash =>
      merkleTreeInsertHashFieldGroups slot hash true
  | .historicMerkleTreeInsertHashIndex slot _ hash idx =>
      merkleTreeInsertHashIndexFieldGroups slot hash idx true
  | .historicMerkleTreeReset slot depth =>
      merkleTreeResetFieldGroups slot depth true
  | .merkleTreeResetHistory slot _ =>
      merkleTreeResetHistoryFieldGroups slot
  | .merkleTreeIsFullAt slot depth keys destination =>
      merkleTreeIsFullFieldGroups slot depth destination keys
  | .merkleTreeCheckRootAt slot _ historic keys expected destination =>
      if historic then historicMerkleTreeCheckRootFieldGroups slot expected destination keys
      else merkleTreeCheckRootFieldGroups slot expected destination keys
  | .merkleTreeInsertHashAt slot _ historic keys hash =>
      merkleTreeInsertHashFieldGroups slot hash historic keys
  | .merkleTreeInsertHashIndexAt slot _ historic keys hash idx =>
      merkleTreeInsertHashIndexFieldGroups slot hash idx historic keys
  | .merkleTreeResetAt slot depth historic keys emptyHistory =>
      merkleTreeResetAtFieldGroups slot depth historic keys emptyHistory
  | .merkleTreeResetHistoryAt slot _ keys =>
      merkleTreeResetHistoryFieldGroups slot keys
  | .listHead slot keys _schema values =>
      [[.native 0x30], indexPathFields slot false keys, listIndexFields 0,
        [.native 0x0c] ++ ledgerFieldSequence values]
  | .listPushFront slot keys _ values =>
      [indexPathFields slot true keys, [.native 0x30], listIndexFields 2,
        [.native 0x0e, .native 1], listRecordNodePushFields values, [.native 0x40],
        listU8CellPushFields 2, [.native 0x40], [.native 0x91], [.native 0x40],
        listU8CellPushFields 1, [.native 0x40], [.native (0x90 + keys.length + 2)]]
  | .listPushFrontCoin slot keys _ nonce color amount commitment =>
      listPushFrontCoinFieldGroups slot keys nonce color amount commitment
  | .listPushFrontCoinTo slot keys _ nonce color amount _isContract _recipient commitment =>
      listPushFrontCoinFieldGroups slot keys nonce color amount commitment
  | .listPopFront slot keys =>
      [indexPathFields slot true keys, [.native 0x30], listIndexFields 2,
        [.native 0x0b], listIndexFields 1,
        [.native (0x90 + keys.length + 1)]]
  | .listReset slot [] =>
      [[.native 0x10, .native 1] ++ (Aligned.field (.native slot)).fields,
        emptyListPushFields, [.native 0x91]]
  | .listReset slot keys =>
      match keys.getLast? with
      | none => []
      | some finalKey =>
        let parents := keys.take (keys.length - 1)
        [indexPathFields slot true parents,
          [.native 0x10, .native 1] ++ finalKey.fields,
          emptyListPushFields, [.native (0x90 + keys.length + 1)]]
  | .mapRemove slot keys =>
      match keys.getLast? with
      | none => []
      | some finalKey =>
        let parents := keys.take (keys.length - 1)
        [indexPathFields slot true parents,
          [.native 0x10, .native 1] ++ finalKey.fields,
          [.native 0x19], [.native (0x90 + keys.length)]]
  | .mapRemoveRecord slot _schema keys values =>
      [ indexPathFields slot true keys
      , [.native 0x10, .native 1] ++ ledgerFieldSequence values
      , [.native 0x19]
      , [.native (0x91 + keys.length)]
      ]
  | .claimContractCall address entryPointHash commitment =>
      claimContractCallFieldGroups address entryPointHash commitment
  | .claimShielded kind digest => shieldedClaimFieldGroups kind.slot digest
  | .insertShieldedCoinSet slot nonce color amount commitment keys =>
      shieldedCoinSetFieldGroups slot keys nonce color amount commitment
  | .insertShieldedCoinSetTo slot nonce color amount _isContract _recipient commitment keys =>
      shieldedCoinSetFieldGroups slot keys nonce color amount commitment
  | .writeShieldedCoinCell slot nonce color amount commitment =>
      shieldedCoinCellFieldGroups slot nonce color amount commitment
  | .writeShieldedCoinCellTo slot nonce color amount _isContract _recipient commitment =>
      shieldedCoinCellFieldGroups slot nonce color amount commitment
  | .receiveShieldedToMap slot nonce color amount commitment =>
      receiveShieldedFieldGroups slot nonce color amount commitment
  | .insertShieldedCoinMap slot key nonce color amount _ _ commitment keys =>
      shieldedCoinMapInsertFieldGroups slot keys key nonce color amount commitment
  | .spendShieldedFromMap _ _ _ _ nullifier output =>
      shieldedClaimFieldGroups 0 nullifier ++ shieldedClaimFieldGroups 2 output
  | .mergeShieldedFromMap _ _ _ _ _ _ _ _ _ nullifierA nullifierB output staged =>
      (staged.map (shieldedClaimFieldGroups 1)).getD [] ++ shieldedClaimFieldGroups 0 nullifierA ++ shieldedClaimFieldGroups 0 nullifierB ++
        shieldedClaimFieldGroups 2 output
  | .sendShieldedFromMap _ _ _ _ _ nullifier output change =>
      shieldedClaimFieldGroups 0 nullifier ++ shieldedClaimFieldGroups 2 output ++
        shieldedClaimFieldGroups 2 change
  | .relayShieldedImmediate _ _ _ _ inputCommitment nullifier outputCommitment =>
      shieldedClaimFieldGroups 1 inputCommitment ++ shieldedClaimFieldGroups 0 nullifier ++
        shieldedClaimFieldGroups 2 outputCommitment
  | .mintShielded domain amount => mintFieldGroups 4 domain amount
  | .mintUnshielded domain amount => mintFieldGroups 5 domain amount
  | .incUnshieldedInputs color amount isUnshielded =>
      standaloneInputFieldGroups color amount isUnshielded
  | .incUnshieldedOutputs color amount isUnshielded =>
      standaloneOutputFieldGroups color amount isUnshielded
  | .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient =>
      standaloneSpendClaimFieldGroups color amount isUnshielded isContract recipient
  | .requireContractCaller address => requireContractCallerFieldGroups address
  | .readCaller destinations => callerFieldGroups destinations
  | .readContractAddress destination => contractAddressFieldGroups destination
  | .readTokenBalance destination color isUnshielded query =>
      taggedBalanceFieldGroups destination color isUnshielded query
  | .blockTimeCompare destination before deadline => blockTimeFieldGroups destination before deadline
  | .emitEvent kind payload => eventFieldGroups kind payload
  | operation => [operation.fields]

structure Read where
  name : String
  ty : Ty
  components : List (String × Ty) := []
  schema : Option Lean.Json := none
  /-- Source guard for a conditionally bound read. Inactive reads use a canonical default. -/
  guard : Option (Expr .bool) := none
  /-- For byte-aligned UInt128 root-cell reads, retain the source cell, slot,
  and fields from the same storage-read operation appended to the plan. -/
  rootCellRead : Option (String × Nat × List Scalar) := none

private def contractCallerReads (start : Nat) : List Read :=
  -- The ledger also puts each Popeq result's value fields in the public input stream.
  (List.range 5).map fun field => {name := s!"_noctium_contract_caller_{start}_{field}", ty := .native}

private def foreignReadDefault : (kind : Foreign.Kind) → Expr (.foreign kind)
  | .base curve => .foreignBase curve 0
  | .scalar curve => .foreignScalar curve 0
  | .point curve => .foreignIdentity curve

def Read.jubjubPointCoordinateName (name : String) (index : Nat) : String :=
  s!"_noctium_jubjub_read_{name}_{index}"

private def Read.byteChunkName (name : String) (index : Nat) : String :=
  s!"_noctium_bytes_{name}_{index}"

def Read.inactiveDefaultConstraint (read : Read) : Option (Expr .bool) :=
  if !read.components.isEmpty then none else
  match read.ty, read.guard with
  | .bytes _, _ | _, none => none
  | .opaqueBytes, some guard => some (.eq (.opaqueBytesProjection (.ref read.name))
      (.select guard (.opaqueBytesProjection (.ref read.name)) (.native 0)))
  | .opaqueString, some guard => some (.eq (.opaqueStringProjection (.ref read.name))
      (.select guard (.opaqueStringProjection (.ref read.name)) (.native 0)))
  | .jubjubScalar, some guard => some (.eq
      (.jubjubScalarToNative (.ref read.name))
      (.select guard (.jubjubScalarToNative (.ref read.name)) (.native 0)))
  | .jubjubPoint, some _ => none
  | .foreign kind, some guard => some (.eq (.ref read.name)
      (.select guard (.ref read.name) (foreignReadDefault kind)))
  | .native, some guard => some (.eq (.ref read.name) (.select guard (.ref read.name) (.native 0)))
  | .bool, some guard => some (.eq (.ref read.name) (.select guard (.ref read.name) (.bool false)))
  | .uint maximum, some guard => some (.eq (.ref read.name)
      (.select guard (.ref read.name) (.uint maximum 0)))

def Read.scalarReads (read : Read) : List Read :=
  if read.components.isEmpty then [read]
  else read.components.map fun (name, ty) => {name, ty, guard := read.guard}

private def Read.scalarBindings (read : Read) : List (String × Ty) :=
  match read.ty with
  | .bytes length =>
    let count := alignedByteChunkCount length
    (List.range count).map fun index =>
      let lowChunkIndex := count - index - 1
      let width := alignedByteChunkWidth length lowChunkIndex
      (Read.byteChunkName read.name index, .uint (2 ^ (width * 8) - 1))
  | .jubjubPoint =>
    [(Read.jubjubPointCoordinateName read.name 0, .native),
      (Read.jubjubPointCoordinateName read.name 1, .native)]
  | _ => [(read.name, read.ty)]

def Read.bindings (read : Read) : List (String × Ty) :=
  read.scalarReads.flatMap Read.scalarBindings

private def Read.scalarInactiveDefaultConstraints (read : Read) : List (Expr .bool) :=
  if read.ty == .jubjubPoint then
    match read.guard with
    | none => []
    | some guard =>
      let point : Expr .jubjubPoint := .ref read.name
      [.eq (.jubjubCoordinate point 0)
          (.select guard (.jubjubCoordinate point 0) (.native 0)),
        .eq (.jubjubCoordinate point 1)
          (.select guard (.jubjubCoordinate point 1) (.native 1))]
  else read.inactiveDefaultConstraint.toList

def Read.inactiveDefaultConstraints (read : Read) : List (Expr .bool) :=
  read.scalarReads.flatMap Read.scalarInactiveDefaultConstraints

structure Plan where
  operations : List Op := []
  /-- Optional source activity guard per opcode group. Empty means all groups
  are active, preserving historical plans. -/
  activityGuards : List (Option (Expr .bool)) := []
  reads : List Read := []
  guards : List (Expr .bool) := []

def Plan.fields (plan : Plan) : List Scalar := plan.operations.flatMap Op.fields

def Plan.fieldGroups (plan : Plan) : List (List Scalar) :=
  plan.operations.flatMap Op.fieldGroups

def jubjubScalarProjectionName (input : String) : String :=
  s!"_noctium_jubjub_scalar_{input}"

def jubjubPointProjectionName (input : String) (index : Nat) : String :=
  s!"_noctium_jubjub_point_{input}_{index}"

def publicInputReadCount (inputs : List Input) : Nat :=
  inputs.foldl (fun count input =>
    if input.visibility != .«public» then count
    else count + match input.ty with
      | .bytes 0 => 0
      | .bytes _ => 1
      | .jubjubPoint => 2
      | .foreign kind => kind.encodedFieldCount
      | _ => 1) 0

/-- Generated field expressions must retain the source/read types even though
their native representation is uniformly a field. -/
def Plan.validate (plan : Plan) (entry : Entrypoint) : Except String Unit := do
  unless (entry.returns.map Output.nativeReturnFieldCount).sum ≤ maxEntrypointReturnFields do
    throw "entrypoint return field limit exceeded"
  unless entry.returnViews.length ≤ maxEntrypointReturnFields do
    throw "entrypoint logical return view limit exceeded"
  for view in entry.returnViews do
    let compiled ← (Types.compileType view.environment view.type).mapError (·.message)
    unless compiled.checked.expandedLeaves ≤ maxEntrypointReturnFields do
      throw "entrypoint return field limit exceeded"
    unless view.fields.length == view.physicalFieldCount compiled.checked.expandedLeaves do
      throw s!"logical return '{view.name}' field count does not match its type"
    discard (Types.schemaJson compiled)
  let publicCount := publicInputReadCount entry.circuit.inputs
  let env := entry.circuit.inputs.map (fun input => (input.name, input.ty)) ++
    entry.circuit.outputs.map (fun output => (output.name, output.ty)) ++
    (plan.reads.drop publicCount).flatMap fun read =>
      read.scalarReads.flatMap fun scalarRead =>
        (match scalarRead.ty with
          | .bytes _ | .opaqueBytes | .opaqueString | .jubjubPoint => [(scalarRead.name, scalarRead.ty)]
          | _ => []) ++ scalarRead.bindings
  for field in plan.fields do field.validate expressionCapabilities env
  for guard in plan.guards do guard.validate expressionCapabilities env
  unless plan.activityGuards.isEmpty || plan.activityGuards.length == plan.operations.length do
    throw "native activity guard schedule length mismatch"
  for guard in plan.activityGuards do
    if let some guard := guard then guard.validate expressionCapabilities env
  for read in plan.reads do
    if read.components.isEmpty != read.schema.isNone then
      throw "native composite read schema/component metadata mismatch"
    if !read.components.isEmpty then
      unless uniqueNames (read.components.map Prod.fst) do
        throw "duplicate native composite read field binding"
      unless read.components.all (fun component =>
          component.2 == .native || component.2 == .bool ||
            (match component.2 with | .uint _ => true | _ => false) ||
            (match component.2 with | .bytes _ => true | _ => false) ||
            component.2 == .jubjubPoint) ||
          (read.guard.isNone && read.components.map Prod.snd == shieldedCoinReadTypes) do
        throw "native composite reads require supported scalar fields or an unguarded shielded coin record"
      for (_, ty) in read.components do ty.validate expressionCapabilities
    if let some guard := read.guard then guard.validate expressionCapabilities env

private def nativeValue : (ty : Ty) → Expr ty → Except String Scalar
  | .native, value => pure value
  | .bool, value => pure (.select value (.native 1) (.native 0))
  | .uint _, value => pure (.cast .native value)
  | .bytes _, _ => throw "Bytes32 requires byte alignment, not scalar conversion"
  | .opaqueBytes, _ => throw "OpaqueBytes require Compress alignment, not scalar conversion"
  | .opaqueString, _ => throw "OpaqueString requires Compress alignment, not scalar conversion"
  | .jubjubScalar, _ | .jubjubPoint, _ | .foreign _, _ => throw "opaque values require explicit encoding projections"

private def nativeAligned : (ty : Ty) → Expr ty → Except String Aligned
  | .native, value => pure (.field value)
  | .bool, value => pure (.field (.select value (.native 1) (.native 0)))
  | .uint _, value => pure (.field (.cast .native value))
  | .bytes 32, value => pure (.bytes32 value)
  | .bytes length, value => pure (.bytes length value)
  | .opaqueBytes, value => pure (.compress value)
  | .opaqueString, value => pure (.compressString value)
  | .foreign kind, value => pure (.foreignKey kind value)
  | .jubjubScalar, _ | .jubjubPoint, _ => throw "opaque values require explicit encoding projections"

private def nativeRead (ty : Ty) (name : String) : Except String Scalar :=
  match ty with
  | .native => pure (.ref name)
  | .bool => pure (.cast .native (.ref name : Expr .bool))
  | .uint maximum => pure (.cast .native (.ref name : Expr (.uint maximum)))
  | .bytes _ => throw "Bytes32 is read through byte alignment"
  | .opaqueBytes => pure (.opaqueBytesProjection (.ref name))
  | .opaqueString => pure (.opaqueStringProjection (.ref name))
  | .jubjubScalar | .jubjubPoint | .foreign _ => throw "opaque inputs use reserved Native projections"

private def pushKey : Aligned → Op
  | .foreignKey kind value =>
    .pushFields (Lean.Json.str kind.sourceName)
      (nativeFieldExpressions (foreignNativeFields kind value)) false
  | value => .push value false

private def keyValueJson (kind : Foreign.Kind) (value : Expr (.foreign kind))
    (ctx : EvalContext) (env : EvalEnv) : Except String Lean.Json := do
  let fields ← Foreign.encodeValue kind (← value.eval ctx env)
  pure (Lean.Json.arr (fields.toArray.map fun field =>
    Lean.Json.arr ((natBytes field).toArray.map Lean.toJson))
  )

private def storageWriteValueWithAlignment : (ty : Ty) → Expr ty → Option CellAlignment → Except String Op
  | .foreign kind, value, _ =>
    pure (.pushFields (Lean.Json.str kind.sourceName)
      (nativeFieldExpressions (foreignNativeFields kind value)) true)
  | .jubjubScalar, value, _ =>
    pure (.pushFields (Lean.Json.str "JubjubScalar")
      (nativeFieldExpressions [.jubjubScalarToNative value]) true)
  | .jubjubPoint, value, _ =>
    pure (.pushFields (Lean.Json.str "JubjubPoint")
      (nativeFieldExpressions [.jubjubCoordinate value 0, .jubjubCoordinate value 1]) true)
  | .bytes 32, value, _ => pure (.push (.bytes32 value) true)
  | .bytes length, value, _ => pure (.push (.bytes length value) true)
  | .opaqueBytes, value, _ => pure (.push (.compress value) true)
  | .opaqueString, value, _ => pure (.push (.compressString value) true)
  | .uint maximum, value, cellAlignment? =>
    if cellAlignment? == some .u128 then
      if h : maximum = 2 ^ 128 - 1 then
        pure (.push (.u128 (h ▸ value)) true)
      else
        throw "u128 cell alignment requires UInt 128"
    else do
      pure (.push (.field (← nativeValue (.uint maximum) value)) true)
  | ty, value, _ => do pure (.push (.field (← nativeValue ty value)) true)

private def storageWriteValue (ty : Ty) (value : Expr ty) : Except String Op :=
  storageWriteValueWithAlignment ty value none

private def storageReadValueWithAlignment : (ty : Ty) → String → Option CellAlignment → Except String Op
  | .uint maximum, name, cellAlignment? => do
    if cellAlignment? == some .u128 then
      unless maximum == 2 ^ 128 - 1 do
        throw "u128 cell alignment requires UInt 128"
      let value : Expr (.uint (2 ^ 128 - 1)) := .ref name
      pure (.popeq (.u128 value))
    else
      let value : Expr (.uint maximum) := .ref name
      pure (.popeq (.field (.cast .native value)))
  | .bytes 32, name, _ => do
    let value : Expr (.bytes 32) := .ref name
    pure (.popeq (.bytes32 value))
  | .bytes length, name, _ => do
    let value : Expr (.bytes length) := .ref name
    pure (.popeq (.bytes length value))
  | .opaqueBytes, name, _ => do
    let value : Expr .opaqueBytes := .ref name
    pure (.popeq (.compress value))
  | .opaqueString, name, _ => do
    let value : Expr .opaqueString := .ref name
    pure (.popeq (.compressString value))
  | .foreign kind, name, _ => do
    let value : Expr (.foreign kind) := .ref name
    pure (.popeqFields (Lean.Json.str kind.sourceName)
      (nativeFieldExpressions (foreignNativeFields kind value)))
  | .jubjubScalar, name, _ => do
    let value : Expr .jubjubScalar := .ref name
    pure (.popeqFields (Lean.Json.str "JubjubScalar")
      (nativeFieldExpressions [.jubjubScalarToNative value]))
  | .jubjubPoint, name, _ => do
    let value : Expr .jubjubPoint := .ref name
    pure (.popeqFields (Lean.Json.str "JubjubPoint")
      (nativeFieldExpressions [.jubjubCoordinate value 0, .jubjubCoordinate value 1]))
  | ty, name, _ => do pure (.popeq (.field (← nativeRead ty name)))

private def storageReadValue (ty : Ty) (name : String) : Except String Op :=
  storageReadValueWithAlignment ty name none

private def nativePathKeys (keys : List PathKey) : Except String (List Aligned) :=
  keys.mapM fun key => match key with
    | .mk ty value => nativeAligned ty value

private def checkedRecordFields (environment : Types.CompositeEnv) (type : Types.CompositeType) :
    Except String (List (String × Ty)) :=
  LedgerValueType.ledgerRecordFields environment type

private def recordSchemaForFields (environment : Types.CompositeEnv)
    (type : Types.CompositeType) (fields : List (String × Ty)) : Except String Lean.Json := do
  if fields.all (fun (_, ty) => ty == .native) then
    let compiled ← (Types.compileType environment type).mapError (·.message)
    Types.schemaJson compiled
  else
    let .structure id := type | throw "mixed ledger records must be named structures"
    pure <| Lean.Json.mkObj [
      ("id", Lean.toJson id),
      ("fields", Lean.toJson (fields.map fun (name, ty) => Lean.Json.mkObj [
        ("name", Lean.toJson name),
        ("type", Lean.toJson (Noctium.NativeExpression.typeName ty))]))]

def recordSchema (environment : Types.CompositeEnv) (type : Types.CompositeType) :
    Except String Lean.Json := do
  let fields ← checkedRecordFields environment type
  recordSchemaForFields environment type fields

def cellRecordSchema (environment : Types.CompositeEnv) (type : Types.CompositeType) :
    Except String Lean.Json := do
  let fields ← LedgerValueType.cellRecordFields environment type
  recordSchemaForFields environment type fields

/-- Produce the checked key schema used by a root record-key Map. -/
def ledgerRecordSchema (environment : Types.CompositeEnv) (type : Types.CompositeType) :
    Except String Lean.Json := do
  let fields ← LedgerValueType.recordMapKeyFields environment type
  recordSchemaForFields environment type fields

/-- Produce the checked record schema used by a typed record Set key. -/
def recordSetSchema (environment : Types.CompositeEnv) (type : Types.CompositeType) :
    Except String Lean.Json := do
  let fields ← LedgerValueType.recordSetKeyFields environment type
  recordSchemaForFields environment type fields

/-- Produce the record schema shared by List operations and state metadata. -/
def listElementOperationSchema (environment : Types.CompositeEnv)
    (type : Types.CompositeType) : Except String Lean.Json :=
  match type with
  | .scalar ty => pure (Lean.Json.str (Noctium.NativeExpression.typeName ty))
  | _ => do
    let nested : Bool := match type with
      | .structure id =>
        let declaration := environment.structures.find? (fun item : Types.StructDecl => item.id == id)
        declaration.any fun item : Types.StructDecl =>
          item.fields.any fun field : Types.Field => match field.type with
            | .structure _ => true
            | _ => false
      | _ => false
    if nested then do
      let compiled ← (Types.compileType environment type).mapError Types.LayoutDiagnostic.message
      Types.schemaJson compiled
    else do
      match LedgerValueType.recordFields environment type with
      | .ok _ => recordSchema environment type
      | .error _ => match LedgerValueType.shieldedCoinRecordFields environment type with
        | .ok _ => recordSchema environment type
        | .error _ => do
          let fields ← LedgerValueType.listElementFields environment type
          let .structure id := type | throw "List records must be named structures"
          pure <| Lean.Json.mkObj [
            ("id", Lean.toJson id),
            ("fields", Lean.toJson (fields.map fun (name, ty) => Lean.Json.mkObj [
              ("name", Lean.toJson name),
              ("type", Lean.toJson (Noctium.NativeExpression.typeName ty))]))]

private def listHeadParts (environment : Types.CompositeEnv)
    (type : Types.CompositeType) (destination : String)
    (fields destinations : List (String × Ty)) : Except String (Lean.Json × List LedgerFieldExpr × Read) := do
  unless fields.map Prod.snd == destinations.map Prod.snd do
    throw "List head destination type mismatch"
  let schema ← listElementOperationSchema environment type
  match type with
  | .scalar ty => do
    unless fields.map Prod.snd == [ty] && destinations == [(destination, ty)] do
      throw "scalar List head requires one destination matching its read name"
    pure (schema, [refLedgerFieldExpr destination ty], {name := destination, ty})
  | _ => do
    let components := destinations
    let values := destinations.map fun (field, ty) => refLedgerFieldExpr field ty
    let read : Read := {name := destination, ty := Ty.native, components := components, schema := some schema}
    pure (schema, values, read)

private def splitPath (keys : List Aligned) : Except String (List Aligned × Aligned) := do
  if keys.isEmpty then throw "nested map path must contain at least one key"
  let some finalKey := keys.getLast? | throw "nested map path must contain at least one key"
  pure (keys.take (keys.length - 1), finalKey)

private def pathWriteOps (slot : Nat) (keys : List Aligned) (value : List Op)
    : Except String (List Op) := do
  let (parents, finalKey) ← splitPath keys
  let levels := keys.length + 1
  if levels >= 16 then throw "nested map insertion exceeds native Ins depth"
  pure ([.indexPath slot true parents, pushKey finalKey] ++ value ++ [.insert levels])

private def pathWriteCompositeOps (slot : Nat) (keys : List Aligned)
    (schema : Lean.Json) (values : List LedgerFieldExpr) : Except String (List Op) := do
  let (parents, finalKey) ← splitPath keys
  let levels := keys.length + 1
  if levels >= 16 then throw "nested map insertion exceeds native Ins depth"
  pure ([.indexPath slot true parents, pushKey finalKey,
    .pushFields schema values true, .insert levels])

private def stateSlot (state : List StateDecl) (name : String) : Except String Nat :=
  match state.findIdx? (·.name == name) with
  | some index => pure index
  | none => throw s!"unknown ledger state '{name}'"

private def stateCellAlignment (state : List StateDecl) (name : String) : Option CellAlignment :=
  (state.find? (·.name == name)).bind fun declaration =>
    match declaration.kind with
    | .cell _ => declaration.cellAlignment?
    | _ => none

private def resolveTreeState (state : List StateDecl) (name : String)
    (keys : List PathKey) : Except String LedgerValueType := do
  let some declaration := state.find? (·.name == name) | throw s!"unknown tree state '{name}'"
  let .tree schema := declaration.kind | throw s!"state '{name}' is not a recursive tree"
  schema.resolvePath keys

private def recordSetKeySchema (state : List StateDecl) (name : String)
    (keys : List PathKey) (values : List LedgerFieldExpr) :
    Except String (Nat × Lean.Json) := do
  let slot ← stateSlot state name
  let .recordSet environment type ← resolveTreeState state name keys
    | throw s!"path does not select a record Set in '{name}'"
  let fields ← LedgerValueType.recordSetKeyFields environment type
  unless fields.map Prod.snd == values.map LedgerFieldExpr.ty do
    throw "record Set key field type mismatch"
  let schema ← recordSchemaForFields environment type fields
  pure (slot, schema)

private def recordSetInsertOps (slot : Nat) (keys : List Aligned)
    (schema : Lean.Json) (values : List LedgerFieldExpr) : Except String (List Op) := do
  let levels := keys.length + 2
  if levels >= 16 then throw "nested record Set insertion exceeds native Ins depth"
  pure [.indexPath slot true keys, .pushFields schema values false,
    .push (.field (.native 1)), .newMap, .insert levels]

private def recordMapKeySchema (state : List StateDecl) (name : String)
    (values : List LedgerFieldExpr) (parentKeys : List PathKey) :
    Except String (Nat × Lean.Json × Ty) := do
  let slot ← stateSlot state name
  let .recordMapKey environment type valueTy ← resolveTreeState state name parentKeys
    | throw s!"path does not select a scalar-valued record-key Map in '{name}'"
  let fields ← if parentKeys.isEmpty then
      LedgerValueType.recordMapKeyFields environment type
    else LedgerValueType.ledgerRecordWriteFields environment type
  unless fields.map Prod.snd == values.map LedgerFieldExpr.ty do
    throw "record Map key field type mismatch"
  let schema ← recordSchemaForFields environment type fields
  pure (slot, schema, valueTy)

private def anyRecordMapKeySchema (state : List StateDecl) (name : String)
    (values : List LedgerFieldExpr) (parentKeys : List PathKey) :
    Except String (Nat × Lean.Json) := do
  let slot ← stateSlot state name
  let selected ← resolveTreeState state name parentKeys
  let (environment, type) ← match selected with
    | .recordMapKey environment type _ => pure (environment, type)
    | .recordMapComposite environment type _ _ => pure (environment, type)
    | _ => throw s!"state '{name}' is not a record-key Map"
  let fields ← match selected with
    | .recordMapKey .. =>
      if parentKeys.isEmpty then LedgerValueType.recordMapKeyFields environment type
      else LedgerValueType.ledgerRecordWriteFields environment type
    | _ => LedgerValueType.ledgerRecordWriteFields environment type
  unless fields.map Prod.snd == values.map LedgerFieldExpr.ty do
    throw "record Map key field type mismatch"
  let schema ← recordSchemaForFields environment type fields
  pure (slot, schema)

private def recordMapCompositeSchemas (state : List StateDecl) (name : String)
    (parentKeys : List PathKey) (keyValues valueValues : List LedgerFieldExpr) : Except String
      (Nat × Lean.Json × Lean.Json × Types.CompositeType) := do
  let slot ← stateSlot state name
  if parentKeys.length > 13 then
    throw "record Map parent path exceeds the native insertion depth"
  let selected ← if parentKeys.isEmpty then do
    let some declaration := state[slot]?
      | throw s!"unknown composite-valued record-key Map '{name}'"
    let .tree schema := declaration.kind
      | throw s!"state '{name}' is not a composite-valued record-key Map"
    pure schema
  else resolveTreeState state name parentKeys
  let .recordMapComposite keyEnvironment keyType valueEnvironment valueType := selected
    | if parentKeys.isEmpty then
        throw s!"state '{name}' is not a composite-valued record-key Map"
      else throw s!"path does not select a composite-valued record-key Map in '{name}'"
  let keyFields ← LedgerValueType.ledgerRecordWriteFields keyEnvironment keyType
  unless keyFields.map Prod.snd == keyValues.map LedgerFieldExpr.ty do
    throw "record Map key field type mismatch"
  let valueFields ← LedgerValueType.ledgerRecordWriteFields valueEnvironment valueType
  unless valueFields.map Prod.snd == valueValues.map LedgerFieldExpr.ty do
    throw "record Map value field type mismatch"
  let keySchema ← recordSchemaForFields keyEnvironment keyType keyFields
  let valueSchema ← cellRecordSchema valueEnvironment valueType
  pure (slot, keySchema, valueSchema, valueType)

private def compositeWritePathOps (state : List StateDecl) (name : String)
    (keys : List PathKey) (type : Types.CompositeType) (values : List LedgerFieldExpr) :
    Except String (List Op) := do
  let slot ← stateSlot state name
  let (environment, fields) ← if keys.isEmpty then do
    let some declaration := state.find? (·.name == name)
      | throw s!"unknown root composite Cell '{name}'"
    let .tree (.composite environment foundType) := declaration.kind
      | throw "root composite write must target a checked record Cell"
    unless foundType == type do throw "nested composite write type mismatch"
    pure (environment, ← LedgerValueType.cellRecordFields environment type)
  else do
    let .composite environment foundType ← resolveTreeState state name keys
      | throw "nested composite write must select a composite value"
    unless foundType == type do throw "nested composite write type mismatch"
    pure (environment, ← LedgerValueType.ledgerRecordWriteFields environment type)
  unless fields.map Prod.snd == values.map LedgerFieldExpr.ty do
    throw "nested composite write field type mismatch"
  let alignedKeys ← nativePathKeys keys
  let schema ← recordSchemaForFields environment type fields
  if keys.isEmpty then
    pure [.push (.field (.native slot)), .pushFields schema values true, .insert 1]
  else pathWriteCompositeOps slot alignedKeys schema values

private def resolveCounterState (state : List StateDecl) (name : String)
    (keys : List PathKey) : Except String Unit := do
  let some declaration := state.find? (·.name == name) | throw s!"unknown Counter state '{name}'"
  let .tree schema := declaration.kind | throw s!"state '{name}' is not a recursive tree"
  schema.counterPath keys

private def resolveListState (state : List StateDecl) (name : String)
    (keys : List PathKey) :
    Except String (Types.CompositeEnv × Types.CompositeType × List (String × Ty)) := do
  let some declaration := state.find? (·.name == name) | throw s!"unknown List state '{name}'"
  let .tree schema := declaration.kind | throw s!"state '{name}' is not a recursive tree"
  schema.listPath keys

private def validateQualifiedCoinListKeys (keys : List PathKey) : Except String Unit := do
  unless keys.length ≤ 13 do
    throw "qualified shielded coin List supports at most thirteen parent Maps"
  unless keys.all (fun key => key.ty == .bytes 32) do
    throw "qualified shielded coin List parent keys must be Bytes32"

private def pushFrontCoinOp (state : List StateDecl) (name : String)
    (keys : List PathKey)
    (nonce color : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 128 - 1)))
    (selfAddress : Expr (.bytes 32)) : Except String Op := do
  validateQualifiedCoinListKeys keys
  let slot ← stateSlot state name
  if slot > 255 then throw "qualified shielded coin List index exceeds native u8 range"
  let (environment, recordType, fields) ← resolveListState state name keys
  let expectedFields ← LedgerValueType.shieldedCoinRecordFields environment recordType
  unless fields == expectedFields do
    throw "qualified shielded coin List must use the exact shielded coin record"
  let schema ← listElementOperationSchema environment recordType
  let keys ← nativePathKeys keys
  let commitment := shieldedCoinDigest "midnight:zswap-cc[v1]" 0 nonce color amount selfAddress
  pure (.listPushFrontCoin slot keys schema nonce color amount commitment)

private def pushFrontCoinToOp (state : List StateDecl) (name : String)
    (keys : List PathKey)
    (nonce color : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 128 - 1)))
    (isContract : Expr .bool) (recipient : Expr (.bytes 32)) : Except String Op := do
  validateQualifiedCoinListKeys keys
  let slot ← stateSlot state name
  if slot > 255 then throw "qualified shielded coin List index exceeds native u8 range"
  let (environment, recordType, fields) ← resolveListState state name keys
  let expectedFields ← LedgerValueType.shieldedCoinRecordFields environment recordType
  unless fields == expectedFields do
    throw "qualified shielded coin List must use the exact shielded coin record"
  let schema ← listElementOperationSchema environment recordType
  let keys ← nativePathKeys keys
  let commitment := shieldedCoinDigestForRecipient
    "midnight:zswap-cc[v1]" nonce color amount isContract recipient
  pure (.listPushFrontCoinTo slot keys schema nonce color amount isContract recipient commitment)

private def insertShieldedCoinMapOp (state : List StateDecl) (name : String)
    (keys : List PathKey) (key nonce color : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 128 - 1)))
    (isContract : Expr .bool) (recipient : Expr (.bytes 32)) : Except String Op := do
  let slot ← stateSlot state name
  if slot > 255 then throw "shielded coin map index exceeds native u8 range"
  if keys.length > 14 then
    throw "qualified coin Map parent path exceeds fourteen Maps"
  let selected ← resolveTreeState state name keys
  unless keys.all (fun parent => parent.ty == .bytes 32) do
    throw "qualified coin Map parent keys must be Bytes32"
  let .map (.bytes 32) (.composite environment recordType) := selected
    | throw "path does not select a Bytes32-keyed qualified coin Map"
  discard (LedgerValueType.shieldedCoinRecordFields environment recordType)
  let commitment := shieldedCoinDigestForRecipient
    "midnight:zswap-cc[v1]" nonce color amount isContract recipient
  pure (.insertShieldedCoinMap slot key nonce color amount isContract recipient commitment
    (← nativePathKeys keys))

private def validateQualifiedCoinSetKeys (keys : List PathKey) : Except String Unit := do
  unless keys.length ≤ 14 do
    throw "insertShieldedCoinSet supports at most fourteen Bytes32 Map parents"
  unless keys.all (fun key => key.ty == .bytes 32) do
    throw "qualified coin Set parent keys must be Bytes32"

private def shieldedCoinSetPath (state : List StateDecl) (name : String)
    (keys : List PathKey) : Except String (Nat × List Aligned) := do
  validateQualifiedCoinSetKeys keys
  let slot ← stateSlot state name
  let selected ← resolveTreeState state name keys
  let (environment, recordType) ← match selected with
    | .shieldedCoinSet environment recordType => pure (environment, recordType)
    | .recordSet environment recordType =>
      if keys.isEmpty then throw "qualified coin Set root must be a shielded coin Set"
      pure (environment, recordType)
    | _ => throw "path does not select a qualified coin Set"
  discard (LedgerValueType.shieldedCoinRecordFields environment recordType)
  pure (slot, ← nativePathKeys keys)

private def insertShieldedCoinSetOp (state : List StateDecl) (name : String)
    (keys : List PathKey) (nonce color : Expr (.bytes 32))
    (amount : Expr (.uint (2 ^ 128 - 1))) (selfAddress : Expr (.bytes 32)) : Except String Op := do
  let (slot, keys) ← shieldedCoinSetPath state name keys
  if slot > 255 then throw "qualified shielded coin Set index exceeds native u8 range"
  let commitment := shieldedCoinDigest "midnight:zswap-cc[v1]" 0 nonce color amount selfAddress
  pure (.insertShieldedCoinSet slot nonce color amount commitment keys)

private def insertShieldedCoinSetToOp (state : List StateDecl) (name : String)
    (keys : List PathKey) (nonce color : Expr (.bytes 32))
    (amount : Expr (.uint (2 ^ 128 - 1))) (isContract : Expr .bool)
    (recipient : Expr (.bytes 32)) : Except String Op := do
  let (slot, keys) ← shieldedCoinSetPath state name keys
  if slot > 255 then throw "qualified shielded coin Set index exceeds native u8 range"
  let commitment := shieldedCoinDigestForRecipient
    "midnight:zswap-cc[v1]" nonce color amount isContract recipient
  pure (.insertShieldedCoinSetTo slot nonce color amount isContract recipient commitment keys)

private def mapSizeOp (state : List StateDecl) (name destination : String)
    (keys : List PathKey) : Except String Op := do
  let slot ← stateSlot state name
  let some declaration := state[slot]? | throw s!"unknown map state '{name}'"
  declaration.kind.validateCollectionPath keys
  pure (.mapSize slot (← nativePathKeys keys) (.ref destination))

private def mapIsEmptyOp (state : List StateDecl) (name destination : String)
    (keys : List PathKey) : Except String Op := do
  let slot ← stateSlot state name
  let some declaration := state[slot]? | throw s!"unknown map state '{name}'"
  declaration.kind.validateCollectionPath keys
  pure (.mapIsEmpty slot (← nativePathKeys keys) destination)

private def counterLessThanOp (state : List StateDecl) (name destination : String)
    (keys : List PathKey) (threshold : Expr (.uint (2 ^ 64 - 1))) : Except String Op := do
  let slot ← stateSlot state name
  resolveCounterState state name keys
  pure (.counterLessThan slot (← nativePathKeys keys) threshold destination)

private def setInsertOps (state : List StateDecl) (name : String)
    (keys : List PathKey) : Except String (List Op) := do
  let slot ← stateSlot state name
  let some {kind := .tree schema, ..} := state[slot]?
    | throw s!"unknown set state '{name}'"
  let .set _ ← schema.entryParent keys
    | throw "set insertion path must select a Set"
  pathWriteOps slot (← nativePathKeys keys) [.push (.field (.native 1)), .newMap]

private def emptyMapOps (state : List StateDecl) (name : String)
    (keys : List PathKey) : Except String (List Op) := do
  let slot ← stateSlot state name
  let some declaration := state[slot]? | throw s!"unknown map state '{name}'"
  declaration.kind.validateCollectionPath keys
  if keys.isEmpty then
    pure ([.push (.field (.native slot)), .push (.field (.native 2)), .newMap, .insert 1])
  else
    pathWriteOps slot (← nativePathKeys keys) [.push (.field (.native 2)), .newMap]

private def merkleTreeSlotAndDepth (state : List StateDecl) (name : String) :
    Except String (Nat × Nat × Bool) := do
  let slot ← stateSlot state name
  let some declaration := state[slot]? | throw s!"unknown MerkleTree state '{name}'"
  let some depth := declaration.kind.merkleTreeDepth?
    | throw s!"unknown MerkleTree state '{name}'"
  unless 2 ≤ depth && depth ≤ 32 do
    throw "MerkleTree depth must be between 2 and 32"
  pure (slot, depth, declaration.kind.isHistoricMerkleTree)

private def merkleTreeIsFullOp (state : List StateDecl) (name destination : String) :
    Except String Op := do
  let (slot, depth, _) ← merkleTreeSlotAndDepth state name
  pure (.merkleTreeIsFull slot depth destination)

private def merkleTreeCheckRootOp (state : List StateDecl) (name : String)
    (expected : Expr .native) (destination : String) : Except String Op := do
  let (slot, depth, historic) ← merkleTreeSlotAndDepth state name
  pure (if historic then .historicMerkleTreeCheckRoot slot depth expected destination
    else .merkleTreeCheckRoot slot depth expected destination)

private def merkleTreeInsertHashOp (state : List StateDecl) (name : String)
    (hash : Expr (.bytes 32)) : Except String Op := do
  let (slot, depth, historic) ← merkleTreeSlotAndDepth state name
  pure (if historic then .historicMerkleTreeInsertHash slot depth hash
    else .merkleTreeInsertHash slot depth hash)

private def merkleTreeInsertHashIndexOp (state : List StateDecl) (name : String)
    (hash : Expr (.bytes 32)) (index : Expr (.uint (2 ^ 64 - 1))) : Except String Op := do
  let (slot, depth, historic) ← merkleTreeSlotAndDepth state name
  pure (if historic then .historicMerkleTreeInsertHashIndex slot depth hash index
    else .merkleTreeInsertHashIndex slot depth hash index)

private def merkleTreeResetOp (state : List StateDecl) (name : String) :
    Except String Op := do
  let (slot, depth, historic) ← merkleTreeSlotAndDepth state name
  pure (if historic then .historicMerkleTreeReset slot depth else .merkleTreeReset slot depth)

private def merkleTreeResetHistoryOp (state : List StateDecl) (name : String) :
    Except String Op := do
  let (slot, depth, historic) ← merkleTreeSlotAndDepth state name
  unless historic do throw "resetHistory requires a HistoricMerkleTree"
  pure (.merkleTreeResetHistory slot depth)

private def merkleTreePathOpConfig (state : List StateDecl) (name : String)
    (keys : List PathKey) : Except String (Nat × Nat × Bool × List Aligned) := do
  let slot ← stateSlot state name
  let some declaration := state[slot]?
    | throw s!"unknown MerkleTree state '{name}'"
  let .tree schema := declaration.kind
    | throw s!"state '{name}' is not a recursive tree"
  let (depth, historic) ← schema.merkleTreePathConfig keys
  pure (slot, depth, historic, ← nativePathKeys keys)

private def merkleTreeIsFullAtOp (state : List StateDecl) (name destination : String)
    (keys : List PathKey) : Except String Op := do
  let (slot, depth, _, keys) ← merkleTreePathOpConfig state name keys
  pure (.merkleTreeIsFullAt slot depth keys destination)

private def merkleTreeCheckRootAtOp (state : List StateDecl) (name : String)
    (keys : List PathKey) (expected : Expr .native) (destination : String) :
    Except String Op := do
  let (slot, depth, historic, keys) ← merkleTreePathOpConfig state name keys
  pure (.merkleTreeCheckRootAt slot depth historic keys expected destination)

private def merkleTreeInsertHashAtOp (state : List StateDecl) (name : String)
    (keys : List PathKey) (hash : Expr (.bytes 32)) : Except String Op := do
  let (slot, depth, historic, keys) ← merkleTreePathOpConfig state name keys
  pure (.merkleTreeInsertHashAt slot depth historic keys hash)

private def merkleTreeInsertHashIndexAtOp (state : List StateDecl) (name : String)
    (keys : List PathKey) (hash : Expr (.bytes 32))
    (index : Expr (.uint (2 ^ 64 - 1))) : Except String Op := do
  let (slot, depth, historic, keys) ← merkleTreePathOpConfig state name keys
  pure (.merkleTreeInsertHashIndexAt slot depth historic keys hash index)

private def merkleTreeResetAtOp (state : List StateDecl) (name : String)
    (keys : List PathKey) (depth : Nat) (historic emptyHistory : Bool) : Except String Op := do
  if emptyHistory && keys.isEmpty then
    throw "empty-history reset requires a nested HistoricMerkleTree"
  let (slot, foundDepth, foundHistoric, keys) ← merkleTreePathOpConfig state name keys
  unless depth == foundDepth && historic == foundHistoric do
    throw "nested MerkleTree reset schema mismatch"
  if emptyHistory && !historic then
    throw "empty-history reset requires a HistoricMerkleTree"
  pure (.merkleTreeResetAt slot depth historic keys emptyHistory)

private def merkleTreeResetHistoryAtOp (state : List StateDecl) (name : String)
    (keys : List PathKey) : Except String Op := do
  let (slot, depth, historic, keys) ← merkleTreePathOpConfig state name keys
  unless historic do throw "resetHistory requires a HistoricMerkleTree"
  pure (.merkleTreeResetHistoryAt slot depth keys)

mutual
private def expressionNames : Expr ty → List String
  | .native _ | .bool _ | .uint _ _ | .opaqueBytesEmpty | .opaqueStringEmpty
  | .foreignBase _ _ | .foreignScalar _ _ | .foreignPoint _ _ => []
  | .opaqueBytesProjection value => expressionNames value
  | .opaqueStringProjection value => expressionNames value
  | .foreignEncodedField value _ | .foreignUnary _ value | .foreignToBytes value
  | .foreignFromBytes _ value => expressionNames value
  | .foreignBinary _ left right => expressionNames left ++ expressionNames right
  | .bytesField value _ | .bytesAt value _ => expressionNames value
  | .sha256 value | .sha512 value | .keccak256 value
  | .keccak256Secp256k1Point value | .persistentHash32 value => expressionNames value
  | .bytes32Literal _ | .bytesLiteral _ _ => []
  | .persistentHashVector32 values => values.flatMap expressionNames
  | .persistentHashNative value => expressionNames value
  | .persistentHashFab _ _ values => expressionNamesFabValues values
  | .transientHashFab _ _ values => expressionNamesFabValues values
  | .hashToCurveFab _ _ values => expressionNamesFabValues values
  | .sha512Fab _ _ values | .keccak256Fab _ _ values => expressionNamesFabValues values
  | .persistentCommitFab _ _ opening values | .transientCommitFab _ _ opening values =>
    expressionNames opening ++ expressionNamesFabValues values
  | .hashToCurve values | .persistentHashNativeVector values | .transientHash values => values.flatMap expressionNames
  | .toBytes32 value | .fromBytes32 value | .fromBytes value => expressionNames value
  | .reverseBytes32 value | .reverseBytes value | .sliceBytes value _ _ => expressionNames value
  | .concatBytes left right => expressionNames left ++ expressionNames right
  | .jubjubScalarFromNative value | .jubjubScalarToNative value
  | .jubjubMulGenerator value | .jubjubNeg value
  | .jubjubCoordinate value _ => expressionNames value
  | .jubjubMul point scalar | .jubjubAdd point scalar =>
    expressionNames point ++ expressionNames scalar
  | .jubjubFromCoordinates x y => expressionNames x ++ expressionNames y
  | .ref name => [name]
  | .boolAnd left right | .boolOr left right | .boolXor left right
  | .add left right => expressionNames left ++ expressionNames right
  | .mul left right => expressionNames left ++ expressionNames right
  | .sub left right => expressionNames left ++ expressionNames right
  | .uadd left right => expressionNames left ++ expressionNames right
  | .usub left right => expressionNames left ++ expressionNames right
  | .umul left right => expressionNames left ++ expressionNames right
  | .inv value => expressionNames value
  | .copyValue value | .cast _ value => expressionNames value
  | .letE name value body => name :: (expressionNames value ++ expressionNames body)
  | .assertE condition body => expressionNames condition ++ expressionNames body
  | .disclose _ value => expressionNames value
  | .eq left right => expressionNames left ++ expressionNames right
  | .select condition yes no =>
    expressionNames condition ++ expressionNames yes ++ expressionNames no
  | .poseidon2 _ left right => expressionNames left ++ expressionNames right
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first
    | have _h := sizeOfSigmaExprMemberLt (by assumption); omega
    | have _h := sizeOfSigmaExprHeadLt _ _; omega
    | have h := sizeOfMemberListLt (by assumption); omega
    | omega

private def expressionNamesFabValues : List (Sigma Expr) → List String
  | [] => []
  | ⟨_, value⟩ :: rest => expressionNames value ++ expressionNamesFabValues rest
termination_by values => sizeOf values
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact sizeOfSigmaExprHeadLt _ _
    | omega
end

private def pathExpressionNames (keys : List PathKey) : List String :=
  keys.flatMap fun key => match key with
    | .mk _ value => expressionNames value

private def freshActivityName (names : List String) : String :=
  let longest := names.foldl (fun length name => max length name.length) 0
  "_noctium_activity_guard_" ++ String.ofList (List.replicate (longest + 1) 'x')

private def totalizeActivityValue (guard : Expr .bool) (avoid : List String)
    (value : Expr ty) : Expr ty :=
  let name := freshActivityName (avoid ++ expressionNames guard ++ expressionNames value)
  .letE name guard (Noctium.GuardedExpression.totalize (.ref name) value)

private def ledgerFieldExprNames (values : List LedgerFieldExpr) : List String :=
  values.flatMap fun
    | .mk _ value => expressionNames value

private def totalizeLedgerFieldExpr (guard : Expr .bool) (avoid : List String)
    (value : LedgerFieldExpr) : LedgerFieldExpr :=
  match value with
  | .mk ty expression => .mk ty (totalizeActivityValue guard avoid expression)

private def totalizeActivityKey (guard : Expr .bool) (avoid : List String) :
    (ty : Ty) → Expr ty → Expr ty
  | .foreign kind, value =>
    let name := freshActivityName (avoid ++ expressionNames guard ++ expressionNames value)
    .letE name guard (.select (.ref name)
      (Noctium.GuardedExpression.totalize (.ref name) value)
      (Noctium.GuardedExpression.zeroValue (.foreign kind)))
  | _, value => totalizeActivityValue guard avoid value

private def totalizePathKeys (condition : Expr .bool) (keys : List PathKey) : List PathKey :=
  let avoid := pathExpressionNames keys
  keys.map fun key => match key with
    | .mk .native value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      let guardedValue := Noctium.GuardedExpression.totalize (.ref guardName) value
      .mk .native (.letE guardName condition
        (.select (.ref guardName) guardedValue (.native 0)))
    | .mk .bool value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      let guardedValue := Noctium.GuardedExpression.totalize (.ref guardName) value
      .mk .bool (.letE guardName condition
        (.select (.ref guardName) guardedValue (.bool false)))
    | .mk (.uint maximum) value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      let guardedValue := Noctium.GuardedExpression.totalize (.ref guardName) value
      .mk (.uint maximum) (.letE guardName condition
        (.select (.ref guardName) guardedValue (.uint maximum 0)))
    | .mk (.bytes 32) value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      let guardedValue := Noctium.GuardedExpression.totalize (.ref guardName) value
      .mk (.bytes 32) (.letE guardName condition (.select (.ref guardName) guardedValue
        (.bytes32Literal (List.replicate 32 0))))
    | .mk (.bytes length) value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      let guardedValue := Noctium.GuardedExpression.totalize (.ref guardName) value
      .mk (.bytes length) (.letE guardName condition (.select (.ref guardName) guardedValue
        (.bytesLiteral length (List.replicate length 0))))
    | .mk (.foreign kind) value =>
      .mk (.foreign kind) (totalizeActivityKey condition avoid (.foreign kind) value)
    | .mk ty value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      .mk ty (.letE guardName condition (Noctium.GuardedExpression.totalize (.ref guardName) value))

private def totalizeActivityCondition (guard condition : Expr .bool) : Expr .bool :=
  let name := freshActivityName (expressionNames guard ++ expressionNames condition)
  .letE name guard
    (.select (.ref name) (Noctium.GuardedExpression.totalize (.ref name) condition) (.bool true))

/-- Evaluate a nested branch condition only when its enclosing branch is active.
The inactive arm becomes false, and partial condition expressions are totalized
under the captured parent guard before eager `select` lowering. -/
def activityGuardWithin (parent condition : Expr .bool) : Expr .bool :=
  let name := freshActivityName (expressionNames parent ++ expressionNames condition)
  .letE name parent
    (.select (.ref name) (Noctium.GuardedExpression.totalize (.ref name) condition) (.bool false))

/-- One effect in the production ordered ledger plan. The current read count
fixes generated absence names and therefore belongs to the accumulator. -/
def appendEffect (state : List StateDecl) (effect : Effect)
    (plan : Plan) : Except String Plan := do
  match effect with
  | .readCell name destination ty =>
    let slot ← stateSlot state name
    let alignment := stateCellAlignment state name
    let value ← storageReadValueWithAlignment ty destination alignment
    let provenance := if alignment == some .u128 then some (name, slot, value.fields) else none
    let read : Read := {name := destination, ty, rootCellRead := provenance}
    pure { plan with
      operations := plan.operations ++ [.dup, .index slot, value]
      reads := plan.reads ++ [read] }
  | .merkleTreeIsFull name destination => do
    let operation ← merkleTreeIsFullOp state name destination
    pure {plan with
      operations := plan.operations ++ [operation]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .merkleTreeCheckRoot name expected destination => do
    let operation ← merkleTreeCheckRootOp state name expected destination
    pure {plan with
      operations := plan.operations ++ [operation]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .merkleTreeInsertHash name hash => do
    let operation ← merkleTreeInsertHashOp state name hash
    pure {plan with operations := plan.operations ++ [operation]}
  | .merkleTreeInsertHashIndex name hash index => do
    let operation ← merkleTreeInsertHashIndexOp state name hash index
    pure {plan with operations := plan.operations ++ [operation]}
  | .merkleTreeReset name => do
    let operation ← merkleTreeResetOp state name
    pure {plan with operations := plan.operations ++ [operation]}
  | .merkleTreeResetHistory name => do
    let operation ← merkleTreeResetHistoryOp state name
    pure {plan with operations := plan.operations ++ [operation]}
  | .merkleTreeIsFullAt name keys destination =>
    pure {plan with
      operations := plan.operations ++ [← merkleTreeIsFullAtOp state name destination keys]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .merkleTreeCheckRootAt name keys expected destination =>
    pure {plan with
      operations := plan.operations ++ [← merkleTreeCheckRootAtOp state name keys expected destination]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .merkleTreeInsertHashAt name keys hash =>
    pure {plan with operations := plan.operations ++ [← merkleTreeInsertHashAtOp state name keys hash]}
  | .merkleTreeInsertHashIndexAt name keys hash index =>
    pure {plan with operations := plan.operations ++ [
      ← merkleTreeInsertHashIndexAtOp state name keys hash index]}
  | .merkleTreeResetAt name keys depth historic emptyHistory =>
    pure {plan with operations := plan.operations ++ [
      ← merkleTreeResetAtOp state name keys depth historic emptyHistory]}
  | .merkleTreeResetHistoryAt name keys =>
    pure {plan with operations := plan.operations ++ [
      ← merkleTreeResetHistoryAtOp state name keys]}
  | .require condition =>
    pure {plan with guards := plan.guards ++ [condition]}
  | .claimContractCall address entryPointHash commitment =>
    pure {plan with operations := plan.operations ++ [
      .claimContractCall address entryPointHash commitment]}
  | .claimShielded kind digest =>
    pure {plan with operations := plan.operations ++ [.claimShielded kind digest]}
  | .receiveShieldedToMap stateName nonce color amount selfAddress => do
    let slot ← stateSlot state stateName
    if slot > 255 then throw "shielded coin map index exceeds native u8 range"
    let commitment := shieldedCoinDigest "midnight:zswap-cc[v1]" 0 nonce color amount selfAddress
    pure {plan with operations := plan.operations ++ [
      .receiveShieldedToMap slot nonce color amount commitment]}
  | .insertShieldedCoinMap stateName key nonce color amount isContract recipient keys => do
    let operation ← insertShieldedCoinMapOp state stateName keys key nonce color amount isContract recipient
    pure {plan with operations := plan.operations ++ [operation]}
  | .insertShieldedCoinSet stateName nonce color amount selfAddress keys => do
    let operation ← insertShieldedCoinSetOp state stateName keys nonce color amount selfAddress
    pure {plan with operations := plan.operations ++ [operation]}
  | .insertShieldedCoinSetTo stateName nonce color amount isContract recipient keys => do
    let operation ← insertShieldedCoinSetToOp state stateName keys nonce color amount
      isContract recipient
    pure {plan with operations := plan.operations ++ [operation]}
  | .writeShieldedCoinCell stateName nonce color amount selfAddress => do
    let slot ← stateSlot state stateName
    if slot > 255 then throw "shielded coin Cell index exceeds native u8 range"
    let commitment := shieldedCoinDigest "midnight:zswap-cc[v1]" 0 nonce color amount selfAddress
    pure {plan with operations := plan.operations ++ [
      .writeShieldedCoinCell slot nonce color amount commitment]}
  | .writeShieldedCoinCellTo stateName nonce color amount isContract recipient => do
    let slot ← stateSlot state stateName
    if slot > 255 then throw "shielded coin Cell index exceeds native u8 range"
    let commitment := shieldedCoinDigestForRecipient
      "midnight:zswap-cc[v1]" nonce color amount isContract recipient
    pure {plan with operations := plan.operations ++ [
      .writeShieldedCoinCellTo slot nonce color amount isContract recipient commitment]}
  | .pushFrontCoin stateName nonce color amount selfAddress keys => do
    let operation ← pushFrontCoinOp state stateName keys nonce color amount selfAddress
    pure {plan with operations := plan.operations ++ [operation]}
  | .pushFrontCoinTo stateName nonce color amount isContract recipient keys => do
    let operation ← pushFrontCoinToOp state stateName keys nonce color amount isContract recipient
    pure {plan with operations := plan.operations ++ [operation]}
  | .spendShieldedFromMap _ nonce color amount recipient selfAddress =>
    pure {plan with operations := plan.operations ++ [
      spendShieldedOp nonce color amount recipient selfAddress]}
  | .mergeShieldedFromMap _ nonceA colorA amountA nonceB colorB amountB selfAddress staged =>
    pure {plan with operations := plan.operations ++ [
      mergeShieldedOp nonceA colorA amountA nonceB colorB amountB selfAddress staged]}
  | .sendShieldedFromMap _ nonce color inputAmount sendAmount recipient selfAddress =>
    pure {plan with operations := plan.operations ++ [
      sendShieldedOp nonce color inputAmount sendAmount recipient selfAddress]}
  | .relayShieldedImmediate nonce color amount recipient selfAddress =>
    pure {plan with operations := plan.operations ++ [
      relayShieldedOp nonce color amount recipient selfAddress]}
  | .checkpoint => pure {plan with operations := plan.operations ++ [.checkpoint]}
  | .mintShielded domain amount =>
    pure {plan with operations := plan.operations ++ [.mintShielded domain amount]}
  | .mintUnshielded domain amount =>
    pure {plan with operations := plan.operations ++ [.mintUnshielded domain amount]}
  | .incUnshieldedInputs color amount isUnshielded =>
    pure {plan with operations := plan.operations ++ [
      .incUnshieldedInputs color amount isUnshielded]}
  | .incUnshieldedOutputs color amount isUnshielded =>
    pure {plan with operations := plan.operations ++ [
      .incUnshieldedOutputs color amount isUnshielded]}
  | .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient =>
    pure {plan with operations := plan.operations ++ [
      .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient]}
  | .emitEvent kind payload =>
    pure {plan with operations := plan.operations ++ [.emitEvent kind payload]}
  | .requireContractCaller address =>
    pure {plan with
      operations := plan.operations ++ [.requireContractCaller address]
      reads := plan.reads ++ contractCallerReads plan.reads.length}
  | .readCaller destinations =>
    pure {plan with
      operations := plan.operations ++ [.readCaller destinations]
      reads := plan.reads ++ destinations.types.map (fun (name, ty) => {name, ty})}
  | .readContractAddress destination =>
    pure {plan with
      operations := plan.operations ++ [.readContractAddress destination]
      reads := plan.reads ++ [{name := destination, ty := .bytes 32}]}
  | .readTokenBalance destination color isUnshielded query =>
    pure {plan with
      operations := plan.operations ++ [.readTokenBalance destination color isUnshielded query]
      reads := plan.reads ++ [{name := destination, ty := query.resultType}]}
  | .blockTimeCompare destination before deadline =>
    pure {plan with
      operations := plan.operations ++ [.blockTimeCompare destination before deadline]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .requireAbsent name _ key =>
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let readName := s!"_noctium_absence_{plan.reads.length}"
    pure { plan with
      operations := plan.operations ++ [
        .dup, .index slot, pushKey key, .member, .popeq (.bit false)]
      reads := plan.reads ++ [{name := readName, ty := .bool}]
      guards := plan.guards ++ [.eq (.ref readName : Expr .bool) (.bool false)] }
  | .writeCell name ty value =>
    let slot ← stateSlot state name
    let value ← storageWriteValueWithAlignment ty value (stateCellAlignment state name)
    pure {plan with operations := plan.operations ++ [
      .push (.field (.native slot)), value, .insert 1]}
  | .writeMap name _ ty key value =>
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let value ← storageWriteValue ty value
    pure {plan with operations := plan.operations ++ [
      .index slot true, pushKey key,
      value, .insert 2]}
  | .writeRecordMap name values ty value parentKeys => do
    let (slot, schema, foundTy) ← recordMapKeySchema state name values parentKeys
    unless foundTy == ty do throw "record Map value type mismatch"
    let keys ← nativePathKeys parentKeys
    let value ← storageWriteValue ty value
    let levels := keys.length + 2
    if levels >= 16 then throw "nested record Map insertion exceeds native Ins depth"
    pure {plan with operations := plan.operations ++ [
      .indexPath slot true keys, .pushFields schema values false, value, .insert levels]}
  | .writeRecordMapComposite name valueType keyValues valueValues parentKeys => do
    let (slot, keySchema, valueSchema, foundType) ←
      recordMapCompositeSchemas state name parentKeys keyValues valueValues
    unless foundType == valueType do throw "record Map value type mismatch"
    let keys ← nativePathKeys parentKeys
    let levels := keys.length + 2
    if levels >= 16 then throw "nested record Map insertion exceeds native Ins depth"
    pure {plan with operations := plan.operations ++ [
      .indexPath slot true keys, .pushFields keySchema keyValues false,
      .pushFields valueSchema valueValues true, .insert levels]}
  | .removeRecordMap name values parentKeys => do
    let (slot, schema) ← anyRecordMapKeySchema state name values parentKeys
    pure {plan with operations := plan.operations ++ [
      .mapRemoveRecord slot schema (← nativePathKeys parentKeys) values]}
  | .readMap name destination _ ty key => do
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let value ← storageReadValue ty destination
    pure { plan with
      operations := plan.operations ++ [
        .dup, .mapIndex slot key,
        value]
      reads := plan.reads ++ [{name := destination, ty}] }
  | .readRecordMap name destination ty values parentKeys => do
    let (slot, schema, foundTy) ← recordMapKeySchema state name values parentKeys
    unless foundTy == ty do throw "record Map value type mismatch"
    let value ← storageReadValue ty destination
    pure {plan with
      operations := plan.operations ++ [
        .dup, .indexRecordPath slot schema values (← nativePathKeys parentKeys), value]
      reads := plan.reads ++ [{name := destination, ty}]}
  | .readRecordMapComposite name destination valueType values destinations parentKeys => do
    let fields := destinations.map fun (fieldName, ty) => .mk ty (.ref fieldName)
    let (slot, keySchema, valueSchema, foundType) ←
      recordMapCompositeSchemas state name parentKeys values fields
    unless foundType == valueType do throw "record Map value type mismatch"
    let read : Read := {name := destination, ty := .native, components := destinations, schema := some valueSchema}
    pure {plan with
      operations := plan.operations ++ [
        .dup, .indexRecordPath slot keySchema values (← nativePathKeys parentKeys),
        .popeqFields valueSchema fields],
      reads := plan.reads ++ [read]}
  | .readMember name destination _ _ key => do
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    pure { plan with
      operations := plan.operations ++ [
        .dup, .index slot, pushKey key, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}] }
  | .readPath name destination keys ty => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let value ← storageReadValue ty destination
    pure {plan with
      operations := plan.operations ++ [.dup, .indexPath slot false keys, value]
      reads := plan.reads ++ [{name := destination, ty}]}
  | .counterRead name destination keys => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    let keys ← nativePathKeys keys
    let value : Expr (.uint (2 ^ 64 - 1)) := .ref destination
    pure {plan with
      operations := plan.operations ++ [.dup, .indexPath slot false keys, .popeq (.counter value)]
      reads := plan.reads ++ [{name := destination, ty := .uint (2 ^ 64 - 1)}]}
  | .counterLessThan name destination keys threshold => do
    pure {plan with
      operations := plan.operations ++ [← counterLessThanOp state name destination keys threshold]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .listLength name destination keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    let value : Expr (.uint (2 ^ 64 - 1)) := .ref destination
    pure {plan with
      operations := plan.operations ++ [.listLength slot alignedKeys value]
      reads := plan.reads ++ [{name := destination, ty := .uint (2 ^ 64 - 1)}]}
  | .mapIsEmpty name destination keys => do
    pure {plan with
      operations := plan.operations ++ [← mapIsEmptyOp state name destination keys]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .mapSize name destination keys => do
    pure {plan with
      operations := plan.operations ++ [← mapSizeOp state name destination keys]
      reads := plan.reads ++ [{name := destination, ty := .uint (2 ^ 64 - 1)}]}
  | .listHead name destination keys type destinations => do
    let slot ← stateSlot state name
    let (environment, foundType, fields) ← resolveListState state name keys
    unless foundType == type do throw "List head record type mismatch"
    let alignedKeys ← nativePathKeys keys
    let (schema, values, read) ← listHeadParts environment type destination fields destinations
    pure {plan with
      operations := plan.operations ++ [.listHead slot alignedKeys schema values]
      reads := plan.reads ++ [read]}
  | .listPushFront name keys type values => do
    let slot ← stateSlot state name
    let (environment, foundType, fields) ← resolveListState state name keys
    unless foundType == type do throw "List push record type mismatch"
    unless fields.map Prod.snd == values.map LedgerFieldExpr.ty do
      throw "List push record field type mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← listElementOperationSchema environment type
    pure {plan with operations := plan.operations ++ [
      .listPushFront slot alignedKeys schema values]}
  | .listPopFront name keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    pure {plan with operations := plan.operations ++ [.listPopFront slot alignedKeys]}
  | .listReset name keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    pure {plan with operations := plan.operations ++ [.listReset slot alignedKeys]}
  | .removePath name keys => do
    let slot ← stateSlot state name
    let some declaration := state.find? (·.name == name)
      | throw s!"unknown map or set state '{name}'"
    let some schema := declaration.kind.pathSchema
      | throw s!"state '{name}' is not a map or set"
    schema.removalPath keys
    let alignedKeys ← nativePathKeys keys
    pure {plan with operations := plan.operations ++ [.mapRemove slot alignedKeys]}
  | .readCompositePath name destination keys type destinations => do
    let slot ← stateSlot state name
    let .composite environment foundType ← resolveTreeState state name keys
      | throw "nested composite read must select a composite value"
    unless foundType == type do throw "nested composite read type mismatch"
    let fields ← if keys.isEmpty then
      LedgerValueType.cellRecordFields environment type
    else LedgerValueType.ledgerRecordFields environment type
    unless fields.map Prod.snd == destinations.map Prod.snd do
      throw "nested composite read destination type mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← if keys.isEmpty then cellRecordSchema environment type
      else recordSchema environment type
    let values := destinations.map fun (name, ty) => refLedgerFieldExpr name ty
    let components := destinations
    pure {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false alignedKeys, .popeqFields schema values]
      reads := plan.reads ++ [{name := destination, ty := .native, components := components, schema := some schema}]}
  | .memberPath name destination keys => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let (parents, finalKey) ← splitPath keys
    pure {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false parents, pushKey finalKey, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .memberRecordSet name destination keys values => do
    let (slot, schema) ← recordSetKeySchema state name keys values
    pure {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false (← nativePathKeys keys), .pushFields schema values false, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .memberRecordMap name destination values parentKeys => do
    let (slot, schema) ← anyRecordMapKeySchema state name values parentKeys
    pure {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false (← nativePathKeys parentKeys),
        .pushFields schema values false, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .setInsertRecord name keys values => do
    let (slot, schema) ← recordSetKeySchema state name keys values
    pure {plan with operations := plan.operations ++
      (← recordSetInsertOps slot (← nativePathKeys keys) schema values)}
  | .removeRecordSet name keys values => do
    let (slot, schema) ← recordSetKeySchema state name keys values
    pure {plan with operations := plan.operations ++ [
      .mapRemoveRecord slot schema (← nativePathKeys keys) values]}
  | .insertPath name keys ty value | .writePath name keys ty value => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let value ← match ty with
      | .foreign _ | .jubjubScalar | .jubjubPoint => storageWriteValue ty value
      | _ => pure (.push (← nativeAligned ty value) true)
    let operations ← pathWriteOps slot keys [value]
    pure {plan with operations := plan.operations ++ operations}
  | .writeCompositePath name keys type values => do
    let operations ← compositeWritePathOps state name keys type values
    pure {plan with operations := plan.operations ++ operations}
  | .counterAdjust name keys subtract amount => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    let alignedKeys ← nativePathKeys keys
    let operation := if subtract then Op.subImmediate amount else Op.addImmediate amount
    pure {plan with operations := plan.operations ++ [
      .indexPath slot true alignedKeys, operation, .insert (keys.length + 1)]}
  | .counterReset name keys => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    if keys.isEmpty then
      let value : Expr (.uint (2 ^ 64 - 1)) := .uint (2 ^ 64 - 1) 0
      pure {plan with operations := plan.operations ++ [
        .push (.field (.native slot)), .push (.counter value) true, .insert 1]}
    else
      let alignedKeys ← nativePathKeys keys
      let value : Expr (.uint (2 ^ 64 - 1)) := .uint (2 ^ 64 - 1) 0
      let operations ← pathWriteOps slot alignedKeys [.push (.counter value) true]
      pure {plan with operations := plan.operations ++ operations}
  | .emptyMapPath name keys => do
    pure {plan with operations := plan.operations ++ (← emptyMapOps state name keys)}
  | .setInsert name keys =>
    pure {plan with operations := plan.operations ++ (← setInsertOps state name keys)}

def appendEffects (state : List StateDecl) (effects : List Effect)
    (initial : Plan) : Except String Plan :=
  effects.foldlM (fun plan effect => appendEffect state effect plan) initial

/-- Lower one source effect. Writes bind their opcode groups to the activity
guard. Guarded requirements become assertions with no VM operation groups. -/
private def appendEffectWithActivity (state : List StateDecl) (effect : Effect)
    (guard : Option (Expr .bool)) (plan : Plan) : Except String Plan := do
  let loweredEffect ← match guard, effect with
    | none, _ => pure effect
    | some condition, .writeCell name ty value =>
      pure (.writeCell name ty (totalizeActivityValue condition [] value))
    | some condition, .writeMap name keyTy valueTy key value =>
      let avoid := expressionNames key ++ expressionNames value
      pure (.writeMap name keyTy valueTy
        (totalizeActivityKey condition avoid keyTy key)
        (totalizeActivityValue condition avoid value))
    | some condition, .claimContractCall address entryPointHash commitment =>
      let avoid := expressionNames address ++ expressionNames entryPointHash ++
        expressionNames commitment
      pure (.claimContractCall
        (totalizeActivityValue condition avoid address)
        (totalizeActivityValue condition avoid entryPointHash)
        (totalizeActivityValue condition avoid commitment))
    | some condition, .claimShielded kind digest =>
      pure (.claimShielded kind
        (totalizeActivityValue condition (expressionNames digest) digest))
    | some condition, .mintShielded domain amount =>
      pure (.mintShielded
        (totalizeActivityValue condition (expressionNames domain) domain)
        (totalizeActivityValue condition (expressionNames amount) amount))
    | some condition, .mintUnshielded domain amount =>
      pure (.mintUnshielded
        (totalizeActivityValue condition (expressionNames domain) domain)
        (totalizeActivityValue condition (expressionNames amount) amount))
    | some condition, .incUnshieldedInputs color amount isUnshielded =>
      pure (.incUnshieldedInputs
        (totalizeActivityValue condition (expressionNames color) color)
        (totalizeActivityValue condition (expressionNames amount) amount)
        (totalizeActivityValue condition (expressionNames isUnshielded) isUnshielded))
    | some condition, .incUnshieldedOutputs color amount isUnshielded =>
      pure (.incUnshieldedOutputs
        (totalizeActivityValue condition (expressionNames color) color)
        (totalizeActivityValue condition (expressionNames amount) amount)
        (totalizeActivityValue condition (expressionNames isUnshielded) isUnshielded))
    | some condition, .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient =>
      pure (.claimUnshieldedCoinSpend
        (totalizeActivityValue condition (expressionNames color) color)
        (totalizeActivityValue condition (expressionNames amount) amount)
        (totalizeActivityValue condition (expressionNames isUnshielded) isUnshielded)
        (totalizeActivityValue condition (expressionNames isContract) isContract)
        (totalizeActivityValue condition (expressionNames recipient) recipient))
    | some condition, .emitEvent kind payload =>
      pure (.emitEvent kind (totalizeActivityValue condition (expressionNames payload) payload))
    | some condition, .requireContractCaller address =>
      pure (.requireContractCaller (totalizeActivityValue condition (expressionNames address) address))
    | some _, .readCaller .. => pure effect
    | some condition, .readTokenBalance destination color isUnshielded query =>
      let limitNames := match query with
        | .exact => []
        | .compare _ limit => expressionNames limit
      let avoid := expressionNames color ++ expressionNames isUnshielded ++ limitNames
      let query := match query with
        | .exact => .exact
        | .compare less limit => .compare less (totalizeActivityValue condition avoid limit)
      pure (.readTokenBalance destination
        (totalizeActivityValue condition avoid color)
        (totalizeActivityValue condition avoid isUnshielded) query)
    | some condition, .blockTimeCompare destination before deadline =>
      pure (.blockTimeCompare destination before
        (totalizeActivityValue condition (expressionNames deadline) deadline))
    | some condition, .readMap name destination keyTy valueTy key =>
      pure (.readMap name destination keyTy valueTy
        (totalizeActivityKey condition (expressionNames key) keyTy key))
    | some condition, .readMember name destination keyTy valueTy key =>
      pure (.readMember name destination keyTy valueTy
        (totalizeActivityKey condition (expressionNames key) keyTy key))
    | some condition, .readPath name destination keys ty =>
      pure (.readPath name destination (totalizePathKeys condition keys) ty)
    | some condition, .readCompositePath name destination keys type destinations =>
      pure (.readCompositePath name destination (totalizePathKeys condition keys) type destinations)
    | some condition, .memberPath name destination keys =>
      pure (.memberPath name destination (totalizePathKeys condition keys))
    | some condition, .memberRecordSet name destination keys values =>
      let avoid := pathExpressionNames keys ++ ledgerFieldExprNames values
      pure (.memberRecordSet name destination (totalizePathKeys condition keys)
        (values.map (totalizeLedgerFieldExpr condition avoid)))
    | some condition, .readRecordMap name destination ty values parentKeys =>
      let avoid := pathExpressionNames parentKeys ++ ledgerFieldExprNames values
      pure (.readRecordMap name destination ty
        (values.map (totalizeLedgerFieldExpr condition avoid))
        (totalizePathKeys condition parentKeys))
    | some condition, .readRecordMapComposite name destination valueType values destinations parentKeys =>
      let avoid := pathExpressionNames parentKeys ++ ledgerFieldExprNames values
      pure (.readRecordMapComposite name destination valueType
        (values.map (totalizeLedgerFieldExpr condition avoid)) destinations
        (totalizePathKeys condition parentKeys))
    | some condition, .memberRecordMap name destination values parentKeys =>
      let avoid := pathExpressionNames parentKeys ++ ledgerFieldExprNames values
      pure (.memberRecordMap name destination
        (values.map (totalizeLedgerFieldExpr condition avoid))
        (totalizePathKeys condition parentKeys))
    | some condition, .writeRecordMap name values valueTy value parentKeys =>
      let avoid := pathExpressionNames parentKeys ++ ledgerFieldExprNames values ++
        expressionNames value
      pure (.writeRecordMap name
        (values.map (totalizeLedgerFieldExpr condition avoid)) valueTy
        (totalizeActivityValue condition avoid value)
        (totalizePathKeys condition parentKeys))
    | some condition, .writeRecordMapComposite name valueType keyValues valueValues parentKeys =>
      let avoid := pathExpressionNames parentKeys ++ ledgerFieldExprNames keyValues ++
        ledgerFieldExprNames valueValues
      pure (.writeRecordMapComposite name valueType
        (keyValues.map (totalizeLedgerFieldExpr condition avoid))
        (valueValues.map (totalizeLedgerFieldExpr condition avoid))
        (totalizePathKeys condition parentKeys))
    | some condition, .removeRecordMap name values parentKeys =>
      let avoid := pathExpressionNames parentKeys ++ ledgerFieldExprNames values
      pure (.removeRecordMap name
        (values.map (totalizeLedgerFieldExpr condition avoid))
        (totalizePathKeys condition parentKeys))
    | some condition, .counterRead name destination keys =>
      pure (.counterRead name destination (totalizePathKeys condition keys))
    | some condition, .counterLessThan name destination keys threshold =>
      let avoid := pathExpressionNames keys ++ expressionNames threshold
      pure (.counterLessThan name destination (totalizePathKeys condition keys)
        (totalizeActivityValue condition avoid threshold))
    | some condition, .counterAdjust name keys subtract amount =>
      let amount := match amount with
        | .uint _ _ => amount
        | _ => totalizeActivityValue condition
            (pathExpressionNames keys ++ expressionNames amount) amount
      pure (.counterAdjust name (totalizePathKeys condition keys) subtract amount)
    | some condition, .counterReset name keys =>
      pure (.counterReset name (totalizePathKeys condition keys))
    | some condition, .listLength name destination keys =>
      pure (.listLength name destination (totalizePathKeys condition keys))
    | some condition, .mapIsEmpty name destination keys =>
      pure (.mapIsEmpty name destination (totalizePathKeys condition keys))
    | some condition, .mapSize name destination keys =>
      pure (.mapSize name destination (totalizePathKeys condition keys))
    | some condition, .listHead name destination keys type destinations =>
      pure (.listHead name destination (totalizePathKeys condition keys) type destinations)
    | some condition, .listPushFront name keys type values =>
      let avoid := pathExpressionNames keys ++ ledgerFieldExprNames values
      pure (.listPushFront name (totalizePathKeys condition keys) type
        (values.map (totalizeLedgerFieldExpr condition avoid)))
    | some condition, .setInsertRecord name keys values =>
      let avoid := pathExpressionNames keys ++ ledgerFieldExprNames values
      pure (.setInsertRecord name (totalizePathKeys condition keys)
        (values.map (totalizeLedgerFieldExpr condition avoid)))
    | some condition, .removeRecordSet name keys values =>
      let avoid := pathExpressionNames keys ++ ledgerFieldExprNames values
      pure (.removeRecordSet name (totalizePathKeys condition keys)
        (values.map (totalizeLedgerFieldExpr condition avoid)))
    | some condition, .listPopFront name keys =>
      pure (.listPopFront name (totalizePathKeys condition keys))
    | some condition, .listReset name keys =>
      pure (.listReset name (totalizePathKeys condition keys))
    | some condition, .merkleTreeInsertHash name hash =>
      pure (.merkleTreeInsertHash name
        (totalizeActivityValue condition (expressionNames hash) hash))
    | some condition, .merkleTreeInsertHashIndex name hash index =>
      let avoid := expressionNames hash ++ expressionNames index
      pure (.merkleTreeInsertHashIndex name
        (totalizeActivityValue condition avoid hash)
        (totalizeActivityValue condition avoid index))
    | some condition, .merkleTreeCheckRoot name expected destination =>
      pure (.merkleTreeCheckRoot name
        (totalizeActivityValue condition (expressionNames expected) expected) destination)
    | some condition, .merkleTreeIsFullAt name keys destination =>
      pure (.merkleTreeIsFullAt name (totalizePathKeys condition keys) destination)
    | some condition, .merkleTreeCheckRootAt name keys expected destination =>
      let avoid := pathExpressionNames keys ++ expressionNames expected
      pure (.merkleTreeCheckRootAt name (totalizePathKeys condition keys)
        (totalizeActivityValue condition avoid expected) destination)
    | some condition, .merkleTreeInsertHashAt name keys hash =>
      let avoid := pathExpressionNames keys ++ expressionNames hash
      pure (.merkleTreeInsertHashAt name (totalizePathKeys condition keys)
        (totalizeActivityValue condition avoid hash))
    | some condition, .merkleTreeInsertHashIndexAt name keys hash index =>
      let avoid := pathExpressionNames keys ++ expressionNames hash ++ expressionNames index
      pure (.merkleTreeInsertHashIndexAt name (totalizePathKeys condition keys)
        (totalizeActivityValue condition avoid hash)
        (totalizeActivityValue condition avoid index))
    | some condition, .merkleTreeResetAt name keys depth historic emptyHistory =>
      pure (.merkleTreeResetAt name (totalizePathKeys condition keys) depth historic emptyHistory)
    | some condition, .merkleTreeResetHistoryAt name keys =>
      pure (.merkleTreeResetHistoryAt name (totalizePathKeys condition keys))
    | some _, .merkleTreeReset .. | some _, .merkleTreeResetHistory .. => pure effect
    | some condition, .removePath name keys =>
      pure (.removePath name (totalizePathKeys condition keys))
    | some condition, .insertPath name keys ty value =>
      let avoid := pathExpressionNames keys ++ expressionNames value
      pure (.insertPath name (totalizePathKeys condition keys) ty
        (totalizeActivityValue condition avoid value))
    | some condition, .writePath name keys ty value =>
      let avoid := pathExpressionNames keys ++ expressionNames value
      pure (.writePath name (totalizePathKeys condition keys) ty
        (totalizeActivityValue condition avoid value))
    | some condition, .writeCompositePath name keys type values =>
      let avoid := pathExpressionNames keys ++ ledgerFieldExprNames values
      pure (.writeCompositePath name (totalizePathKeys condition keys) type
        (values.map (totalizeLedgerFieldExpr condition avoid)))
    | some condition, .emptyMapPath name keys =>
      pure (.emptyMapPath name (totalizePathKeys condition keys))
    | some condition, .setInsert name keys =>
      pure (.setInsert name (totalizePathKeys condition keys))
    | some _, .readCell .. | some _, .readContractAddress .. |
        some _, .merkleTreeIsFull .. | some _, .checkpoint => pure effect
    | some condition, .require required =>
      pure (.require (totalizeActivityCondition condition required))
    | some _, _ => throw "native guards are supported only on ledger reads, writes, and require effects"
  let before := plan.operations.length
  let result ← appendEffect state loweredEffect plan
  let added := result.operations.length - before
  match guard, effect with
  | some _, .require _ => pure result
  | some condition, .readCell .. | some condition, .readMap .. | some condition, .readMember .. |
      some condition, .blockTimeCompare .. =>
    let readIndex := plan.reads.length
    let some read := result.reads[readIndex]? | throw "guarded read did not append a read binding"
    let reads := result.reads.take readIndex ++ [{read with guard := some condition}]
    let priorGuards := if plan.activityGuards.isEmpty then List.replicate before none
      else plan.activityGuards
    pure {result with
      reads := reads
      activityGuards := priorGuards ++ List.replicate added (some condition)}
  | some condition, .readContractAddress .. | some condition, .readPath .. | some condition, .readCompositePath .. |
      some condition, .memberPath .. | some condition, .memberRecordSet .. |
      some condition, .memberRecordMap .. | some condition, .readRecordMap .. |
      some condition, .readRecordMapComposite .. | some condition, .counterRead .. |
      some condition, .counterLessThan .. |
      some condition, .listLength .. | some condition, .listHead .. |
      some condition, .readTokenBalance .. | some condition, .mapSize .. | some condition, .mapIsEmpty .. |
      some condition, .merkleTreeIsFull .. | some condition, .merkleTreeCheckRoot .. |
      some condition, .merkleTreeIsFullAt .. | some condition, .merkleTreeCheckRootAt .. =>
    let readIndex := plan.reads.length
    let some read := result.reads[readIndex]? | throw "guarded nested read did not append a read binding"
    let reads := result.reads.take readIndex ++ [{read with guard := some condition}]
    let priorGuards := if plan.activityGuards.isEmpty then List.replicate before none
      else plan.activityGuards
    pure {result with
      reads := reads
      activityGuards := priorGuards ++ List.replicate added (some condition)}
  | some condition, .writeCell .. | some condition, .writeMap .. |
      some condition, .writeRecordMap .. | some condition, .writeRecordMapComposite .. =>
    let priorGuards := if plan.activityGuards.isEmpty then List.replicate before none
      else plan.activityGuards
    pure {result with activityGuards := priorGuards ++ List.replicate added (some condition)}
  | some condition, .requireContractCaller .. | some condition, .readCaller .. =>
    let priorGuards := if plan.activityGuards.isEmpty then List.replicate before none
      else plan.activityGuards
    let reads := plan.reads ++ ((result.reads.drop plan.reads.length).map fun read =>
      {read with guard := some condition})
    pure {result with reads, activityGuards := priorGuards ++ List.replicate added (some condition)}
  | some condition, .insertPath .. | some condition, .writePath .. |
      some condition, .writeCompositePath .. | some condition, .emptyMapPath .. |
      some condition, .counterAdjust .. | some condition, .counterReset .. |
      some condition, .listPushFront .. | some condition, .listPopFront .. |
      some condition, .listReset .. | some condition, .removePath .. |
      some condition, .setInsert .. | some condition, .setInsertRecord .. |
      some condition, .removeRecordSet .. | some condition, .removeRecordMap .. |
      some condition, .merkleTreeInsertHash .. | some condition, .merkleTreeReset .. |
      some condition, .merkleTreeInsertHashIndex .. |
      some condition, .merkleTreeResetHistory .. |
      some condition, .merkleTreeInsertHashAt .. | some condition, .merkleTreeInsertHashIndexAt .. |
      some condition, .merkleTreeResetAt .. | some condition, .merkleTreeResetHistoryAt .. |
      some condition, .claimContractCall .. | some condition, .claimShielded .. |
      some condition, .mintShielded .. |
      some condition, .relayShieldedImmediate .. |
      some condition, .mintUnshielded .. | some condition, .incUnshieldedInputs .. |
      some condition, .incUnshieldedOutputs .. | some condition, .claimUnshieldedCoinSpend .. |
      some condition, .emitEvent .. | some condition, .checkpoint =>
    let priorGuards := if plan.activityGuards.isEmpty then List.replicate before none
      else plan.activityGuards
    pure {result with activityGuards := priorGuards ++ List.replicate added (some condition)}
  | none, _ =>
    if plan.activityGuards.isEmpty then pure result
    else
      let priorGuards := plan.activityGuards
      pure {result with activityGuards := priorGuards ++ List.replicate added none}
  | some _, _ => throw "native guards are supported only on ledger reads, writes, and require effects"

/-- Lower ordered effects while keeping optional activity guards aligned with
each emitted opcode group, and record the exclusive operation end after each
source effect. -/
def appendEffectsGuardedWithBoundaries (state : List StateDecl) (effects : List Effect)
    (guards : List (Option (Expr .bool))) (initial : Plan) :
    Except String (Plan × List Nat) := do
  unless guards.isEmpty || guards.length == effects.length do
    throw "effect guard metadata length mismatch"
  let mut plan := initial
  let mut boundaries := []
  for (effect, index) in effects.zipIdx do
    plan ← appendEffectWithActivity state effect (guards[index]?.getD none) plan
    boundaries := plan.operations.length :: boundaries
  pure (plan, boundaries.reverse)

private theorem guardedLoop_boundary_count (state : List StateDecl)
    (guards : List (Option (Expr .bool))) (items : List (Effect × Nat))
    (initial result : Plan) (before after : List Nat)
    (accepted : forIn items (initial, before)
      (fun (item : Effect × Nat) (current : Plan × List Nat) => do
      let next ← appendEffectWithActivity state item.1
        (guards[item.2]?.getD none) current.1
      pure (ForInStep.yield (next, next.operations.length :: current.2))) =
        .ok (result, after)) :
    after.length = before.length + items.length := by
  induction items generalizing initial result before after with
  | nil =>
    simp only [List.forIn_nil] at accepted
    have pairEq := Except.ok.inj accepted
    cases pairEq
    simp
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    simp only [bind, Except.bind] at accepted
    cases first : appendEffectWithActivity state item.1
        (guards[item.2]?.getD none) initial with
    | error message => simp [first] at accepted
    | ok next =>
      simp only [first, pure_bind] at accepted
      have restAccepted : forIn rest (next, next.operations.length :: before)
          (fun (item : Effect × Nat) (current : Plan × List Nat) => do
            let later ← appendEffectWithActivity state item.1
              (guards[item.2]?.getD none) current.1
            pure (ForInStep.yield (later, later.operations.length :: current.2))) =
          .ok (result, after) := by
        change (forIn rest (next, next.operations.length :: before)
          (fun (item : Effect × Nat) (current : Plan × List Nat) => do
            let later ← appendEffectWithActivity state item.1
              (guards[item.2]?.getD none) current.1
            pure (ForInStep.yield (later, later.operations.length :: current.2)))) =
          .ok (result, after) at accepted
        exact accepted
      have tail := ih next result (next.operations.length :: before) after restAccepted
      simp only [List.length_cons] at tail ⊢
      omega

private theorem guardedLoop_last_boundary (state : List StateDecl)
    (guards : List (Option (Expr .bool))) (items : List (Effect × Nat))
    (initial result : Plan) (before after : List Nat)
    (accepted : forIn items (initial, before)
      (fun (item : Effect × Nat) (current : Plan × List Nat) => do
      let next ← appendEffectWithActivity state item.1
        (guards[item.2]?.getD none) current.1
      pure (ForInStep.yield (next, next.operations.length :: current.2))) =
        .ok (result, after)) :
    items ≠ [] → after.head? = some result.operations.length := by
  induction items generalizing initial result before after with
  | nil => simp
  | cons item rest ih =>
    intro _
    rw [List.forIn_cons] at accepted
    simp only [bind, Except.bind] at accepted
    cases first : appendEffectWithActivity state item.1
        (guards[item.2]?.getD none) initial with
    | error message => simp [first] at accepted
    | ok next =>
      simp only [first, pure_bind] at accepted
      have restAccepted : forIn rest (next, next.operations.length :: before)
          (fun (item : Effect × Nat) (current : Plan × List Nat) => do
            let later ← appendEffectWithActivity state item.1
              (guards[item.2]?.getD none) current.1
            pure (ForInStep.yield (later, later.operations.length :: current.2))) =
          .ok (result, after) := by
        change (forIn rest (next, next.operations.length :: before)
          (fun (item : Effect × Nat) (current : Plan × List Nat) => do
            let later ← appendEffectWithActivity state item.1
              (guards[item.2]?.getD none) current.1
            pure (ForInStep.yield (later, later.operations.length :: current.2)))) =
          .ok (result, after) at accepted
        exact accepted
      cases rest with
      | nil =>
        simp only [List.forIn_nil] at restAccepted
        have pairEq := Except.ok.inj restAccepted
        have resultEq := (Prod.mk.inj pairEq).1
        have afterEq := (Prod.mk.inj pairEq).2
        cases resultEq
        cases afterEq
        rfl
      | cons head tail =>
        exact ih next result (next.operations.length :: before) after
          restAccepted (by simp)

/-- Successful guarded lowering records exactly one exclusive end offset for
each source effect, including effects that emit no operations. -/
theorem appendEffectsGuardedWithBoundaries_count (state : List StateDecl)
    (effects : List Effect) (guards : List (Option (Expr .bool)))
    (initial result : Plan) (boundaries : List Nat)
    (accepted : appendEffectsGuardedWithBoundaries state effects guards
      initial = .ok (result, boundaries)) :
    boundaries.length = effects.length := by
  unfold appendEffectsGuardedWithBoundaries at accepted
  split at accepted
  · let step := fun (item : Effect × Nat) (current : Plan × List Nat) => do
      let next ← appendEffectWithActivity state item.1
        (guards[item.2]?.getD none) current.1
      pure (ForInStep.yield (next, next.operations.length :: current.2))
    change (forIn effects.zipIdx (initial, []) step).map
      (fun current => (current.1, current.2.reverse)) = .ok (result, boundaries) at accepted
    cases loop : forIn effects.zipIdx (initial, []) step with
    | error message =>
      simp [loop, Functor.map, Except.map] at accepted
    | ok current =>
      have mapped : (Except.ok (current.1, current.2.reverse) :
          Except String (Plan × List Nat)) = .ok (result, boundaries) := by
        simpa [loop, Functor.map, Except.map] using accepted
      have outputEq : (current.1, current.2.reverse) = (result, boundaries) :=
        Except.ok.inj mapped
      have count := guardedLoop_boundary_count state guards effects.zipIdx
        initial current.1 [] current.2 loop
      have boundaryEq : current.2.reverse = boundaries := (Prod.mk.inj outputEq).2
      have count' : current.2.length = effects.length := by simpa using count
      calc
        boundaries.length = current.2.reverse.length := by rw [boundaryEq]
        _ = current.2.length := List.length_reverse
        _ = effects.length := count'
  · simp [bind, Except.bind] at accepted

/-- The last returned offset is the operation length after the final source
effect. Equal offsets are valid when an effect emits no operations. -/
theorem appendEffectsGuardedWithBoundaries_lastOffset (state : List StateDecl)
    (effects : List Effect) (guards : List (Option (Expr .bool)))
    (initial result : Plan) (boundaries : List Nat)
    (accepted : appendEffectsGuardedWithBoundaries state effects guards
      initial = .ok (result, boundaries)) (nonempty : effects ≠ []) :
    boundaries.reverse.head? = some result.operations.length := by
  unfold appendEffectsGuardedWithBoundaries at accepted
  split at accepted
  · let step := fun (item : Effect × Nat) (current : Plan × List Nat) => do
      let next ← appendEffectWithActivity state item.1
        (guards[item.2]?.getD none) current.1
      pure (ForInStep.yield (next, next.operations.length :: current.2))
    change (forIn effects.zipIdx (initial, []) step).map
      (fun current => (current.1, current.2.reverse)) = .ok (result, boundaries) at accepted
    cases loop : forIn effects.zipIdx (initial, []) step with
    | error message => simp [loop, Functor.map, Except.map] at accepted
    | ok current =>
      have mapped : (Except.ok (current.1, current.2.reverse) :
          Except String (Plan × List Nat)) = .ok (result, boundaries) := by
        simpa [loop, Functor.map, Except.map] using accepted
      have outputEq := Except.ok.inj mapped
      have latest := guardedLoop_last_boundary state guards effects.zipIdx
        initial current.1 [] current.2 loop (by
          cases effects with
          | nil => contradiction
          | cons _ _ => simp [List.zipIdx])
      have planEq := (Prod.mk.inj outputEq).1
      have boundaryEq := (Prod.mk.inj outputEq).2
      calc
        boundaries.reverse.head? = current.2.head? := by
          rw [← boundaryEq]
          simp
        _ = some current.1.operations.length := latest
        _ = some result.operations.length := by rw [planEq]
  · simp [bind, Except.bind] at accepted

/-- Lower ordered effects while keeping optional activity guards aligned with
each emitted opcode group. -/
def appendEffectsGuarded (state : List StateDecl) (effects : List Effect)
    (guards : List (Option (Expr .bool))) (initial : Plan) : Except String Plan :=
  (appendEffectsGuardedWithBoundaries state effects guards initial).map Prod.fst

private def publicInputStep (input : Input) (plan : Plan) : Except String Plan := do
  if input.visibility != .«public» then return plan
  match input.ty with
  | .bytes 32 =>
    let bytes : Expr (.bytes 32) := .ref input.name
    let value := Aligned.bytes32 bytes
    pure {plan with
      operations := plan.operations ++ [.push value, .popeq value]
      reads := plan.reads ++ [{name := input.name, ty := .bytes 32}]}
  | .bytes 0 => pure plan
  | .bytes length =>
    let bytes : Expr (.bytes length) := .ref input.name
    let value := Aligned.bytes length bytes
    pure {plan with
      operations := plan.operations ++ [.push value, .popeq value]
      reads := plan.reads ++ [{name := input.name, ty := .bytes length}]}
  | .jubjubScalar => do
    let scalar : Expr .jubjubScalar := .ref input.name
    let value := Aligned.field (.jubjubScalarToNative scalar)
    let name := input.publicProjectionIdentifiers[0]!
    pure {plan with
      operations := plan.operations ++ [.push value, .popeq value]
      reads := plan.reads ++ [{name, ty := .native}]}
  | .jubjubPoint => do
    let point : Expr .jubjubPoint := .ref input.name
    let mut result := plan
    for index in [0, 1] do
      let value := Aligned.field (.jubjubCoordinate point index)
      let name := input.publicProjectionIdentifiers[index]!
      result := {result with
        operations := result.operations ++ [.push value, .popeq value]
        reads := result.reads ++ [{name, ty := .native}]}
    pure result
  | .foreign kind => do
    let value : Expr (.foreign kind) := .ref input.name
    let mut result := plan
    for index in List.range kind.encodedFieldCount do
      let aligned := Aligned.field (.foreignEncodedField value index)
      let name := input.publicProjectionIdentifiers[index]!
      result := {result with
        operations := result.operations ++ [.push aligned, .popeq aligned]
        reads := result.reads ++ [{name, ty := .native}]}
    pure result
  | .opaqueBytes => do
    let value := Aligned.compress (.ref input.name)
    pure {plan with
      operations := plan.operations ++ [.push value, .popeq value]
      reads := plan.reads ++ [{name := input.name, ty := .opaqueBytes}]}
  | .opaqueString => do
    let value := Aligned.compressString (.ref input.name)
    pure {plan with
      operations := plan.operations ++ [.push value, .popeq value]
      reads := plan.reads ++ [{name := input.name, ty := .opaqueString}]}
  | .native | .bool | .uint _ => do
    let value := Aligned.field (← nativeRead input.ty input.name)
    pure { plan with
      operations := plan.operations ++ [.push value, .popeq value]
      reads := plan.reads ++ [{name := input.name, ty := input.ty}] }

private def appendPublicInput := publicInputStep

/-- The exact public-input prefix used before source effects. -/
def publicInputPlan (inputs : List Input) (initial : Plan := {}) : Except String Plan :=
  inputs.foldlM (fun plan input => appendPublicInput input plan) initial

/-- Reads introduced by one public circuit input, in the order used by the
public transcript. Compound curve and foreign values contribute their native
projections in projection order. -/
def publicInputReads (input : Input) : List Read :=
  if input.visibility != .«public» then [] else
  match input.ty with
  | .bytes 0 => []
  | .bytes length => [{name := input.name, ty := .bytes length}]
  | .jubjubScalar =>
    [{name := input.publicProjectionIdentifiers[0]!, ty := .native}]
  | .jubjubPoint =>
    [{name := input.publicProjectionIdentifiers[0]!, ty := .native},
      {name := input.publicProjectionIdentifiers[1]!, ty := .native}]
  | .foreign kind =>
    (List.range kind.encodedFieldCount).map fun index =>
      {name := input.publicProjectionIdentifiers[index]!, ty := .native}
  | .opaqueBytes => [{name := input.name, ty := .opaqueBytes}]
  | .opaqueString => [{name := input.name, ty := .opaqueString}]
  | .native | .bool | .uint _ => [{name := input.name, ty := input.ty}]

private theorem visibilityNePublic (visibility : Visibility) :
    (visibility != .public) = (visibility == .private) := by
  cases visibility <;> decide

private theorem visibilityEqPrivate (visibility : Visibility) :
    (visibility == .private) = (if visibility = .private then true else false) := by
  cases visibility <;> decide

private theorem foldl_planReads_append {α} (items : List α) (initial : Plan)
    (step : Plan → α → Plan) (read : α → Read)
    (stepReads : ∀ plan item, (step plan item).reads = plan.reads ++ [read item]) :
    (items.foldl step initial).reads = initial.reads ++ items.map read := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
    simp only [List.foldl_cons]
    rw [ih, stepReads]
    simp [List.map, List.append_assoc]

private theorem publicInputStep_reads (input : Input) (initial result : Plan)
    (accepted : publicInputStep input initial = .ok result) :
    result.reads = initial.reads ++ publicInputReads input := by
  cases input with
  | mk name ty visibility span =>
    cases visibility <;> cases ty
    case public.bytes length =>
      by_cases is32 : length = 32
      · subst length
        simp [publicInputStep, publicInputReads, visibilityNePublic, visibilityEqPrivate]
          at accepted ⊢ <;> cases accepted <;> rfl
      · by_cases isZero : length = 0
        · subst length
          simp [publicInputStep, publicInputReads, visibilityNePublic, visibilityEqPrivate]
            at accepted ⊢ <;> cases accepted <;> rfl
        · simp [publicInputStep, publicInputReads, visibilityNePublic,
            visibilityEqPrivate] at accepted ⊢ <;> cases accepted <;> rfl
    case public.foreign kind =>
      simp [publicInputStep, publicInputReads, Input.publicProjectionIdentifiers,
        visibilityNePublic, visibilityEqPrivate] at accepted ⊢
      cases accepted
      apply foldl_planReads_append
      intro plan index
      rfl
    all_goals
      simp [publicInputStep, publicInputReads, Input.publicProjectionIdentifiers,
        nativeRead, visibilityNePublic, visibilityEqPrivate] at accepted ⊢ <;>
        cases accepted <;> rfl

private theorem exceptBindOk {ε α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- A successful public-input fold records its generated reads in source
input order. Compound curve and foreign values follow their projection order. -/
theorem publicInputPlan_reads_order (inputs : List Input) (initial result : Plan)
    (accepted : publicInputPlan inputs initial = .ok result) :
    result.reads = initial.reads ++ inputs.flatMap publicInputReads := by
  induction inputs generalizing initial with
  | nil =>
    simp [publicInputPlan] at accepted
    cases accepted
    simp
  | cons input rest ih =>
    change (publicInputStep input initial >>= fun next =>
      publicInputPlan rest next) = .ok result at accepted
    simp only [exceptBindOk] at accepted
    rcases accepted with ⟨next, firstAccepted, restAccepted⟩
    have first := publicInputStep_reads input initial next firstAccepted
    have remaining := ih next restAccepted
    rw [remaining, first]
    simp [List.flatMap_cons, List.append_assoc]

/-- Inputs accepted by the scalar transcript prefix: private values are
omitted, while public values use the scalar Native alignment. -/
def publicInputScalarCompatible (input : Input) : Prop :=
  input.visibility = .«private» ∨ input.ty = .native ∨ input.ty = .bool ∨
    ∃ maximum, input.ty = .uint maximum

/-- Exact operation pairs contributed by one public Native, Bool, or UInt
input. The list order matches the source input order. -/
def publicInputScalarOperations (input : Input) : List Op :=
  match input.visibility, input.ty with
  | .«public», .native =>
    let value := Aligned.field (.ref input.name : Expr .native)
    [.push value, .popeq value]
  | .«public», .bool =>
    let value := Aligned.field (.cast .native (.ref input.name : Expr .bool))
    [.push value, .popeq value]
  | .«public», .uint maximum =>
    let value := Aligned.field (.cast .native (.ref input.name : Expr (.uint maximum)))
    [.push value, .popeq value]
  | _, _ => []

private theorem publicInputStep_scalar_operations (input : Input)
    (initial result : Plan)
    (compatible : publicInputScalarCompatible input)
    (accepted : publicInputStep input initial = .ok result) :
    result.operations = initial.operations ++ publicInputScalarOperations input := by
  cases input with
  | mk name ty visibility span =>
    cases visibility with
    | «private» =>
      simp [publicInputStep, publicInputScalarOperations,
        visibilityNePublic, visibilityEqPrivate] at accepted ⊢ <;>
        cases accepted <;> rfl
    | «public» =>
      cases ty with
      | native | bool | uint _ =>
        simp [publicInputStep, publicInputScalarOperations, nativeRead,
          visibilityNePublic, visibilityEqPrivate] at accepted ⊢ <;>
          cases accepted <;> rfl
      | bytes length | opaqueBytes | opaqueString | jubjubScalar | jubjubPoint | foreign _ =>
        simp [publicInputScalarCompatible] at compatible

/-- For scalar-qualified circuit inputs, the fallible public-input fold emits
exactly the ordered scalar push/popeq pairs used by the VM prefix. -/
theorem publicInputPlan_scalar_operations (inputs : List Input) (initial plan : Plan)
    (accepted : publicInputPlan inputs initial = .ok plan)
    (compatible : ∀ input ∈ inputs, publicInputScalarCompatible input) :
    plan.operations = initial.operations ++
      inputs.flatMap publicInputScalarOperations := by
  induction inputs generalizing initial plan with
  | nil =>
    simp [publicInputPlan] at accepted
    cases accepted
    simp
  | cons input rest ih =>
    change (publicInputStep input initial >>= fun next =>
      publicInputPlan rest next) = .ok plan at accepted
    simp only [exceptBindOk] at accepted
    rcases accepted with ⟨next, firstAccepted, restAccepted⟩
    have firstShape := publicInputStep_scalar_operations input initial next
      (compatible input (by simp)) firstAccepted
    have restCompatible : ∀ item ∈ rest, publicInputScalarCompatible item := by
      intro item member
      exact compatible item (by simp [member])
    have restShape := ih next plan restAccepted restCompatible
    rw [restShape, firstShape]
    simp [List.flatMap_cons, List.append_assoc]

private def previousPublicInputStep (input : Input) (plan : Plan) : Except String Plan :=
  publicInputStep input plan

private def previousPublicInputLoop (inputs : List Input) (initial : Plan) : Except String Plan := do
  let mut plan := initial
  for input in inputs do
    plan ← previousPublicInputStep input plan
  pure plan

/-- The old mutable public-input loop equals the production pure prefix for
all input lists and starting plans. -/
theorem previousPublicInputLoop_eq_publicInputPlan (inputs : List Input)
    (initial : Plan) :
    previousPublicInputLoop inputs initial = publicInputPlan inputs initial := by
  unfold previousPublicInputLoop
  simp only [bind_pure]
  change (forIn inputs initial (fun input plan => do
      let result ← previousPublicInputStep input plan
      pure (ForInStep.yield result))) =
    inputs.foldlM (fun plan input => appendPublicInput input plan) initial
  have stepEq (input : Input) (plan : Plan) :
      (do let result ← previousPublicInputStep input plan
          pure (ForInStep.yield result)) =
        ForInStep.yield <$> previousPublicInputStep input plan := by
    cases previousPublicInputStep input plan <;> rfl
  simp only [stepEq]
  rw [List.forIn_yield_eq_foldlM]
  simp only [previousPublicInputStep, appendPublicInput]
  have mapIdentity (plan : Plan) (input : Input) :
      (fun result : Plan => result) <$> publicInputStep input plan =
        publicInputStep input plan := by
    cases publicInputStep input plan <;> rfl
  simp only [mapIdentity]

/-- Imperative counterpart retained for the kernel equivalence check. -/
private def previousEffectStep (state : List StateDecl) (effect : Effect)
    (initial : Plan) : Except String Plan := do
  let mut plan := initial
  match effect with
  | .readCell name destination ty =>
    let slot ← stateSlot state name
    let alignment := stateCellAlignment state name
    let value ← storageReadValueWithAlignment ty destination alignment
    let provenance := if alignment == some .u128 then some (name, slot, value.fields) else none
    let read : Read := {name := destination, ty, rootCellRead := provenance}
    plan := { plan with
      operations := plan.operations ++ [.dup, .index slot, value]
      reads := plan.reads ++ [read] }
  | .merkleTreeIsFull name destination => do
    let operation ← merkleTreeIsFullOp state name destination
    plan := {plan with
      operations := plan.operations ++ [operation]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .merkleTreeCheckRoot name expected destination => do
    let operation ← merkleTreeCheckRootOp state name expected destination
    plan := {plan with
      operations := plan.operations ++ [operation]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .merkleTreeInsertHash name hash => do
    let operation ← merkleTreeInsertHashOp state name hash
    plan := {plan with operations := plan.operations ++ [operation]}
  | .merkleTreeInsertHashIndex name hash index => do
    let operation ← merkleTreeInsertHashIndexOp state name hash index
    plan := {plan with operations := plan.operations ++ [operation]}
  | .merkleTreeReset name => do
    let operation ← merkleTreeResetOp state name
    plan := {plan with operations := plan.operations ++ [operation]}
  | .merkleTreeResetHistory name => do
    let operation ← merkleTreeResetHistoryOp state name
    plan := {plan with operations := plan.operations ++ [operation]}
  | .merkleTreeIsFullAt name keys destination => do
    let operation ← merkleTreeIsFullAtOp state name destination keys
    plan := {plan with
      operations := plan.operations ++ [operation]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .merkleTreeCheckRootAt name keys expected destination => do
    let operation ← merkleTreeCheckRootAtOp state name keys expected destination
    plan := {plan with
      operations := plan.operations ++ [operation]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .merkleTreeInsertHashAt name keys hash => do
    let operation ← merkleTreeInsertHashAtOp state name keys hash
    plan := {plan with operations := plan.operations ++ [operation]}
  | .merkleTreeInsertHashIndexAt name keys hash index => do
    let operation ← merkleTreeInsertHashIndexAtOp state name keys hash index
    plan := {plan with operations := plan.operations ++ [operation]}
  | .merkleTreeResetAt name keys depth historic emptyHistory => do
    let operation ← merkleTreeResetAtOp state name keys depth historic emptyHistory
    plan := {plan with operations := plan.operations ++ [operation]}
  | .merkleTreeResetHistoryAt name keys => do
    let operation ← merkleTreeResetHistoryAtOp state name keys
    plan := {plan with operations := plan.operations ++ [operation]}
  | .require condition =>
    plan := {plan with guards := plan.guards ++ [condition]}
  | .claimContractCall address entryPointHash commitment =>
    plan := {plan with operations := plan.operations ++ [
      .claimContractCall address entryPointHash commitment]}
  | .claimShielded kind digest =>
    plan := {plan with operations := plan.operations ++ [.claimShielded kind digest]}
  | .receiveShieldedToMap stateName nonce color amount selfAddress => do
    let slot ← stateSlot state stateName
    if slot > 255 then throw "shielded coin map index exceeds native u8 range"
    let commitment := shieldedCoinDigest "midnight:zswap-cc[v1]" 0 nonce color amount selfAddress
    plan := {plan with operations := plan.operations ++ [
      .receiveShieldedToMap slot nonce color amount commitment]}
  | .insertShieldedCoinMap stateName key nonce color amount isContract recipient keys => do
    let operation ← insertShieldedCoinMapOp state stateName keys key nonce color amount isContract recipient
    plan := {plan with operations := plan.operations ++ [operation]}
  | .insertShieldedCoinSet stateName nonce color amount selfAddress keys => do
    let operation ← insertShieldedCoinSetOp state stateName keys nonce color amount selfAddress
    plan := {plan with operations := plan.operations ++ [operation]}
  | .insertShieldedCoinSetTo stateName nonce color amount isContract recipient keys => do
    let operation ← insertShieldedCoinSetToOp state stateName keys nonce color amount
      isContract recipient
    plan := {plan with operations := plan.operations ++ [operation]}
  | .writeShieldedCoinCell stateName nonce color amount selfAddress => do
    let slot ← stateSlot state stateName
    if slot > 255 then throw "shielded coin Cell index exceeds native u8 range"
    let commitment := shieldedCoinDigest "midnight:zswap-cc[v1]" 0 nonce color amount selfAddress
    plan := {plan with operations := plan.operations ++ [
      .writeShieldedCoinCell slot nonce color amount commitment]}
  | .writeShieldedCoinCellTo stateName nonce color amount isContract recipient => do
    let slot ← stateSlot state stateName
    if slot > 255 then throw "shielded coin Cell index exceeds native u8 range"
    let commitment := shieldedCoinDigestForRecipient
      "midnight:zswap-cc[v1]" nonce color amount isContract recipient
    plan := {plan with operations := plan.operations ++ [
      .writeShieldedCoinCellTo slot nonce color amount isContract recipient commitment]}
  | .pushFrontCoin stateName nonce color amount selfAddress keys => do
    let operation ← pushFrontCoinOp state stateName keys nonce color amount selfAddress
    plan := {plan with operations := plan.operations ++ [operation]}
  | .pushFrontCoinTo stateName nonce color amount isContract recipient keys => do
    let operation ← pushFrontCoinToOp state stateName keys nonce color amount isContract recipient
    plan := {plan with operations := plan.operations ++ [operation]}
  | .spendShieldedFromMap _ nonce color amount recipient selfAddress =>
    plan := {plan with operations := plan.operations ++ [
      spendShieldedOp nonce color amount recipient selfAddress]}
  | .mergeShieldedFromMap _ nonceA colorA amountA nonceB colorB amountB selfAddress staged =>
    plan := {plan with operations := plan.operations ++ [
      mergeShieldedOp nonceA colorA amountA nonceB colorB amountB selfAddress staged]}
  | .sendShieldedFromMap _ nonce color inputAmount sendAmount recipient selfAddress =>
    plan := {plan with operations := plan.operations ++ [
      sendShieldedOp nonce color inputAmount sendAmount recipient selfAddress]}
  | .relayShieldedImmediate nonce color amount recipient selfAddress =>
    plan := {plan with operations := plan.operations ++ [
      relayShieldedOp nonce color amount recipient selfAddress]}
  | .checkpoint => plan := {plan with operations := plan.operations ++ [.checkpoint]}
  | .mintShielded domain amount =>
    plan := {plan with operations := plan.operations ++ [.mintShielded domain amount]}
  | .mintUnshielded domain amount =>
    plan := {plan with operations := plan.operations ++ [.mintUnshielded domain amount]}
  | .incUnshieldedInputs color amount isUnshielded =>
    plan := {plan with operations := plan.operations ++ [
      .incUnshieldedInputs color amount isUnshielded]}
  | .incUnshieldedOutputs color amount isUnshielded =>
    plan := {plan with operations := plan.operations ++ [
      .incUnshieldedOutputs color amount isUnshielded]}
  | .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient =>
    plan := {plan with operations := plan.operations ++ [
      .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient]}
  | .emitEvent kind payload =>
    plan := {plan with operations := plan.operations ++ [.emitEvent kind payload]}
  | .requireContractCaller address =>
    plan := {plan with
      operations := plan.operations ++ [.requireContractCaller address]
      reads := plan.reads ++ contractCallerReads plan.reads.length}
  | .readCaller destinations =>
    plan := {plan with
      operations := plan.operations ++ [.readCaller destinations]
      reads := plan.reads ++ destinations.types.map (fun (name, ty) => {name, ty})}
  | .readContractAddress destination =>
    plan := {plan with
      operations := plan.operations ++ [.readContractAddress destination]
      reads := plan.reads ++ [{name := destination, ty := .bytes 32}]}
  | .readTokenBalance destination color isUnshielded query =>
    plan := {plan with
      operations := plan.operations ++ [.readTokenBalance destination color isUnshielded query]
      reads := plan.reads ++ [{name := destination, ty := query.resultType}]}
  | .blockTimeCompare destination before deadline =>
    plan := {plan with
      operations := plan.operations ++ [.blockTimeCompare destination before deadline]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .requireAbsent name _ key =>
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let name := s!"_noctium_absence_{plan.reads.length}"
    plan := { plan with
      operations := plan.operations ++ [
        .dup, .index slot, pushKey key, .member, .popeq (.bit false)]
      reads := plan.reads ++ [{name, ty := .bool}]
      guards := plan.guards ++ [.eq (.ref name : Expr .bool) (.bool false)] }
  | .writeCell name ty value =>
    let slot ← stateSlot state name
    let value ← storageWriteValueWithAlignment ty value (stateCellAlignment state name)
    plan := {plan with operations := plan.operations ++ [
      .push (.field (.native slot)), value, .insert 1]}
  | .writeMap name _ ty key value =>
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let value ← storageWriteValue ty value
    plan := {plan with operations := plan.operations ++ [
      .index slot true, pushKey key,
      value, .insert 2]}
  | .readMap name destination _ ty key => do
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let value ← storageReadValue ty destination
    plan := { plan with
      operations := plan.operations ++ [
        .dup, .mapIndex slot key,
        value]
      reads := plan.reads ++ [{name := destination, ty}] }
  | .readMember name destination _ _ key => do
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    plan := { plan with
      operations := plan.operations ++ [
        .dup, .index slot, pushKey key, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}] }
  | .readPath name destination keys ty => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let value ← storageReadValue ty destination
    plan := {plan with
      operations := plan.operations ++ [.dup, .indexPath slot false keys, value]
      reads := plan.reads ++ [{name := destination, ty}]}
  | .counterRead name destination keys => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    let keys ← nativePathKeys keys
    let value : Expr (.uint (2 ^ 64 - 1)) := .ref destination
    plan := {plan with
      operations := plan.operations ++ [.dup, .indexPath slot false keys, .popeq (.counter value)]
      reads := plan.reads ++ [{name := destination, ty := .uint (2 ^ 64 - 1)}]}
  | .counterLessThan name destination keys threshold => do
    plan := {plan with
      operations := plan.operations ++ [← counterLessThanOp state name destination keys threshold]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .listLength name destination keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    let value : Expr (.uint (2 ^ 64 - 1)) := .ref destination
    plan := {plan with
      operations := plan.operations ++ [.listLength slot alignedKeys value]
      reads := plan.reads ++ [{name := destination, ty := .uint (2 ^ 64 - 1)}]}
  | .mapIsEmpty name destination keys => do
    plan := {plan with
      operations := plan.operations ++ [← mapIsEmptyOp state name destination keys]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .mapSize name destination keys => do
    plan := {plan with
      operations := plan.operations ++ [← mapSizeOp state name destination keys]
      reads := plan.reads ++ [{name := destination, ty := .uint (2 ^ 64 - 1)}]}
  | .listHead name destination keys type destinations => do
    let slot ← stateSlot state name
    let (environment, foundType, fields) ← resolveListState state name keys
    unless foundType == type do throw "List head record type mismatch"
    let alignedKeys ← nativePathKeys keys
    let (schema, values, read) ← listHeadParts environment type destination fields destinations
    plan := {plan with
      operations := plan.operations ++ [.listHead slot alignedKeys schema values]
      reads := plan.reads ++ [read]}
  | .listPushFront name keys type values => do
    let slot ← stateSlot state name
    let (environment, foundType, fields) ← resolveListState state name keys
    unless foundType == type do throw "List push record type mismatch"
    unless fields.map Prod.snd == values.map LedgerFieldExpr.ty do
      throw "List push record field type mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← listElementOperationSchema environment type
    plan := {plan with operations := plan.operations ++ [
      .listPushFront slot alignedKeys schema values]}
  | .listPopFront name keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    plan := {plan with operations := plan.operations ++ [.listPopFront slot alignedKeys]}
  | .listReset name keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    plan := {plan with operations := plan.operations ++ [.listReset slot alignedKeys]}
  | .readCompositePath name destination keys type destinations => do
    let slot ← stateSlot state name
    let .composite environment foundType ← resolveTreeState state name keys
      | throw "nested composite read must select a composite value"
    unless foundType == type do throw "nested composite read type mismatch"
    let fields ← if keys.isEmpty then
      LedgerValueType.cellRecordFields environment type
    else LedgerValueType.ledgerRecordFields environment type
    unless fields.map Prod.snd == destinations.map Prod.snd do
      throw "nested composite read destination type mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← if keys.isEmpty then cellRecordSchema environment type
      else recordSchema environment type
    let values := destinations.map fun (name, ty) => refLedgerFieldExpr name ty
    let components := destinations
    plan := {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false alignedKeys, .popeqFields schema values]
      reads := plan.reads ++ [{name := destination, ty := .native, components := components, schema := some schema}]}
  | .memberPath name destination keys => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let (parents, finalKey) ← splitPath keys
    plan := {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false parents, pushKey finalKey, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .memberRecordSet name destination keys values => do
    let (slot, schema) ← recordSetKeySchema state name keys values
    plan := {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false (← nativePathKeys keys), .pushFields schema values false, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .readRecordMap name destination ty values parentKeys => do
    let (slot, schema, foundTy) ← recordMapKeySchema state name values parentKeys
    unless foundTy == ty do throw "record Map value type mismatch"
    let value ← storageReadValue ty destination
    plan := {plan with
      operations := plan.operations ++ [
        .dup, .indexRecordPath slot schema values (← nativePathKeys parentKeys), value]
      reads := plan.reads ++ [{name := destination, ty}]}
  | .readRecordMapComposite name destination valueType values destinations parentKeys => do
    let valueExpressions := destinations.map fun (fieldName, ty) => .mk ty (.ref fieldName)
    let (slot, keySchema, valueSchema, foundType) ←
      recordMapCompositeSchemas state name parentKeys values valueExpressions
    unless foundType == valueType do throw "record Map value type mismatch"
    let read : Read := {name := destination, ty := .native, components := destinations, schema := some valueSchema}
    plan := {plan with
      operations := plan.operations ++ [
        .dup, .indexRecordPath slot keySchema values (← nativePathKeys parentKeys),
        .popeqFields valueSchema valueExpressions],
      reads := plan.reads ++ [read]}
  | .memberRecordMap name destination values parentKeys => do
    let (slot, schema) ← anyRecordMapKeySchema state name values parentKeys
    plan := {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false (← nativePathKeys parentKeys),
        .pushFields schema values false, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .writeRecordMap name values ty value parentKeys => do
    let (slot, schema, foundTy) ← recordMapKeySchema state name values parentKeys
    unless foundTy == ty do throw "record Map value type mismatch"
    let keys ← nativePathKeys parentKeys
    let value ← storageWriteValue ty value
    let levels := keys.length + 2
    if levels >= 16 then throw "nested record Map insertion exceeds native Ins depth"
    plan := {plan with operations := plan.operations ++ [
      .indexPath slot true keys, .pushFields schema values false, value, .insert levels]}
  | .writeRecordMapComposite name valueType keyValues valueValues parentKeys => do
    let (slot, keySchema, valueSchema, foundType) ←
      recordMapCompositeSchemas state name parentKeys keyValues valueValues
    unless foundType == valueType do throw "record Map value type mismatch"
    let keys ← nativePathKeys parentKeys
    let levels := keys.length + 2
    if levels >= 16 then throw "nested record Map insertion exceeds native Ins depth"
    plan := {plan with operations := plan.operations ++ [
      .indexPath slot true keys, .pushFields keySchema keyValues false,
      .pushFields valueSchema valueValues true, .insert levels]}
  | .removeRecordMap name values parentKeys => do
    let (slot, schema) ← anyRecordMapKeySchema state name values parentKeys
    plan := {plan with operations := plan.operations ++ [
      .mapRemoveRecord slot schema (← nativePathKeys parentKeys) values]}
  | .setInsertRecord name keys values => do
    let (slot, schema) ← recordSetKeySchema state name keys values
    plan := {plan with operations := plan.operations ++
      (← recordSetInsertOps slot (← nativePathKeys keys) schema values)}
  | .removeRecordSet name keys values => do
    let (slot, schema) ← recordSetKeySchema state name keys values
    plan := {plan with operations := plan.operations ++ [
      .mapRemoveRecord slot schema (← nativePathKeys keys) values]}
  | .insertPath name keys ty value | .writePath name keys ty value => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let value ← match ty with
      | .foreign _ | .jubjubScalar | .jubjubPoint => storageWriteValue ty value
      | _ => pure (.push (← nativeAligned ty value) true)
    let operations ← pathWriteOps slot keys [value]
    plan := {plan with operations := plan.operations ++ operations}
  | .writeCompositePath name keys type values => do
    let operations ← compositeWritePathOps state name keys type values
    plan := {plan with operations := plan.operations ++ operations}
  | .counterAdjust name keys subtract amount => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    let alignedKeys ← nativePathKeys keys
    let operation := if subtract then Op.subImmediate amount else Op.addImmediate amount
    plan := {plan with operations := plan.operations ++ [
      .indexPath slot true alignedKeys, operation, .insert (keys.length + 1)]}
  | .counterReset name keys => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    if keys.isEmpty then
      let value : Expr (.uint (2 ^ 64 - 1)) := .uint (2 ^ 64 - 1) 0
      plan := {plan with operations := plan.operations ++ [
        .push (.field (.native slot)), .push (.counter value) true, .insert 1]}
    else
      let alignedKeys ← nativePathKeys keys
      let value : Expr (.uint (2 ^ 64 - 1)) := .uint (2 ^ 64 - 1) 0
      let operations ← pathWriteOps slot alignedKeys [.push (.counter value) true]
      plan := {plan with operations := plan.operations ++ operations}
  | .emptyMapPath name keys => do
    plan := {plan with operations := plan.operations ++ (← emptyMapOps state name keys)}
  | .setInsert name keys =>
    plan := {plan with operations := plan.operations ++ (← setInsertOps state name keys)}
  | .removePath name keys => do
    let slot ← stateSlot state name
    let some declaration := state.find? (·.name == name)
      | throw s!"unknown map or set state '{name}'"
    let some schema := declaration.kind.pathSchema
      | throw s!"state '{name}' is not a map or set"
    schema.removalPath keys
    let alignedKeys ← nativePathKeys keys
    plan := {plan with operations := plan.operations ++ [.mapRemove slot alignedKeys]}
  pure plan

private def previousEffectLoop (state : List StateDecl) (effects : List Effect)
    (initial : Plan) : Except String Plan := do
  let mut plan := initial
  for effect in effects do
    plan ← previousEffectStep state effect plan
  pure plan

private theorem previousEffectStep_eq_appendEffect (state : List StateDecl)
    (effect : Effect) (plan : Plan) :
    previousEffectStep state effect plan = appendEffect state effect plan := by
  cases effect <;> simp [previousEffectStep, appendEffect, stateSlot] <;> rfl

/-- Every old loop result and first failure equals the production effect
fold, for arbitrary plans, schemas, and ordered effect lists. -/
theorem previousEffectLoop_eq_appendEffect (state : List StateDecl)
    (effects : List Effect) (initial : Plan) :
    previousEffectLoop state effects initial =
      appendEffects state effects initial := by
  unfold appendEffects
  unfold previousEffectLoop
  simp only [bind_pure]
  change (forIn effects initial (fun effect plan => do
      let result ← previousEffectStep state effect plan
      pure (ForInStep.yield result))) =
    effects.foldlM (fun plan effect => appendEffect state effect plan) initial
  have stepEq (effect : Effect) (plan : Plan) :
      (do let result ← previousEffectStep state effect plan
          pure (ForInStep.yield result)) =
        ForInStep.yield <$> previousEffectStep state effect plan := by
    cases previousEffectStep state effect plan <;> rfl
  simp only [stepEq]
  rw [List.forIn_yield_eq_foldlM]
  simp only [previousEffectStep_eq_appendEffect, Except.map, Functor.map]
  congr 1
  funext plan effect
  cases appendEffect state effect plan <;> rfl

/-- Final production gate for a symbolic native plan. -/
def finishPlan (entry : Entrypoint) (result : Except String Plan) : Except Diagnostic Plan :=
  match result with
  | .ok plan =>
    match plan.validate entry with
    | .ok _ => pure plan
    | .error message => throw {span := entry.span, message}
  | .error message => throw {span := entry.span, message}

/-- Lower a typed entrypoint and return the exclusive operation end after each
source effect. Public-input operations precede the first boundary. -/
def lowerWithEffectBoundaries (state : List StateDecl) (entry : Entrypoint) :
    Except Diagnostic (Plan × List Nat) := do
  entry.validate ledgerCapabilities state
  Disclosure.entrypoint entry
  let result : Except String (Plan × List Nat) := do
    let mut plan : Plan := {}
    let sourceNames := entry.circuit.inputs.map (·.name) ++ entry.circuit.outputs.map (·.name) ++
      entry.effects.flatMap (fun effect => match effect with
        | .readCell _ destination _ | .readMap _ destination .. |
            .readMember _ destination .. | .readPath _ destination .. |
            .memberPath _ destination .. | .counterRead _ destination .. |
            .counterLessThan _ destination .. |
            .mapSize _ destination .. |
            .readContractAddress destination | .readTokenBalance destination .. |
            .mapIsEmpty _ destination .. | .listLength _ destination .. |
            .merkleTreeIsFull _ destination | .merkleTreeCheckRoot _ _ destination |
            .merkleTreeIsFullAt _ _ destination | .merkleTreeCheckRootAt _ _ _ destination => [destination]
        | .readCaller destinations => destinations.types.map Prod.fst
        | .readCompositePath _ _ _ _ destinations => destinations.map Prod.fst
        | .readRecordMapComposite _ destination _ _ destinations _ =>
          destination :: destinations.map Prod.fst
        | .listHead _ _ _ _ destinations => destinations.map Prod.fst
        | _ => [])
    if sourceNames.any (·.startsWith "_noctium_") then
      throw "source names beginning '_noctium_' are reserved by the native transcript producer"
    -- Public parameters must appear among Popeq reads consumed by public_input.
    plan ← publicInputPlan entry.circuit.inputs plan
    appendEffectsGuardedWithBoundaries state entry.effects entry.effectGuards plan
  let (plan, boundaries) ← result.mapError fun message => {span := entry.span, message}
  pure ((← finishPlan entry (.ok plan)), boundaries)

private theorem exceptMapErrorOk {α ε δ : Type} (mapError : ε → δ)
    (source : Except ε α) (value : α) :
    source.mapError mapError = .ok value ↔ source = .ok value := by
  cases source <;> simp [Except.mapError]

theorem lowerWithEffectBoundaries_inputPrefix (state : List StateDecl)
    (entry : Entrypoint) (plan : Plan) (boundaries : List Nat)
    (accepted : lowerWithEffectBoundaries state entry = .ok (plan, boundaries)) :
    ∃ inputPlan,
      publicInputPlan entry.circuit.inputs {} = .ok inputPlan ∧
      appendEffectsGuardedWithBoundaries state entry.effects entry.effectGuards inputPlan =
        .ok (plan, boundaries) := by
  unfold lowerWithEffectBoundaries at accepted
  simp only [exceptBindOk] at accepted
  rcases accepted with ⟨_, _, ⟨_, _, ⟨result, resultAccepted,
    ⟨finished, finishAccepted, outputAccepted⟩⟩⟩⟩
  rcases result with ⟨rawPlan, rawBoundaries⟩
  have outputPair : (finished, rawBoundaries) = (plan, boundaries) := by
    change Except.ok (finished, rawBoundaries) = Except.ok (plan, boundaries) at outputAccepted
    exact (Except.ok.inj outputAccepted)
  rcases Prod.mk.inj outputPair with ⟨finishedEq, boundariesEq⟩
  have finishIdentity : finished = rawPlan := by
    cases validation : rawPlan.validate entry with
    | error message =>
      simp [finishPlan, validation] at finishAccepted
    | ok valid =>
      simp [finishPlan, validation] at finishAccepted
      have pureResult : (pure rawPlan : Except Diagnostic Plan) = .ok rawPlan := rfl
      rw [pureResult] at finishAccepted
      exact (Except.ok.inj finishAccepted).symm
  have rawPlanEq : rawPlan = plan := finishIdentity.symm.trans finishedEq
  simp only [exceptMapErrorOk] at resultAccepted
  split at resultAccepted
  · change (Except.error
      "source names beginning '_noctium_' are reserved by the native transcript producer" :
        Except String (Plan × List Nat)) = Except.ok (rawPlan, rawBoundaries) at resultAccepted
    cases resultAccepted
  · simp only [exceptBindOk] at resultAccepted
    rcases resultAccepted with ⟨inputPlan, inputAccepted, effectsAccepted⟩
    rw [rawPlanEq, boundariesEq] at effectsAccepted
    exact ⟨inputPlan, inputAccepted, effectsAccepted⟩

/-- Lower a typed entrypoint to a symbolic native VM program. The state layout
is a root array with one slot per declaration. Cells, including booleans, use
Native field alignment. Membership results use the VM's byte-aligned boolean.
The plan is not deployable until its fields are bound by the relation producer. -/
def lower (state : List StateDecl) (entry : Entrypoint) : Except Diagnostic Plan :=
  (lowerWithEffectBoundaries state entry).map Prod.fst

/-- JSON value atoms must be hydrated into Uint8Array by the ledger JS adapter. -/
def Aligned.toJson (ctx : EvalContext) (env : EvalEnv) (value : Aligned) : Except String Lean.Json := do
  let (atoms, alignment) ← match value with
    | .field expression => do
      pure (Lean.toJson [natBytes (← expression.eval ctx env)],
        Lean.Json.mkObj [("tag", Lean.toJson ("field" : String))])
    | .foreignKey kind expression => do
      let atoms ← keyValueJson kind expression ctx env
      pure (atoms, Lean.Json.mkObj [("tag", Lean.toJson ("field" : String))])
    | .bit b => pure (Lean.toJson [natBytes (if b then 1 else 0)],
        Lean.Json.mkObj [("tag", Lean.toJson ("bytes" : String)), ("length", Lean.toJson (1 : Nat))])
    | .bitExpr expression => pure (Lean.toJson [natBytes (if ← expression.eval ctx env then 1 else 0)],
        Lean.Json.mkObj [("tag", Lean.toJson ("bytes" : String)), ("length", Lean.toJson (1 : Nat))])
    | .bytes32 expression => do
      let values ← expression.eval ctx env
      pure (Lean.Json.arr #[Lean.Json.arr (values.toArray.map Lean.toJson)],
        Lean.Json.mkObj [("tag", Lean.toJson ("bytes" : String)),
          ("length", Lean.toJson (32 : Nat))])
    | .bytes length expression => do
      let values ← expression.eval ctx env
      pure (Lean.Json.arr #[Lean.Json.arr (values.toArray.map Lean.toJson)],
        Lean.Json.mkObj [("tag", Lean.toJson ("bytes" : String)),
          ("length", Lean.toJson length)])
    | .compress expression => do
      let values ← expression.eval ctx env
      pure (Lean.Json.arr #[Lean.Json.arr (values.toArray.map Lean.toJson)],
        Lean.Json.mkObj [("tag", Lean.toJson ("compress" : String))])
    | .compressString expression => do
      let text ← expression.eval ctx env
      let bytes := text.toUTF8.data.toList.map UInt8.toNat
      unless bytes.length ≤ maxOpaqueStringBytes && (bytes.isEmpty || bytes.getLast! != 0) do
        throw "opaque string is not in canonical UTF-8 Compress form"
      pure (Lean.Json.arr #[Lean.Json.arr (bytes.toArray.map Lean.toJson)],
        Lean.Json.mkObj [("tag", Lean.toJson ("compress" : String))])
    | .nativeFields _ => throw "grouped Native fields serialize through pushFields/popeqFields"
    | .counter expression => do
      let value ← expression.eval ctx env
      pure (Lean.toJson [natBytes value], Lean.Json.mkObj [
        ("tag", Lean.toJson ("bytes" : String)), ("length", Lean.toJson (8 : Nat))])
    | .u128 expression => do
      let value ← expression.eval ctx env
      pure (Lean.toJson [natBytes value], Lean.Json.mkObj [
        ("tag", Lean.toJson ("bytes" : String)),
          ("length", Lean.toJson (16 : Nat))])
  let alignmentSegments := match value with
    | .foreignKey kind _ => Lean.Json.arr (Array.replicate kind.encodedFieldCount
        (Lean.Json.mkObj [("tag", Lean.toJson ("atom" : String)), ("value", alignment)]))
    | _ => Lean.Json.arr #[Lean.Json.mkObj [
        ("tag", Lean.toJson ("atom" : String)), ("value", alignment)]]
  pure (Lean.Json.mkObj [("value", atoms), ("alignment", alignmentSegments)])

def Op.toJson (ctx : EvalContext) (env : EvalEnv) : Op → Except String Lean.Json
  | .dup => pure (Lean.Json.mkObj [("dup", Lean.Json.mkObj [("n", Lean.toJson (0 : Nat))])])
  | .index slot pushPath => do
    let value ← (Aligned.field (.native slot)).toJson ctx env
    pure (Lean.Json.mkObj [("idx", Lean.Json.mkObj [
      ("cached", Lean.toJson false), ("pushPath", Lean.toJson pushPath),
      ("path", Lean.Json.arr #[Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", value)]])])])
  | .mapIndex slot key => do
    let slotValue ← (Aligned.field (.native slot)).toJson ctx env
    let keyValue ← key.toJson ctx env
    pure (Lean.Json.mkObj [("idx", Lean.Json.mkObj [
      ("cached", Lean.toJson false), ("pushPath", Lean.toJson false),
      ("path", Lean.Json.arr #[
        Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", slotValue)],
        Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", keyValue)]])])])
  | .indexRecordPath slot schema expressions keys => do
    let values ← (expressions.flatMap ledgerFieldPayloads).mapM (fun value => value.eval ctx env)
    let keyValues ← keys.mapM fun key => key.toJson ctx env
    let keyParts := keyValues.map fun value =>
      Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", value)]
    pure (Lean.Json.mkObj [("indexRecordPath", Lean.Json.mkObj (
      [("slot", Lean.toJson slot), ("schema", schema), ("values", Lean.toJson values)] ++
      (if keyParts.isEmpty then [] else [("keys", Lean.Json.arr keyParts.toArray)])))])
  | .indexPath slot pushPath keys => do
    let slotValue ← (Aligned.field (.native slot)).toJson ctx env
    let keyValues ← keys.mapM fun key => key.toJson ctx env
    let path := (slotValue :: keyValues).map fun value =>
      Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", value)]
    pure (Lean.Json.mkObj [("idx", Lean.Json.mkObj [
      ("cached", Lean.toJson false), ("pushPath", Lean.toJson pushPath),
      ("path", Lean.Json.arr path.toArray)])])
  | .push value storage => do
    pure (Lean.Json.mkObj [("push", Lean.Json.mkObj [("storage", Lean.toJson storage),
      ("value", Lean.Json.mkObj [("tag", Lean.toJson ("cell" : String)),
        ("content", ← value.toJson ctx env)])])])
  | .newMap => pure (Lean.Json.mkObj [("new", Lean.Json.mkObj [])])
  | .popeq value => do
    pure (Lean.Json.mkObj [("popeq", Lean.Json.mkObj [("cached", Lean.toJson false),
      ("result", ← value.toJson ctx env)])])
  | .pushFields schema values storage => do
    let values ← (values.flatMap ledgerFieldPayloads).mapM (fun value => value.eval ctx env)
    pure (Lean.Json.mkObj [("pushFields", Lean.Json.mkObj [
      ("schema", schema), ("storage", Lean.toJson storage), ("values", Lean.toJson values)])])
  | .popeqFields schema values => do
    let values ← (values.flatMap ledgerFieldPayloads).mapM (fun value => value.eval ctx env)
    pure (Lean.Json.mkObj [("popeqFields", Lean.Json.mkObj [
      ("schema", schema), ("values", Lean.toJson values)])])
  | .member => pure (Lean.toJson ("member" : String))
  | .insert levels => pure (Lean.Json.mkObj [("ins", Lean.Json.mkObj [
      ("cached", Lean.toJson false), ("n", Lean.toJson levels)])])
  | .addImmediate amount => do
    pure (Lean.Json.mkObj [("addi", Lean.Json.mkObj [
      ("immediate", Lean.toJson (← amount.eval ctx env))])])
  | .subImmediate amount => do
    pure (Lean.Json.mkObj [("subi", Lean.Json.mkObj [
      ("immediate", Lean.toJson (← amount.eval ctx env))])])
  | .listLength slot keys value => do
    pure (Lean.Json.mkObj [("listLength", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length),
      ("value", Lean.toJson (← value.eval ctx env))])])
  | .mapSize .. => throw "mapSize uses its dedicated native-plan operation JSON"
  | .mapIsEmpty .. => throw "mapIsEmpty uses its dedicated native-plan operation JSON"
  | .counterLessThan .. => throw "counterLessThan uses its dedicated native-plan operation JSON"
  | .merkleTreeIsFull .. | .merkleTreeIsFullAt .. =>
    throw "merkleTreeIsFull uses its dedicated native-plan operation JSON"
  | .merkleTreeCheckRoot .. | .historicMerkleTreeCheckRoot .. | .merkleTreeCheckRootAt .. =>
    throw "merkleTreeCheckRoot uses its dedicated native-plan operation JSON"
  | .merkleTreeInsertHash .. | .historicMerkleTreeInsertHash .. | .merkleTreeInsertHashAt .. =>
    throw "merkleTreeInsertHash uses its dedicated native-plan operation JSON"
  | .merkleTreeInsertHashIndex .. | .historicMerkleTreeInsertHashIndex .. | .merkleTreeInsertHashIndexAt .. =>
    throw "merkleTreeInsertHashIndex uses its dedicated native-plan operation JSON"
  | .merkleTreeReset .. | .historicMerkleTreeReset .. | .merkleTreeResetAt .. =>
    throw "merkleTreeReset uses its dedicated native-plan operation JSON"
  | .merkleTreeResetHistory .. | .merkleTreeResetHistoryAt .. =>
    throw "merkleTreeResetHistory uses its dedicated native-plan operation JSON"
  | .listHead slot keys schema values => do
    let values ← (values.flatMap ledgerFieldPayloads).mapM (fun value => value.eval ctx env)
    pure (Lean.Json.mkObj [("listHead", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length),
      ("schema", schema), ("values", Lean.toJson values)])])
  | .listPushFront slot keys schema values => do
    let values ← (values.flatMap ledgerFieldPayloads).mapM (fun value => value.eval ctx env)
    pure (Lean.Json.mkObj [("listPushFront", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length),
      ("schema", schema), ("values", Lean.toJson values)])])
  | .listPopFront slot keys => pure (Lean.Json.mkObj [("listPopFront", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length)])])
  | .listReset slot keys => pure (Lean.Json.mkObj [("listReset", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length)])])
  | .mapRemove slot keys => pure (Lean.Json.mkObj [("mapRemove", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length)])])
  | .mapRemoveRecord slot schema keys values => do
      let values ← (values.flatMap ledgerFieldPayloads).mapM (fun value => value.eval ctx env)
      let keys ← keys.mapM (fun key => key.toJson ctx env)
      pure (Lean.Json.mkObj [("mapRemoveRecord", Lean.Json.mkObj (
        [("slot", Lean.toJson slot), ("schema", schema)] ++
        (if keys.isEmpty then [] else [("keys", Lean.Json.arr keys.toArray)]) ++
        [("values", Lean.toJson values)]))])
  | .claimContractCall .. => throw "claimContractCall uses its dedicated native-plan operation JSON"
  | .claimShielded .. => throw "claimShielded uses its dedicated native-plan operation JSON"
  | .receiveShieldedToMap .. => throw "shielded coin receive uses its dedicated native-plan operation JSON"
  | .insertShieldedCoinMap .. => throw "qualified shielded coin Map insertion uses its dedicated native-plan operation JSON"
  | .insertShieldedCoinSet .. => throw "qualified shielded coin Set insertion uses its dedicated native-plan operation JSON"
  | .insertShieldedCoinSetTo .. => throw "qualified shielded coin Set recipient insertion uses its dedicated native-plan operation JSON"
  | .writeShieldedCoinCell .. => throw "shielded coin Cell write uses its dedicated native-plan operation JSON"
  | .writeShieldedCoinCellTo .. => throw "shielded coin Cell recipient write uses its dedicated native-plan operation JSON"
  | .listPushFrontCoin .. => throw "qualified shielded coin List push uses its dedicated native-plan operation JSON"
  | .listPushFrontCoinTo .. => throw "qualified shielded coin List recipient push uses its dedicated native-plan operation JSON"
  | .spendShieldedFromMap .. => throw "shielded coin spend uses its dedicated native-plan operation JSON"
  | .mergeShieldedFromMap .. => throw "shielded coin merge uses its dedicated native-plan operation JSON"
  | .sendShieldedFromMap .. => throw "shielded coin send uses its dedicated native-plan operation JSON"
  | .relayShieldedImmediate .. => throw "shielded coin relay uses its dedicated native-plan operation JSON"
  | .mintShielded .. => throw "shielded mint uses its dedicated native-plan operation JSON"
  | .mintUnshielded .. => throw "unshielded mint uses its dedicated native-plan operation JSON"
  | .incUnshieldedInputs .. => throw "unshielded input accumulation uses its dedicated native-plan operation JSON"
  | .incUnshieldedOutputs .. => throw "unshielded output accumulation uses its dedicated native-plan operation JSON"
  | .claimUnshieldedCoinSpend .. => throw "unshielded spend claim uses its dedicated native-plan operation JSON"
  | .requireContractCaller .. => throw "requireContractCaller uses its dedicated native-plan operation JSON"
  | .checkpoint => pure (Lean.toJson ("ckpt" : String))
  | .readCaller .. => throw "caller read uses its dedicated native-plan operation JSON"
  | .readContractAddress .. => throw "contract address read uses its dedicated native-plan operation JSON"
  | .readTokenBalance .. => throw "readTokenBalance uses its dedicated native-plan operation JSON"
  | .blockTimeCompare .. => throw "block-time comparison uses its dedicated native-plan operation JSON"
  | .emitEvent .. => throw "emitEvent uses its dedicated native-plan operation JSON"

def Plan.toJson (ctx : EvalContext) (env : EvalEnv) (plan : Plan) : Except String Lean.Json := do
  pure (Lean.Json.arr (← plan.operations.mapM (Op.toJson ctx env)).toArray)

end Noctium.Backend.Impact
