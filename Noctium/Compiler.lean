import Noctium.NativeExpression
import Noctium.Frontend
import Noctium.Backend.Zkir
import Noctium.EntryPointHash
import Noctium.Target
import Noctium.ArtifactRole
import Noctium.RustBinding
import Noctium.Types.ValueSchema

namespace Noctium.Compiler
open Lean Elab Command

private def sourceCapabilities : Capabilities := Capabilities.source

private abbrev typeName : Ty → String := _root_.Noctium.NativeExpression.typeName
private abbrev foreignConstantJson := _root_.Noctium.NativeExpression.foreignConstantJson

private def expressionJson : Expr ty → Json
  | .native n => Json.mkObj [("native", toJson (toString n))]
  | .bool b => Json.mkObj [("bool", toJson b)]
  | .uint maximum value => Json.mkObj [("uint", Json.mkObj [
      ("maximum", toJson (toString maximum)), ("value", toJson (toString value))])]
  | .bytesField value index => Json.mkObj [("bytesField", Json.mkObj [
      ("value", expressionJson value), ("index", toJson index)])]
  | .opaqueBytesProjection value => expressionJson value
  | .bytesAt value index => Json.mkObj [("byteAt", Json.mkObj [
      ("value", expressionJson value), ("index", toJson index)])]
  | .bytesLiteral length values => Json.mkObj [("tag", toJson ("bytesLiteral" : String)),
      ("length", toJson length), ("values", toJson values)]
  | .reverseBytes (length := length) value => Json.mkObj [
      ("tag", toJson ("reverseBytes" : String)), ("length", toJson length),
      ("value", expressionJson value)]
  | .sliceBytes (length := length) value start stop => Json.mkObj [
      ("tag", toJson ("sliceBytes" : String)), ("length", toJson length),
      ("value", expressionJson value), ("start", toJson start), ("end", toJson stop)]
  | .concatBytes (leftLength := leftLength) (rightLength := rightLength) left right =>
      Json.mkObj [("tag", toJson ("concatBytes" : String)),
        ("leftLength", toJson leftLength), ("rightLength", toJson rightLength),
        ("left", expressionJson left), ("right", expressionJson right)]
  | .sha256 (length := length) value => Json.mkObj [
      ("tag", toJson ("sha256" : String)), ("length", toJson length),
      ("value", expressionJson value)]
  | .sha512 (length := length) value => Json.mkObj [
      ("tag", toJson ("sha512" : String)), ("length", toJson length),
      ("value", expressionJson value)]
  | .keccak256 (length := length) value => Json.mkObj [
      ("tag", toJson ("keccak256" : String)), ("length", toJson length),
      ("value", expressionJson value)]
  | .keccak256Secp256k1Point value => Json.mkObj [
      ("tag", toJson ("keccak256Secp256k1Point" : String)),
      ("value", expressionJson value)]
  | .reverseBytes32 value => Json.mkObj [("tag", toJson ("reverseBytes32" : String)),
      ("value", expressionJson value)]
  | .persistentHash32 value => Json.mkObj [("tag", toJson ("persistentHash32" : String)),
      ("value", expressionJson value)]
  | .bytes32Literal values => Json.mkObj [("tag", toJson ("bytes32Literal" : String)),
      ("values", toJson values)]
  | .persistentHashVector32 values => Json.mkObj [("tag", toJson ("persistentHashVector32" : String)),
      ("values", toJson (values.map expressionJson))]
  | .persistentHashNative value => Json.mkObj [("tag", toJson ("persistentHashNative" : String)),
      ("value", expressionJson value)]
  | .persistentHashNativeVector values => Json.mkObj [("tag", toJson ("persistentHashNativeVector" : String)),
      ("values", toJson (values.map expressionJson))]
  | .transientHash values => Json.mkObj [("tag", toJson ("transientHash" : String)),
      ("values", toJson (values.map expressionJson))]
  | .toBytes32 value => Json.mkObj [("tag", toJson ("toBytes32" : String)),
      ("value", expressionJson value)]
  | .fromBytes32 (target := target) value => Json.mkObj [("tag", toJson ("fromBytes32" : String)),
      ("type", toJson (typeName target)), ("value", expressionJson value)]
  | .fromBytes (target := target) (length := length) value => Json.mkObj [
      ("tag", toJson ("fromBytes" : String)), ("type", toJson (typeName target)),
      ("length", toJson length), ("value", expressionJson value)]
  | .jubjubScalarFromNative value => Json.mkObj [("tag", toJson ("jubjubScalarFromNative" : String)),
      ("value", expressionJson value)]
  | .jubjubScalarToNative value => Json.mkObj [("tag", toJson ("jubjubScalarToNative" : String)),
      ("value", expressionJson value)]
  | .jubjubMulGenerator scalar => Json.mkObj [("tag", toJson ("jubjubMulGenerator" : String)),
      ("scalar", expressionJson scalar)]
  | .jubjubMul point scalar => Json.mkObj [("tag", toJson ("jubjubMul" : String)),
      ("point", expressionJson point), ("scalar", expressionJson scalar)]
  | .jubjubAdd left right => Json.mkObj [("tag", toJson ("jubjubAdd" : String)),
      ("left", expressionJson left), ("right", expressionJson right)]
  | .jubjubNeg point => Json.mkObj [("tag", toJson ("jubjubNeg" : String)),
      ("point", expressionJson point)]
  | .jubjubCoordinate point index => Json.mkObj [("tag", toJson ("jubjubCoordinate" : String)),
      ("point", expressionJson point), ("index", toJson index)]
  | .jubjubFromCoordinates x y => Json.mkObj [("tag", toJson ("jubjubFromCoordinates" : String)),
      ("x", expressionJson x), ("y", expressionJson y)]
  | .hashToCurve values => Json.mkObj [("tag", toJson ("hashToCurve" : String)),
      ("values", toJson (values.map expressionJson))]
  | .foreignBase curve value => foreignConstantJson (.base curve) value
  | .foreignScalar curve value => foreignConstantJson (.scalar curve) value
  | .foreignPoint curve value => foreignConstantJson (.point curve) value
  | .foreignEncodedField (kind := kind) value index => Json.mkObj [
      ("tag", toJson ("foreignEncodedField" : String)),
      ("value", expressionJson value), ("index", toJson index)]
  | .foreignUnary operation value => Json.mkObj [
      ("tag", toJson ("foreignUnary" : String)),
      ("operation", toJson operation.name), ("value", expressionJson value)]
  | .foreignBinary operation left right => Json.mkObj [
      ("tag", toJson ("foreignBinary" : String)),
      ("operation", toJson operation.name),
      ("left", expressionJson left), ("right", expressionJson right)]
  | .foreignToBytes value => Json.mkObj [
      ("tag", toJson ("foreignToBytes" : String)), ("value", expressionJson value)]
  | .foreignFromBytes (kind := kind) (length := length) value => Json.mkObj [
      ("tag", toJson ("foreignFromBytes" : String)),
      ("type", toJson kind.sourceName), ("length", toJson length),
      ("value", expressionJson value)]
  | .boolAnd left right => Json.mkObj [("tag", toJson ("boolAnd" : String)),
      ("left", expressionJson left), ("right", expressionJson right)]
  | .boolOr left right => Json.mkObj [("tag", toJson ("boolOr" : String)),
      ("left", expressionJson left), ("right", expressionJson right)]
  | .boolXor left right => Json.mkObj [("tag", toJson ("boolXor" : String)),
      ("left", expressionJson left), ("right", expressionJson right)]
  | .ref name => Json.mkObj [("ref", toJson name)]
  | .add a b => Json.mkObj [("add", toJson [expressionJson a, expressionJson b])]
  | .mul a b => Json.mkObj [("mul", toJson [expressionJson a, expressionJson b])]
  | .sub a b => Json.mkObj [("sub", toJson [expressionJson a, expressionJson b])]
  | .uadd a b => Json.mkObj [("uadd", toJson [expressionJson a, expressionJson b])]
  | .usub a b => Json.mkObj [("usub", toJson [expressionJson a, expressionJson b])]
  | .umul a b => Json.mkObj [("umul", toJson [expressionJson a, expressionJson b])]
  | .inv value => Json.mkObj [("tag", toJson ("inv" : String)), ("value", expressionJson value)]
  | .cast target value => Json.mkObj [("cast", Json.mkObj [
      ("type", toJson (typeName target)), ("value", expressionJson value)])]
  | .letE name value body => Json.mkObj [("let", Json.mkObj [
      ("name", toJson name), ("value", expressionJson value), ("body", expressionJson body)])]
  | .assertE condition body => Json.mkObj [("assertThen", toJson [expressionJson condition, expressionJson body])]
  | .copyValue value | .disclose _ value => expressionJson value
  | .eq a b => Json.mkObj [("eq", toJson [expressionJson a, expressionJson b])]
  | .select c a b => Json.mkObj [("select", toJson [expressionJson c, expressionJson a, expressionJson b])]
  | .poseidon2 domain a b => Json.mkObj [("poseidon2", Json.mkObj [
      ("domain", toJson (toString domain)), ("args", toJson [expressionJson a, expressionJson b])])]

private abbrev nativeExpressionJson {ty : Ty} : Expr ty → Json :=
  _root_.Noctium.NativeExpression.toJson

private def nativeImmediateAmountJson
    (amount : Expr (.uint (2 ^ 32 - 1))) : Json :=
  match amount with
  | .uint _ value => toJson value
  | _ => nativeExpressionJson amount

private def sourceImmediateAmountJson
    (amount : Expr (.uint (2 ^ 32 - 1))) : Json :=
  match amount with
  | .uint _ value => toJson value
  | _ => expressionJson amount

private def alignedJson (value : Backend.Impact.Aligned) : List (String × Json) :=
  match value with
  | .field expression => [("alignment", toJson ("field" : String)), ("expression", nativeExpressionJson expression)]
  | .foreignKey _ expression => [("alignment", toJson ("field" : String)), ("expression", nativeExpressionJson expression)]
  | .bit b => [("alignment", toJson ("bit" : String)), ("expression", nativeExpressionJson (.bool b))]
  | .bitExpr expression => [("alignment", toJson ("bit" : String)), ("expression", nativeExpressionJson expression)]
  | .bytes32 expression => [("alignment", toJson ("bytes32" : String)), ("expression", nativeExpressionJson expression)]
  | .bytes length expression => [("alignment", toJson (s!"bytes:{length}")), ("expression", nativeExpressionJson expression)]
  | .compress expression => [("alignment", toJson ("compress" : String)),
      ("expression", nativeExpressionJson expression)]
  | .nativeFields expressions => [("alignment", toJson ("nativeFields" : String)),
      ("expressions", toJson (expressions.map nativeExpressionJson))]
  | .counter expression => [("alignment", toJson ("u64" : String)),
      ("expression", nativeExpressionJson expression)]

private def alignedExpressionJson (value : Backend.Impact.Aligned) : Json :=
  match value with
  | .field expression => nativeExpressionJson expression
  | .foreignKey _ expression => nativeExpressionJson expression
  | .bit value => nativeExpressionJson (.bool value)
  | .bitExpr expression => nativeExpressionJson expression
  | .bytes32 expression => nativeExpressionJson expression
  | .bytes _ expression => nativeExpressionJson expression
  | .compress expression => nativeExpressionJson expression
  | .nativeFields expressions => toJson (expressions.map nativeExpressionJson)
  | .counter expression => nativeExpressionJson expression

private def ledgerFieldExprJson (value : LedgerFieldExpr) : Json :=
  match value with
  | .mk _ expression => nativeExpressionJson expression

private def sourceLedgerFieldExprJson (value : LedgerFieldExpr) : Json :=
  match value with
  | .mk _ expression => expressionJson expression

private def operationJsonBare : Backend.Impact.Op → Json
  | .dup => Json.mkObj [("op", toJson ("dup" : String))]
  | .index slot pushPath => Json.mkObj [("op", toJson ("index" : String)),
      ("slot", toJson slot), ("pushPath", toJson pushPath)]
  | .mapIndex slot key => Json.mkObj [("op", toJson ("index" : String)),
      ("slot", toJson slot), ("pushPath", toJson Bool.false),
      ("key", alignedExpressionJson key)]
  | .indexPath slot pushPath keys => Json.mkObj [
      ("op", toJson ("indexPath" : String)), ("slot", toJson slot),
      ("pushPath", toJson pushPath),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .push value storage => Json.mkObj ([("op", toJson ("push" : String)), ("storage", toJson storage)] ++ alignedJson value)
  | .newMap => Json.mkObj [("op", toJson ("new" : String))]
  | .popeq value => Json.mkObj ([("op", toJson ("popeq" : String))] ++ alignedJson value)
  | .pushFields schema expressions storage => Json.mkObj [
      ("op", toJson ("pushFields" : String)), ("storage", toJson storage),
      ("expressions", toJson (expressions.map ledgerFieldExprJson)), ("schema", schema)]
  | .popeqFields schema expressions => Json.mkObj [
      ("op", toJson ("popeqFields" : String)),
      ("expressions", toJson (expressions.map ledgerFieldExprJson)), ("schema", schema)]
  | .member => Json.mkObj [("op", toJson ("member" : String))]
  | .insert n => Json.mkObj [("op", toJson ("insert" : String)), ("n", toJson n)]
  | .addImmediate amount => Json.mkObj [("op", toJson ("addImmediate" : String)),
      ("amount", nativeImmediateAmountJson amount)]
  | .subImmediate amount => Json.mkObj [("op", toJson ("subImmediate" : String)),
      ("amount", nativeImmediateAmountJson amount)]
  | .listLength slot keys expression => Json.mkObj [
      ("op", toJson ("listLength" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key))),
      ("expression", nativeExpressionJson expression)]
  | .mapSize slot keys expression => Json.mkObj [
      ("op", toJson ("mapSize" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key))),
      ("expression", nativeExpressionJson expression)]
  | .mapIsEmpty slot keys destination => Json.mkObj [
      ("op", toJson ("mapIsEmpty" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key))),
      ("destination", toJson destination)]
  | .counterLessThan slot keys threshold destination => Json.mkObj [
      ("op", toJson ("counterLessThan" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key))),
      ("threshold", nativeExpressionJson threshold), ("destination", toJson destination)]
  | .listHead slot keys schema expressions => Json.mkObj [
      ("op", toJson ("listHead" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key))),
      ("schema", schema), ("expressions", toJson (expressions.map ledgerFieldExprJson))]
  | .listPushFront slot keys schema expressions => Json.mkObj [
      ("op", toJson ("listPushFront" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key))),
      ("schema", schema), ("expressions", toJson (expressions.map ledgerFieldExprJson))]
  | .listPopFront slot keys => Json.mkObj [
      ("op", toJson ("listPopFront" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .listReset slot keys => Json.mkObj [
      ("op", toJson ("listReset" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .merkleTreeIsFull slot depth destination => Json.mkObj [
      ("op", toJson ("merkleTreeIsFull" : String)), ("slot", toJson slot),
      ("depth", toJson depth), ("destination", toJson destination)]
  | .merkleTreeIsFullAt slot depth keys destination => Json.mkObj [
      ("op", toJson ("merkleTreeIsFull" : String)), ("slot", toJson slot),
      ("depth", toJson depth), ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .merkleTreeCheckRoot slot depth expected destination
  | .historicMerkleTreeCheckRoot slot depth expected destination => Json.mkObj [
      ("op", toJson ("merkleTreeCheckRoot" : String)), ("slot", toJson slot),
      ("depth", toJson depth), ("expected", nativeExpressionJson expected),
      ("destination", toJson destination)]
  | .merkleTreeCheckRootAt slot depth _ keys expected destination => Json.mkObj [
      ("op", toJson ("merkleTreeCheckRoot" : String)), ("slot", toJson slot),
      ("depth", toJson depth), ("expected", nativeExpressionJson expected),
      ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .merkleTreeInsertHash slot depth hash
  | .historicMerkleTreeInsertHash slot depth hash => Json.mkObj [
      ("op", toJson ("merkleTreeInsertHash" : String)), ("slot", toJson slot),
      ("depth", toJson depth), ("hash", nativeExpressionJson hash)]
  | .merkleTreeInsertHashAt slot depth _ keys hash => Json.mkObj [
      ("op", toJson ("merkleTreeInsertHash" : String)), ("slot", toJson slot),
      ("depth", toJson depth), ("hash", nativeExpressionJson hash),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .merkleTreeInsertHashIndex slot depth hash idx
  | .historicMerkleTreeInsertHashIndex slot depth hash idx => Json.mkObj [
      ("op", toJson ("merkleTreeInsertHashIndex" : String)), ("slot", toJson slot),
      ("depth", toJson depth), ("hash", nativeExpressionJson hash),
      ("index", nativeExpressionJson idx)]
  | .merkleTreeInsertHashIndexAt slot depth _ keys hash index => Json.mkObj [
      ("op", toJson ("merkleTreeInsertHashIndex" : String)), ("slot", toJson slot),
      ("depth", toJson depth), ("hash", nativeExpressionJson hash),
      ("index", nativeExpressionJson index),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .merkleTreeReset slot depth
  | .historicMerkleTreeReset slot depth => Json.mkObj [
      ("op", toJson ("merkleTreeReset" : String)), ("slot", toJson slot),
      ("depth", toJson depth)]
  | .merkleTreeResetAt slot depth _ keys emptyHistory => Json.mkObj ([
      ("op", toJson ("merkleTreeReset" : String)), ("slot", toJson slot),
      ("depth", toJson depth),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))] ++
        (if emptyHistory then [("emptyHistory", toJson Bool.true)] else []))
  | .merkleTreeResetHistory slot depth => Json.mkObj [
      ("op", toJson ("merkleTreeResetHistory" : String)), ("slot", toJson slot),
      ("depth", toJson depth)]
  | .merkleTreeResetHistoryAt slot depth keys => Json.mkObj [
      ("op", toJson ("merkleTreeResetHistory" : String)), ("slot", toJson slot),
      ("depth", toJson depth),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .mapRemove slot keys => Json.mkObj [
      ("op", toJson ("mapRemove" : String)), ("slot", toJson slot),
      ("keys", toJson (keys.map fun key => Json.mkObj (alignedJson key)))]
  | .claimContractCall address entryPointHash commitment => Json.mkObj [
      ("op", toJson ("claimcontractcall" : String)),
      ("address", nativeExpressionJson address),
      ("entryPointHash", nativeExpressionJson entryPointHash),
      ("commitment", nativeExpressionJson commitment)]
  | .receiveShieldedToMap slot nonce color amount commitment => Json.mkObj [
      ("op", toJson ("receiveShieldedToMap" : String)), ("slot", toJson slot),
      ("nonce", nativeExpressionJson nonce), ("color", nativeExpressionJson color),
      ("amount", nativeExpressionJson amount),
      ("commitment", nativeExpressionJson commitment)]
  | .insertShieldedCoinSet slot nonce color amount commitment => Json.mkObj [
      ("op", toJson ("insertShieldedCoinSet" : String)), ("slot", toJson slot),
      ("nonce", nativeExpressionJson nonce), ("color", nativeExpressionJson color),
      ("amount", nativeExpressionJson amount),
      ("commitment", nativeExpressionJson commitment)]
  | .writeShieldedCoinCell slot nonce color amount commitment => Json.mkObj [
      ("op", toJson ("writeShieldedCoinCell" : String)), ("slot", toJson slot),
      ("nonce", nativeExpressionJson nonce), ("color", nativeExpressionJson color),
      ("amount", nativeExpressionJson amount),
      ("commitment", nativeExpressionJson commitment)]
  | .spendShieldedFromMap nonce color amount recipient nullifier outputCommitment => Json.mkObj [
      ("op", toJson ("spendShieldedFromMap" : String)),
      ("nonce", nativeExpressionJson nonce), ("color", nativeExpressionJson color),
      ("amount", nativeExpressionJson amount), ("recipient", nativeExpressionJson recipient),
      ("nullifier", nativeExpressionJson nullifier),
      ("outputCommitment", nativeExpressionJson outputCommitment)]
  | .sendShieldedFromMap nonce color inputAmount sendAmount recipient nullifier
      outputCommitment changeCommitment => Json.mkObj [
      ("op", toJson ("sendShieldedFromMap" : String)),
      ("nonce", nativeExpressionJson nonce), ("color", nativeExpressionJson color),
      ("inputAmount", nativeExpressionJson inputAmount),
      ("sendAmount", nativeExpressionJson sendAmount),
      ("recipient", nativeExpressionJson recipient),
      ("nullifier", nativeExpressionJson nullifier),
      ("outputCommitment", nativeExpressionJson outputCommitment),
      ("changeCommitment", nativeExpressionJson changeCommitment)]
  | .relayShieldedImmediate nonce color amount recipient inputCommitment nullifier outputCommitment =>
      Json.mkObj [
        ("op", toJson ("relayShieldedImmediate" : String)),
        ("nonce", nativeExpressionJson nonce), ("color", nativeExpressionJson color),
        ("amount", nativeExpressionJson amount), ("recipient", nativeExpressionJson recipient),
        ("inputCommitment", nativeExpressionJson inputCommitment),
        ("nullifier", nativeExpressionJson nullifier),
        ("outputCommitment", nativeExpressionJson outputCommitment)]
  | .mintShielded domain amount => Json.mkObj [
      ("op", toJson ("mintShielded" : String)), ("domain", nativeExpressionJson domain),
      ("amount", nativeExpressionJson amount)]
  | .mintUnshielded domain amount => Json.mkObj [
      ("op", toJson ("mintUnshielded" : String)), ("domain", nativeExpressionJson domain),
      ("amount", nativeExpressionJson amount)]
  | .incUnshieldedInputs color amount isUnshielded => Json.mkObj [
      ("op", toJson ("incUnshieldedInputs" : String)),
      ("color", nativeExpressionJson color), ("amount", nativeExpressionJson amount),
      ("isUnshielded", nativeExpressionJson isUnshielded)]
  | .incUnshieldedOutputs color amount isUnshielded => Json.mkObj [
      ("op", toJson ("incUnshieldedOutputs" : String)),
      ("color", nativeExpressionJson color), ("amount", nativeExpressionJson amount),
      ("isUnshielded", nativeExpressionJson isUnshielded)]
  | .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient => Json.mkObj [
      ("op", toJson ("claimUnshieldedCoinSpend" : String)),
      ("color", nativeExpressionJson color), ("amount", nativeExpressionJson amount),
      ("isUnshielded", nativeExpressionJson isUnshielded),
      ("isContract", nativeExpressionJson isContract),
      ("recipient", nativeExpressionJson recipient)]
  | .requireContractCaller address => Json.mkObj [
      ("op", toJson ("requireContractCaller" : String)), ("address", nativeExpressionJson address)]
  | .readCaller names => Json.mkObj [
      ("op", toJson ("readCaller" : String)),
      ("present", toJson names.present), ("isContract", toJson names.isContract),
      ("contractAddress", toJson names.contractAddress), ("userAddress", toJson names.userAddress)]
  | .readContractAddress destination => Json.mkObj [
      ("op", toJson ("readContractAddress" : String)), ("destination", toJson destination)]
  | .readTokenBalance destination color isUnshielded query => Json.mkObj (
      [("op", toJson ("readTokenBalance" : String)),
        ("destination", toJson destination), ("color", nativeExpressionJson color),
        ("isUnshielded", nativeExpressionJson isUnshielded)] ++ match query with
      | .exact => []
      | .compare less limit =>
        [("comparison", Json.mkObj [
          (if less then "lessThan" else "greaterThan", nativeExpressionJson limit)])])
  | .blockTimeCompare destination before deadline => Json.mkObj [
      ("op", toJson ("blockTimeCompare" : String)), ("destination", toJson destination),
      ("before", toJson before), ("deadline", nativeExpressionJson deadline)]

  | .checkpoint => Json.mkObj [("op", toJson ("checkpoint" : String))]
  | .emitEvent kind payload => Json.mkObj [
      ("op", toJson ("emitEvent" : String)), ("tag", toJson kind.tag),
      ("payload", nativeExpressionJson payload)]

private def operationJson (activityGuard : Option (Expr .bool))
    (operation : Backend.Impact.Op) : Json :=
  let encoded := operationJsonBare operation
  match activityGuard with
  | none => encoded
  | some guard => Json.mkObj [
      ("op", toJson ("guarded" : String)),
      ("guard", nativeExpressionJson guard),
      ("operation", encoded)]

private def effectJson : Effect → Json
  | .readCell state destination ty => Json.mkObj [("op", toJson ("readCell" : String)),
      ("state", toJson state), ("destination", toJson destination), ("type", toJson (typeName ty))]
  | .readMap state destination _ ty key => Json.mkObj [("op", toJson ("readMap" : String)),
      ("state", toJson state), ("destination", toJson destination), ("type", toJson (typeName ty)),
      ("key", expressionJson key)]
  | .readMember state destination _ _ key => Json.mkObj [("op", toJson ("readMember" : String)),
      ("state", toJson state), ("destination", toJson destination),
      ("type", toJson (typeName .bool)), ("key", expressionJson key)]
  | .require condition => Json.mkObj [("op", toJson ("require" : String)), ("condition", expressionJson condition)]
  | .claimContractCall address entryPointHash commitment => Json.mkObj [
      ("op", toJson ("claimContractCall" : String)),
      ("address", expressionJson address),
      ("entryPointHash", expressionJson entryPointHash),
      ("commitment", expressionJson commitment)]
  | .receiveShieldedToMap state nonce color amount selfAddress => Json.mkObj [
      ("op", toJson ("receiveShieldedToMap" : String)), ("state", toJson state),
      ("nonce", expressionJson nonce), ("color", expressionJson color),
      ("amount", expressionJson amount), ("selfAddress", expressionJson selfAddress)]
  | .insertShieldedCoinSet state nonce color amount selfAddress => Json.mkObj [
      ("op", toJson ("insertShieldedCoinSet" : String)), ("state", toJson state),
      ("nonce", expressionJson nonce), ("color", expressionJson color),
      ("amount", expressionJson amount), ("selfAddress", expressionJson selfAddress)]
  | .writeShieldedCoinCell state nonce color amount selfAddress => Json.mkObj [
      ("op", toJson ("writeShieldedCoinCell" : String)), ("state", toJson state),
      ("nonce", expressionJson nonce), ("color", expressionJson color),
      ("amount", expressionJson amount), ("selfAddress", expressionJson selfAddress)]
  | .spendShieldedFromMap state nonce color amount recipient selfAddress => Json.mkObj [
      ("op", toJson ("spendShieldedFromMap" : String)), ("state", toJson state),
      ("nonce", expressionJson nonce), ("color", expressionJson color),
      ("amount", expressionJson amount), ("recipient", expressionJson recipient),
      ("selfAddress", expressionJson selfAddress)]
  | .sendShieldedFromMap state nonce color inputAmount sendAmount recipient selfAddress => Json.mkObj [
      ("op", toJson ("sendShieldedFromMap" : String)), ("state", toJson state),
      ("nonce", expressionJson nonce), ("color", expressionJson color),
      ("inputAmount", expressionJson inputAmount), ("sendAmount", expressionJson sendAmount),
      ("recipient", expressionJson recipient), ("selfAddress", expressionJson selfAddress)]
  | .relayShieldedImmediate nonce color amount recipient selfAddress => Json.mkObj [
      ("op", toJson ("relayShieldedImmediate" : String)),
      ("nonce", expressionJson nonce), ("color", expressionJson color),
      ("amount", expressionJson amount), ("recipient", expressionJson recipient),
      ("selfAddress", expressionJson selfAddress)]
  | .mintShielded domain amount => Json.mkObj [
      ("op", toJson ("mintShielded" : String)), ("domain", expressionJson domain),
      ("amount", expressionJson amount)]
  | .mintUnshielded domain amount => Json.mkObj [
      ("op", toJson ("mintUnshielded" : String)), ("domain", expressionJson domain),
      ("amount", expressionJson amount)]
  | .incUnshieldedInputs color amount isUnshielded => Json.mkObj [
      ("op", toJson ("incUnshieldedInputs" : String)),
      ("color", expressionJson color), ("amount", expressionJson amount),
      ("isUnshielded", expressionJson isUnshielded)]
  | .incUnshieldedOutputs color amount isUnshielded => Json.mkObj [
      ("op", toJson ("incUnshieldedOutputs" : String)),
      ("color", expressionJson color), ("amount", expressionJson amount),
      ("isUnshielded", expressionJson isUnshielded)]
  | .claimUnshieldedCoinSpend color amount isUnshielded isContract recipient => Json.mkObj [
      ("op", toJson ("claimUnshieldedCoinSpend" : String)),
      ("color", expressionJson color), ("amount", expressionJson amount),
      ("isUnshielded", expressionJson isUnshielded),
      ("isContract", expressionJson isContract), ("recipient", expressionJson recipient)]
  | .requireContractCaller address => Json.mkObj [
      ("op", toJson ("requireContractCaller" : String)), ("address", expressionJson address)]
  | .checkpoint => Json.mkObj [("op", toJson ("checkpoint" : String))]
  | .readCaller names => Json.mkObj [
      ("op", toJson ("readCaller" : String)),
      ("present", toJson names.present), ("isContract", toJson names.isContract),
      ("contractAddress", toJson names.contractAddress), ("userAddress", toJson names.userAddress)]
  | .readContractAddress destination => Json.mkObj [
      ("op", toJson ("readContractAddress" : String)), ("destination", toJson destination)]
  | .readTokenBalance destination color isUnshielded query => Json.mkObj (
      [("op", toJson ("readTokenBalance" : String)),
        ("destination", toJson destination), ("color", expressionJson color),
        ("isUnshielded", expressionJson isUnshielded)] ++ match query with
      | .exact => []
      | .compare less limit =>
        [("comparison", Json.mkObj [
          (if less then "lessThan" else "greaterThan", expressionJson limit)])])
  | .blockTimeCompare destination before deadline => Json.mkObj [
      ("op", toJson ("blockTimeCompare" : String)), ("destination", toJson destination),
      ("before", toJson before), ("deadline", expressionJson deadline)]
  | .emitEvent kind payload => Json.mkObj [
      ("op", toJson ("emitEvent" : String)), ("tag", toJson kind.tag),
      ("payload", expressionJson payload)]
  | .writeCell state _ value => Json.mkObj [("op", toJson ("writeCell" : String)),
      ("state", toJson state), ("value", expressionJson value)]
  | .writeMap state _ _ key value => Json.mkObj [("op", toJson ("writeMap" : String)),
      ("state", toJson state), ("key", expressionJson key), ("value", expressionJson value)]
  | .requireAbsent state _ key => Json.mkObj [("op", toJson ("requireAbsent" : String)),
      ("state", toJson state), ("key", expressionJson key)]
  | .readPath state destination keys ty => Json.mkObj [
      ("op", toJson ("readPath" : String)), ("state", toJson state),
      ("destination", toJson destination), ("type", toJson (typeName ty)),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .memberPath state destination keys => Json.mkObj [
      ("op", toJson ("memberPath" : String)), ("state", toJson state),
      ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .counterRead state destination keys => Json.mkObj [
      ("op", toJson ("counterRead" : String)), ("state", toJson state),
      ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .counterLessThan state destination keys threshold => Json.mkObj [
      ("op", toJson ("counterLessThan" : String)), ("state", toJson state),
      ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)),
      ("threshold", expressionJson threshold)]
  | .counterAdjust state keys subtract amount => Json.mkObj [
      ("op", toJson ("counterAdjust" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)),
      ("subtract", toJson subtract), ("amount", sourceImmediateAmountJson amount)]
  | .counterReset state keys => Json.mkObj [
      ("op", toJson ("counterReset" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .merkleTreeIsFull state destination => Json.mkObj [
      ("op", toJson ("merkleTreeIsFull" : String)), ("state", toJson state),
      ("destination", toJson destination)]
  | .merkleTreeIsFullAt state keys destination => Json.mkObj [
      ("op", toJson ("merkleTreeIsFull" : String)), ("state", toJson state),
      ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => match key with | .mk _ value => expressionJson value))]
  | .merkleTreeCheckRoot state expected destination => Json.mkObj [
      ("op", toJson ("merkleTreeCheckRoot" : String)), ("state", toJson state),
      ("expected", expressionJson expected), ("destination", toJson destination)]
  | .merkleTreeCheckRootAt state keys expected destination => Json.mkObj [
      ("op", toJson ("merkleTreeCheckRoot" : String)), ("state", toJson state),
      ("expected", expressionJson expected), ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => match key with | .mk _ value => expressionJson value))]
  | .merkleTreeInsertHash state hash => Json.mkObj [
      ("op", toJson ("merkleTreeInsertHash" : String)), ("state", toJson state),
      ("hash", expressionJson hash)]
  | .merkleTreeInsertHashAt state keys hash => Json.mkObj [
      ("op", toJson ("merkleTreeInsertHash" : String)), ("state", toJson state),
      ("hash", expressionJson hash),
      ("keys", toJson (keys.map fun key => match key with | .mk _ value => expressionJson value))]
  | .merkleTreeInsertHashIndex state hash index => Json.mkObj [
      ("op", toJson ("merkleTreeInsertHashIndex" : String)),
      ("state", toJson state), ("hash", expressionJson hash),
      ("index", expressionJson index)]
  | .merkleTreeInsertHashIndexAt state keys hash index => Json.mkObj [
      ("op", toJson ("merkleTreeInsertHashIndex" : String)), ("state", toJson state),
      ("hash", expressionJson hash), ("index", expressionJson index),
      ("keys", toJson (keys.map fun key => match key with | .mk _ value => expressionJson value))]
  | .merkleTreeReset state => Json.mkObj [
      ("op", toJson ("merkleTreeReset" : String)), ("state", toJson state)]
  | .merkleTreeResetAt state keys _ _ emptyHistory => Json.mkObj ([
      ("op", toJson ("merkleTreeReset" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with | .mk _ value => expressionJson value))] ++
        (if emptyHistory then [("emptyHistory", toJson Bool.true)] else []))
  | .merkleTreeResetHistory state => Json.mkObj [
      ("op", toJson ("merkleTreeResetHistory" : String)), ("state", toJson state)]
  | .merkleTreeResetHistoryAt state keys => Json.mkObj [
      ("op", toJson ("merkleTreeResetHistory" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with | .mk _ value => expressionJson value))]
  | .listLength state destination keys => Json.mkObj [
      ("op", toJson ("listLength" : String)), ("state", toJson state),
      ("destination", toJson destination), ("type", toJson (typeName (.uint (2 ^ 64 - 1)))),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .mapIsEmpty state destination keys => Json.mkObj [
      ("op", toJson ("mapIsEmpty" : String)), ("state", toJson state),
      ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .mapSize state destination keys => Json.mkObj [
      ("op", toJson ("mapSize" : String)), ("state", toJson state),
      ("destination", toJson destination),
      ("type", toJson (typeName (.uint (2 ^ 64 - 1)))),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .listHead state destination keys _ destinations => Json.mkObj [
      ("op", toJson ("listHead" : String)), ("state", toJson state),
      ("destination", toJson destination),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)),
      ("destinations", toJson (destinations.map Prod.fst))]
  | .listPushFront state keys _ values => Json.mkObj [
      ("op", toJson ("listPushFront" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)),
      ("values", toJson (values.map sourceLedgerFieldExprJson))]
  | .listPopFront state keys => Json.mkObj [
      ("op", toJson ("listPopFront" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .listReset state keys => Json.mkObj [
      ("op", toJson ("listReset" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .insertPath state keys _ value => Json.mkObj [
      ("op", toJson ("insertPath" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)), ("value", expressionJson value)]
  | .writePath state keys _ value => Json.mkObj [
      ("op", toJson ("writePath" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)), ("value", expressionJson value)]
  | .readCompositePath state destination keys _ destinations => Json.mkObj [
        ("op", toJson ("readCompositePath" : String)), ("state", toJson state),
        ("destination", toJson destination),
        ("destinations", toJson (destinations.map Prod.fst)),
        ("keys", toJson (keys.map fun key => match key with
          | .mk _ value => expressionJson value))]
  | .writeCompositePath state keys _ values => Json.mkObj [
      ("op", toJson ("writeCompositePath" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value)),
      ("values", toJson (values.map sourceLedgerFieldExprJson))]
  | .emptyMapPath state keys => Json.mkObj [
      ("op", toJson ("emptyMapPath" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .setInsert state keys => Json.mkObj [
      ("op", toJson ("setInsert" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]
  | .removePath state keys => Json.mkObj [
      ("op", toJson ("removePath" : String)), ("state", toJson state),
      ("keys", toJson (keys.map fun key => match key with
        | .mk _ value => expressionJson value))]

private def guardedEffectJson (guard : Option (Expr .bool)) (effect : Effect) : Json :=
  let encoded := effectJson effect
  match guard with
  | none => encoded
  | some condition => Json.mkObj [
      ("op", toJson ("guarded" : String)),
      ("guard", expressionJson condition),
      ("effect", encoded)]

private def stateJson (state : StateDecl) : Json :=
  let compositeSchema (environment : Types.CompositeEnv) (type : Types.CompositeType) : Json :=
    (Backend.Impact.recordSchema environment type).toOption.getD Json.null
  let rec treeJson : LedgerValueType → Json
    | .scalar ty => Json.mkObj [("scalar", toJson (typeName ty))]
    | .map keyTy value => Json.mkObj [("map", toJson [toJson (typeName keyTy), treeJson value])]
    | .set keyTy => Json.mkObj [("set", toJson (typeName keyTy))]
    | .shieldedCoinSet environment type => Json.mkObj [("set", Json.mkObj [
        ("composite", compositeSchema environment type)])]
    | .composite environment type => Json.mkObj [("composite", compositeSchema environment type)]
    | .list environment type => Json.mkObj [("list", match type with
        | .scalar ty => Json.mkObj [("scalar", toJson (typeName ty))]
        | _ => Json.mkObj [("composite", compositeSchema environment type)])]
    | .counter => Json.mkObj [("counter", toJson Bool.true)]
    | .merkleTree depth historic => Json.mkObj (
        [("merkleTree", toJson depth)] ++
        (if historic then [("historic", toJson Bool.true)] else []))
  let kind := match state.kind with
    | .cell ty => Json.mkObj [("cell", toJson (typeName ty))]
    | .map kt vt => Json.mkObj [("map", toJson [typeName kt, typeName vt])]
    | .tree value => Json.mkObj [("tree", treeJson value)]
    | .merkleTree depth => Json.mkObj [("merkleTree", toJson depth)]
    | .historicMerkleTree depth => Json.mkObj [
        ("merkleTree", toJson depth), ("historic", toJson Bool.true)]
    | .opaqueString => Json.mkObj [("opaqueString", toJson Bool.true)]
  Json.mkObj ([("name", toJson state.name), ("kind", kind)] ++
    (if state.sealed then [("sealed", toJson Bool.true)] else []))

private def constructorTypeName : ConstructorType → String
  | .scalar ty => typeName ty
  | .opaqueString => "OpaqueString"

private def constructorValueJson : ConstructorValue → Json
  | .scalar value => Json.mkObj [
      ("kind", toJson ("scalarExpression" : String)),
      ("expression", nativeExpressionJson value)]
  | .opaqueStringParameter name => Json.mkObj [
      ("kind", toJson ("opaqueStringParameter" : String)),
      ("name", toJson name)]
  | .opaqueStringLiteral value => Json.mkObj [
      ("kind", toJson ("opaqueStringLiteral" : String)),
      ("value", toJson value)]

private def constructorJson (ctor : Constructor) : Json := Json.mkObj [
  ("parameters", toJson (ctor.parameters.map fun parameter => Json.mkObj [
    ("name", toJson parameter.name), ("type", toJson (constructorTypeName parameter.type))])),
  ("initializers", toJson (ctor.initializers.map fun initializer => Json.mkObj [
    ("state", toJson initializer.state),
    ("type", toJson (constructorTypeName initializer.type)),
    ("value", constructorValueJson initializer.value)]))]

private def jsonLetParts (expression : Json) : Except String (Array Json × Json) := do
  let tag ← (← expression.getObjVal? "tag").getStr?
  let body ← expression.getObjVal? "body"
  match tag with
  | "lets" => return (← (← expression.getObjVal? "bindings").getArr?, body)
  | "let" =>
    let name ← expression.getObjVal? "name"
    let value ← expression.getObjVal? "value"
    return (#[Json.arr #[name, value]], body)
  | _ => throw "not a binding"

private def jsonBindingParts : Json → Option (String × Json)
  | .arr items =>
    if items.size != 2 then none else
      match items[0]?, items[1]? with
      | some (Json.str name), some value => some (name, value)
      | _, _ => none
  | _ => none

private def jsonStringField (expression : Json) (field : String) : Option String :=
  ((expression.getObjVal? field).toOption.bind fun value => value.getStr?.toOption)

private def jsonValueField (expression : Json) (field : String) : Option Json :=
  (expression.getObjVal? field).toOption

private def jsonArrayField (expression : Json) (field : String) : Option (Array Json) :=
  (jsonValueField expression field).bind fun value => value.getArr?.toOption

private partial def jsonFreeReferences (bound : List String) : Json → List String
  | .obj fields =>
    let expression := .obj fields
    match jsonStringField expression "tag" with
    | some "reference" =>
      match jsonStringField expression "name" with
      | some name => if bound.contains name then [] else [name]
      | none => [""]
    | some "let" =>
      match jsonStringField expression "name", jsonValueField expression "value",
          jsonValueField expression "body" with
      | some name, some value, some body =>
        jsonFreeReferences bound value ++ jsonFreeReferences (name :: bound) body
      | _, _, _ => fields.toList.flatMap (fun (_, value) => jsonFreeReferences bound value)
    | some "lets" =>
      match jsonArrayField expression "bindings", jsonValueField expression "body" with
      | some bindings, some body => Id.run do
        let mut scope := bound
        let mut references := []
        for binding in bindings do
          match jsonBindingParts binding with
          | some (name, value) =>
            references := references ++ jsonFreeReferences scope value
            scope := name :: scope
          | none => references := references ++ [""]
        return references ++ jsonFreeReferences scope body
      | _, _ => fields.toList.flatMap (fun (_, value) => jsonFreeReferences bound value)
    | _ => fields.toList.flatMap (fun (_, value) => jsonFreeReferences bound value)
  | .arr values => values.toList.flatMap (jsonFreeReferences bound)
  | _ => []

private def shareableBinding (inputNames outputNames earlierNames : List String)
    (binding : Json) : _root_.Bool :=
  match jsonBindingParts binding with
  | some (name, value) =>
    -- '$' marks compiler-generated temporaries in Noctium expressions.
    let allowedNames := inputNames ++ earlierNames
    name.startsWith "$" && !inputNames.contains name &&
      !outputNames.contains name && !earlierNames.contains name &&
      (jsonFreeReferences [] value).all fun reference =>
        !outputNames.contains reference && allowedNames.contains reference
  | none => _root_.Bool.false

private def commonSharedPrefix (outputs : List Json) (inputNames outputNames : List String) : Array Json := Id.run do
  if outputs.length < 2 then return #[]
  let some firstExpression := outputs.head? | return #[]
  let some (firstBindings, _) := (jsonLetParts firstExpression).toOption | return #[]
  let otherBindings := outputs.drop 1 |>.map fun expression =>
    ((jsonLetParts expression).toOption.map Prod.fst).getD #[]
  let mut common := #[]
  let mut earlierNames := []
  for index in List.range firstBindings.size do
    let some binding := firstBindings[index]? | break
    if otherBindings.all (fun bindings => bindings[index]? == some binding) &&
        shareableBinding inputNames outputNames earlierNames binding then
      common := common.push binding
      if let some (name, _) := jsonBindingParts binding then
        earlierNames := earlierNames ++ [name]
    else
      break
  return common

private def beginsWithBindings (bindings shared : Array Json) : _root_.Bool :=
  shared.size ≤ bindings.size && shared.toList.zipIdx.all fun (binding, index) =>
    bindings[index]? == some binding

private def wrapJsonLets (bindings : Array Json) (body : Json) : Json :=
  if bindings.isEmpty then body else if bindings.size == 1 then
    match jsonBindingParts bindings[0]! with
    | some (name, value) => Json.mkObj [
        ("tag", toJson ("let" : String)), ("name", toJson name), ("value", value), ("body", body)]
    | none => body
  else Json.mkObj [
    ("tag", toJson ("lets" : String)), ("bindings", Json.arr bindings), ("body", body)]

private def stripSharedPrefix (shared : Array Json) (expression : Json) : Json :=
  match jsonLetParts expression with
  | .ok (bindings, body) =>
    if beginsWithBindings bindings shared then
      wrapJsonLets (bindings.extract shared.size bindings.size) body
    else expression
  | .error _ => expression

private partial def markSharedConstraintLets (shared : Array Json) : Json → Json
  | .arr values => Json.arr (values.map (markSharedConstraintLets shared))
  | .obj fields =>
    let expression := Json.mkObj (fields.toList.map fun (key, value) =>
      (key, markSharedConstraintLets shared value))
    match jsonLetParts expression with
    | .ok (bindings, body) =>
      if beginsWithBindings bindings shared then
        Json.mkObj [("tag", toJson ("sharedLets" : String)),
          ("body", wrapJsonLets (bindings.extract shared.size bindings.size) body)]
      else expression
    | .error _ => expression
  | expression => expression

private def circuitSchemaJson (name : Name) (circuit : Circuit)
    (standaloneFile : _root_.Bool := Bool.true) : Json :=
  let files := if standaloneFile then [("file", toJson (name.toString ++ ".zkir"))] else []
  let outputExpressions := circuit.outputs.map fun out => nativeExpressionJson out.value
  let sharedBindings := commonSharedPrefix outputExpressions (circuit.inputs.map (·.name))
    (circuit.outputs.map (·.name))
  let outputs := (circuit.outputs.zip outputExpressions).map fun (out, expression) => Json.mkObj [
    ("name", toJson out.name), ("type", toJson (typeName out.ty)),
    ("visibility", toJson ("public" : String)),
    ("expression", if sharedBindings.isEmpty then expression
      else stripSharedPrefix sharedBindings expression)]
  Json.mkObj ([("name", toJson name.toString)] ++ files ++ [
    ("inputs", toJson (circuit.inputs.map fun input => Json.mkObj [
      ("name", toJson input.name), ("type", toJson (typeName input.ty)),
      ("visibility", toJson (if input.visibility == .«public» then "public" else "private"))])),
    ("outputs", toJson outputs)] ++
    (if sharedBindings.isEmpty then [] else [("sharedBindings", Json.arr sharedBindings)]) ++ [
    ("constraints", toJson (circuit.constraints.map fun constraint =>
      if sharedBindings.isEmpty then nativeExpressionJson constraint
      else markSharedConstraintLets sharedBindings (nativeExpressionJson constraint)))])

private def failDiagnostic (d : Diagnostic) : CommandElabM α :=
  throwError "{d.span.file}:{d.span.line}:{d.span.column}: {d.message}"

/-- Rebuild module roots from their registered source constants for each
compiler inspection. Generated declarations remain convenient names for users,
but their cached values do not authorize compilation. -/
private unsafe def rebuildModuleOutputs : CommandElabM (Array (Name × ModuleBuildOutput)) := do
  let env ← getEnv
  let mut outputs := #[]
  for info in moduleBuildRegistry.getState env do
    unless env.isImportedConst info.contractName do
      outputs := outputs.push (info.contractName, ← rebuildModuleBuild info)
  return outputs

private def moduleCircuitFor (outputs : Array (Name × ModuleBuildOutput)) (name : Name) :
    Option ModuleCircuitBuildInfo :=
  outputs.toList.flatMap (·.2.circuits) |>.find? (·.declarationName == name)

private def importedModuleCircuit (env : Environment) (name : Name) : _root_.Bool :=
  match name with
  | .str (.str owner "__moduleCircuit") _ =>
    (moduleBuildRegistry.getState env).any fun info =>
      env.isImportedConst info.contractName && owner == info.contractName
  | _ => _root_.Bool.false

private def importedWitnessCircuit (env : Environment) (name : Name) : _root_.Bool :=
  (witnessRegistry.getState env).any (·.circuitName == name)

private def moduleWitnessProgramFor (outputs : Array (Name × ModuleBuildOutput))
    (info : WitnessInfo) : Option Helpers.Program := do
  let circuit ← outputs.toList.flatMap (·.2.circuits) |>.find? fun item =>
    item.source.kind == .witness && item.programName == info.sourceName &&
      item.source.outputName == info.exportName
  pure circuit.program

/-- Evaluate only definitions generated and registered by the Noctium elaborators. -/
private unsafe def registeredCircuits (moduleOutputs : Array (Name × ModuleBuildOutput))
    (contracts : Array (Name × Contract)) :
    CommandElabM (Array (Name × Circuit)) := do
  let env ← getEnv
  let referencedCircuits := contracts.toList.flatMap fun (_, contract) =>
    contract.entrypoints.map (·.circuit.name)
  let mut circuits := #[]
  for info in circuitRegistry.getState env do
    let imported := env.isImportedConst info.declName
    let selectedImportedOrdinary := imported &&
      referencedCircuits.contains info.declName.toString &&
      info.stateProgram?.isNone &&
      !importedWitnessCircuit env info.declName &&
      !importedModuleCircuit env info.declName
    if !imported || selectedImportedOrdinary then
      let moduleCircuit := moduleCircuitFor moduleOutputs info.declName
      if moduleCircuit.isNone then
        if let some (sourceName, exportName) := info.sourceProgram? then
          let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
          match ComponentDisclosure.checkProgram program exportName with
          | .ok _ => pure ()
          | .error d => failDiagnostic d
      if let some text := info.specializationArtifact? then
        match Helpers.Specialization.parseSignatureArtifactText text with
        | .ok _ => pure ()
        | .error message => throwError "invalid generic specialization signature artifact: {message}"
      let circuit ← if info.stateProgram?.isSome then
          let some compiledEntry := contracts.toList.flatMap (·.2.entrypoints) |>.find?
            (·.circuit.name == info.declName.toString)
            | throwError "structured ledger circuit has no owning contract: {info.declName}"
          pure compiledEntry.circuit
        else match moduleCircuit with
          | some fresh => pure fresh.circuit
          | none => evalConstCheck Circuit ``Circuit info.declName
      match circuit.validate sourceCapabilities with
      | .error d => failDiagnostic d
      | .ok _ =>
        if selectedImportedOrdinary then
          unless circuit.name == info.declName.toString do
            throwError "registered circuit identity does not match declaration '{info.declName}'"
        match Disclosure.circuit circuit with
        | .error d => failDiagnostic d
        | .ok _ => circuits := circuits.push (info.declName, circuit)
  return circuits

private unsafe def registeredContracts (moduleOutputs : Array (Name × ModuleBuildOutput))
    (dedupRangeChecks : _root_.Bool) :
    CommandElabM (Array (Name × Contract) × Array (Name × String × Witness.Compiled)) := do
  let env ← getEnv
  let mut contracts : Array (Name × Contract) := #[]
  let mut hosted : Array (Name × String × Witness.Compiled) := #[]
  for name in contractRegistry.getState env do
    unless env.isImportedConst name do
      let contract ← match moduleOutputs.toList.find? (·.1 == name) with
        | some (_, rebuilt) => pure rebuilt.contract
        | none => evalConstCheck Contract ``Contract name
      let mut entries : List Entrypoint := []
      for compiledEntry in contract.entrypoints do
        let source := (circuitRegistry.getState env).find? fun info =>
          info.declName.toString == compiledEntry.circuit.name && info.stateProgram?.isSome
        let rebuilt : Entrypoint × Option Witness.Compiled ← match source.bind (·.stateProgram?) with
          | none => pure (compiledEntry, none)
          | some (sourceName, exportName) => do
            let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
            let (fresh, hostWitness) ← match Witness.compileStateEntrypointWithWitness program exportName
                contract.state compiledEntry.circuit.name dedupRangeChecks with
              | .ok value => pure value
              | .error d => failDiagnostic d
            let namedCircuit := {fresh.circuit with name := compiledEntry.circuit.name}
            pure ({fresh with name := compiledEntry.name, circuit := namedCircuit}, hostWitness)
        let (rebuiltEntry, hostWitness) := rebuilt
        if let some compiled := hostWitness then
          hosted := hosted.push (name, rebuiltEntry.name, compiled)
        entries := entries ++ [rebuiltEntry]
      let contract := {contract with entrypoints := entries}
      match contract.validate sourceCapabilities with
      | .error d => failDiagnostic d
      | .ok _ =>
        match Disclosure.contract contract with
        | .error d => failDiagnostic d
        | .ok _ => contracts := contracts.push (name, contract)
  return (contracts, hosted)

private def artifactName (name : Name) : String := name.toString

private def validateArtifactStem (text : String) : CommandElabM Unit := do
  if text.contains '/' || text.contains '\\' || (text.splitOn "..").length > 1 then
    throwError "declaration name is not a safe artifact filename: {text}"

private def validateArtifactName (name : Name) : CommandElabM Unit :=
  validateArtifactStem (artifactName name)

private def nativeCircuitFile (contract : Name) (ep : Entrypoint) : String :=
  artifactName contract ++ "." ++ ep.name ++ ".zkir"

private def nativePlanFile (contract : Name) (ep : Entrypoint) : String :=
  artifactName contract ++ "." ++ ep.name ++ ".impact.json"

private def returnViewsJson (views : List ReturnView) : Json :=
  Json.arr (views.toArray.map fun view =>
    let schema : Except String Json := do
      let compiled ← (Types.compileType view.environment view.type).mapError
        fun diagnostic => diagnostic.message
      Types.schemaJson compiled
    Json.mkObj [
      ("name", toJson view.name),
      ("schema", schema.toOption.getD Json.null),
      ("fields", toJson view.fields)])

/-- The exact symbolic plan tree written by the compiler. This pure function
also gives proof modules a kernel-visible artifact boundary. -/
def nativePlanJson (profile : TargetProfile) (contractName : Name)
    (state : List StateDecl) (ctor : Option Constructor)
    (ep : Entrypoint) (plan : Backend.Impact.Plan)
    (standaloneFile : _root_.Bool := Bool.true) : Json := Id.run do
  let publicReadCount := Backend.Impact.publicInputReadCount ep.circuit.inputs
  let reads := plan.reads.zipIdx.map fun (indexedRead : Backend.Impact.Read × Nat) =>
    let item := indexedRead.1
    let index := indexedRead.2
    let projections : List (String × Json) := if index < publicReadCount then [] else match item.ty with
      | .bytes _ | .jubjubPoint => [("projections", toJson ((Backend.Impact.Read.bindings item).map fun (binding : String × Ty) => Json.mkObj [
          ("name", toJson binding.1), ("type", toJson (typeName binding.2))]))]
      | _ => []
    Json.mkObj ([
      ("name", toJson item.name),
      ("type", toJson (if item.schema.isSome then "Composite" else typeName item.ty))] ++
      (match item.schema with
        | none => []
        | some schema => [
            ("components", toJson (item.components.map fun (name, ty) => Json.mkObj [
              ("name", toJson name), ("type", toJson (typeName ty))])),
            ("schema", schema)]) ++ projections ++
      (match item.guard with
        | none => []
        | some guard => [("guard", nativeExpressionJson guard)]))
  let targetPlanFields := if profile.name == TargetProfile.selected321.name then [
    ("target", toJson profile.name), ("targetProfile", toJson profile)
  ] else []
  let returnFields := if ep.returns.isEmpty then [] else [
    ("returns", toJson (ep.returns.map fun returned => Json.mkObj [
      ("name", toJson returned.name), ("type", toJson (typeName returned.ty)),
      ("visibility", toJson ("public" : String)),
      ("expression", nativeExpressionJson returned.value)]))]
  let returnViewFields := if ep.returnViews.isEmpty then [] else [
    ("returnViews", returnViewsJson ep.returnViews)]
  let callInputFields := if ep.callInputs.isEmpty then [] else [
    ("callInputs", toJson ep.callInputs)]
  let constructorFields := match ctor with
    | none => []
    | some value => [("constructor", constructorJson value)]
  let circuit := circuitSchemaJson ep.circuit.name.toName ep.circuit standaloneFile
  let schemaVersion : Nat := if (circuit.getObjVal? "sharedBindings").isOk then 2 else 1
  return Json.mkObj ([
    ("schemaVersion", toJson schemaVersion)] ++ targetPlanFields ++ [
    ("contractName", toJson contractName.toString),
    ("entrypoint", toJson ep.name), ("nativeCircuitFile", toJson (nativeCircuitFile contractName ep)),
    ("state", toJson (state.map stateJson)),
    ("circuit", circuit),
    ("operations", toJson (plan.operations.zipIdx.map fun (operation, index) =>
      operationJson (plan.activityGuards[index]?.getD none) operation)),
    ] ++ constructorFields ++ callInputFields ++ returnFields ++ returnViewFields ++ [
    ("reads", toJson reads),
    ("guards", toJson (plan.guards.map nativeExpressionJson))])

private unsafe def inspectWithModules (moduleOutputs : Array (Name × ModuleBuildOutput))
    (dedupRangeChecks : _root_.Bool := Bool.false) :
    CommandElabM (Array (Name × Circuit) × Array (Name × Contract) × Array (Name × String × Witness.Compiled)) := do
  if (← get).messages.hasErrors then
    throwError "cannot export Noctium artifacts after source elaboration errors"
  let (contracts, hosted) ← registeredContracts moduleOutputs dedupRangeChecks
  let circuits ← registeredCircuits moduleOutputs contracts
  let sourceEnv ← getEnv
  let controls := (controlRegistry.getState sourceEnv).filter (!sourceEnv.isImportedConst ·)
  if circuits.isEmpty && controls.isEmpty then throwError "source contains no Noctium circuit declarations"
  for name in controls do validateArtifactName name
  for (name, _) in circuits do validateArtifactName name
  for (name, contract) in contracts do
    validateArtifactName name
    for ep in contract.entrypoints do
      validateArtifactStem ep.name
      unless circuits.any (fun (_, circuit) => circuit.name == ep.circuit.name) do
        throwError "contract entrypoint references imported circuit '{ep.circuit.name}'; include its source declaration in this compilation unit"
  return (circuits, contracts, hosted)

private unsafe def inspect : CommandElabM (Array (Name × Circuit) × Array (Name × Contract)) := do
  let moduleOutputs ← rebuildModuleOutputs
  let (circuits, contracts, _) ← inspectWithModules moduleOutputs
  return (circuits, contracts)

elab "#noctium_check" : command => do
  let (circuits, contracts) ← unsafe inspect
  logInfo m!"checked {circuits.size} circuit(s), {contracts.size} contract(s); target integration unqualified"

private unsafe def checkTarget (profile : TargetProfile) : CommandElabM Unit := do
  let (circuits, contracts) ← unsafe inspect
  logInfo m!"checked {circuits.size} circuit(s), {contracts.size} contract(s); target {profile.name} ({profile.qualification})"

private def parseTargetProfile (source : String) : CommandElabM TargetProfile := do
  match TargetProfile.parse source with
  | .ok profile => pure profile
  | .error message => throwError "invalid target profile: {message}"

elab "#noctium_check_target" profileJson:str : command => do
  let profile ← parseTargetProfile profileJson.getString
  unsafe checkTarget profile

private def compileArtifacts (directory : String) (profile : TargetProfile)
    (displayDirectory : String := directory) (roles : List ArtifactRole := [])
    (rustBindings dedupRangeChecks : _root_.Bool := Bool.false) : CommandElabM Unit := do
  let moduleOutputs ← unsafe rebuildModuleOutputs
  let (circuits, contracts, hosted) ← unsafe inspectWithModules moduleOutputs dedupRangeChecks
  let emit := fun role => roles.isEmpty || roles.contains role
  let contracts := if emit .ledger then contracts else #[]
  let bindPlanBytes := !(emit .standalone) && !contracts.isEmpty
  let entryCircuits := contracts.toList.flatMap fun (_, contract) => contract.entrypoints.map (·.circuit.name)
  -- Lower and validate the requested products before publishing files.
  let mut lowered : Array (ArtifactRole × String × String) := #[]
  let mut planDigests : Std.HashMap String String := {}
  let sourceEnv ← getEnv
  let controls := if emit .control then
    (controlRegistry.getState sourceEnv).filter (!sourceEnv.isImportedConst ·) else #[]
  let witnesses := (witnessRegistry.getState sourceEnv).filter (!sourceEnv.isImportedConst ·.circuitName)
  let mut witnessMetadata : Array Json := #[]
  let mut standaloneWitnesses : Array (String × Witness.Compiled) := #[]
  for name in controls do
    validateArtifactName name
    let plan ← unsafe evalConstCheck Json ``Lean.Json name
    lowered := lowered.push (.control, artifactName name ++ ".control.json", plan.pretty)
  for (name, circuit) in (if emit .standalone then circuits else #[]) do
    match Backend.Zkir.lowerCircuit circuit dedupRangeChecks with
    | .error d => failDiagnostic d
    | .ok json => lowered := lowered.push (.standalone, artifactName name ++ ".zkir", json.pretty)
  for (name, _) in (if emit .specialization then circuits else #[]) do
    let some info := circuitRegistry.getState (← getEnv) |>.find? (·.declName == name)
      | throwError "missing circuit registry entry for '{name}'"
    if let some fresh := moduleCircuitFor moduleOutputs name then
      lowered := lowered.push (.specialization, artifactName name ++ ".specialization.json",
        (Lean.toJson fresh.signatureArtifact).pretty)
    else if let some text := info.specializationArtifact? then
      let artifact ← match Helpers.Specialization.parseSignatureArtifactText text with
        | .ok artifact => pure artifact
        | .error message => throwError "invalid generic specialization signature artifact: {message}"
      lowered := lowered.push (.specialization, artifactName name ++ ".specialization.json", (Lean.toJson artifact).pretty)
  for info in witnesses do
    let witnessPrefix := artifactName info.circuitName
    if emit .witness && (emit .standalone || entryCircuits.contains info.circuitName.toString) then
      let moduleProgram := moduleWitnessProgramFor moduleOutputs info
      -- Ledger-only bindings replace the standalone relation with the checked ledger relation.
      let cached := if moduleProgram.isNone && !(dedupRangeChecks && emit .standalone) then
        (checkedWitnesses.getState sourceEnv).find? info.circuitName
        else none
      let compiled ← match cached with
        | some value => pure value
        | none => do
          let program ← match moduleProgram with
            | some fresh => pure fresh
            | none => unsafe evalConstCheck Helpers.Program ``Helpers.Program info.sourceName
          match Witness.compile program info.exportName info.circuitName.toString info.outputName dedupRangeChecks with
          | .ok value => pure value
          | .error diagnostic => failDiagnostic diagnostic
      standaloneWitnesses := standaloneWitnesses.push (info.circuitName.toString, compiled)
      if emit .standalone then
        lowered := lowered.push (.witness, witnessPrefix ++ ".witness.json", compiled.binding.compress)
        lowered := lowered.push (.witness, witnessPrefix ++ ".witness.control.json", compiled.plan.pretty)
        witnessMetadata := witnessMetadata.push (Json.mkObj [("circuit", toJson info.circuitName.toString),
          ("bindingFile", toJson (witnessPrefix ++ ".witness.json")), ("controlFile", toJson (witnessPrefix ++ ".witness.control.json")),
          ("target", toJson ("standalone" : String)), ("nativeWitnessQualified", toJson Bool.false)])
    if emit .observations then
      if let some text := info.observationArtifact? then
        let observation ← match Json.parse text with
          | .ok value => pure value
          | .error message => throwError "invalid source observation artifact: {message}"
        lowered := lowered.push (.observations, witnessPrefix ++ ".observations.json", observation.pretty)
  for (name, contract) in contracts do
    for ep in contract.entrypoints do
      let ep := Passes.pruneEntrypoint ep
      if !(emit .witness) && witnesses.any (·.circuitName.toString == ep.circuit.name) then
        throwError "ledger entrypoint '{name}.{ep.name}' requires --emit witness"
      let (plan, json) ← match Backend.Zkir.lowerPrunedEntrypoint contract.state ep dedupRangeChecks with
        | .error d => failDiagnostic d
        | .ok artifacts => pure artifacts
      lowered := lowered.push (.ledger, nativeCircuitFile name ep, json.pretty)
      let compiledWitness? ← if let some (_, compiled) :=
          standaloneWitnesses.find? (fun (circuitName, _) => circuitName == ep.circuit.name) then
          pure (some compiled)
        else if let some (_, _, compiled) := hosted.find? (fun (owner, entrypoint, _) =>
            owner == name && entrypoint == ep.name) then do
          unless emit .witness do
            throwError "ledger entrypoint '{name}.{ep.name}' requires --emit witness"
          pure (some compiled)
        else pure none
      if let some compiled := compiledWitness? then
        let compiled ← match Witness.bindEntrypoint compiled json name.toString ep.name
            (nativeCircuitFile name ep) profile.name
            ((plan.reads.drop (Backend.Impact.publicInputReadCount ep.circuit.inputs)).flatMap (·.bindings))
            ep.callInputs with
          | .ok value => pure value
          | .error diagnostic => failDiagnostic diagnostic
        let witnessPrefix := artifactName name ++ "." ++ ep.name
        lowered := lowered.push (.witness, witnessPrefix ++ ".witness.json", compiled.binding.compress)
        lowered := lowered.push (.witness, witnessPrefix ++ ".witness.control.json", compiled.plan.pretty)
        if rustBindings then
          let code ← match RustBinding.generate (witnessPrefix ++ ".witness.control.json") compiled.binding with
            | .ok value => pure value
            | .error message => throwError "invalid Rust witness interface: {message}"
          lowered := lowered.push (.rustBinding, "bindings/rust/" ++ witnessPrefix ++ ".rs", code)
        witnessMetadata := witnessMetadata.push (Json.mkObj [("circuit", toJson ep.circuit.name),
          ("bindingFile", toJson (witnessPrefix ++ ".witness.json")), ("controlFile", toJson (witnessPrefix ++ ".witness.control.json")),
          ("target", toJson ("entrypoint" : String)), ("contract", toJson name.toString),
          ("entrypoint", toJson ep.name), ("nativeWitnessQualified", toJson Bool.false)])
      let planJson := nativePlanJson profile name contract.state contract.constructor ep plan (emit .standalone)
      let file := nativePlanFile name ep
      let content := if bindPlanBytes then planJson.compress else planJson.pretty
      if bindPlanBytes then
        planDigests := planDigests.insert file (EntryPointHash.sha256Hex (content ++ "\n").toUTF8)
      lowered := lowered.push (.ledger, file, content)
  if lowered.isEmpty then throwError "source has no artifacts for the selected roles"
  if rustBindings && !(lowered.any (·.1 == .rustBinding)) then
    throwError "--bindings rust requires a ledger entrypoint with a host witness"
  unless uniqueNames (lowered.toList.map (·.2.1)) do
    throwError "generated artifact filenames collide; rename the circuit or contract entrypoint"
  let contractMetadata := contracts.map fun (name, contract) =>
    let entrypoints := contract.entrypoints.map fun ep => Id.run do
      let baseFields : List (String × Json) := [
        ("name", toJson ep.name), ("circuit", toJson ep.circuit.name),
        ("nativeCircuitFile", toJson (nativeCircuitFile name ep)),
        ("nativePlanFile", toJson (nativePlanFile name ep)),
        ("nativeCircuitQualified", toJson Bool.false),
        ("effects", toJson (ep.effects.zipIdx.map fun (effect, index) =>
          guardedEffectJson (ep.effectGuards[index]?.getD none) effect))]
      let callInputFields : List (String × Json) := if ep.callInputs.isEmpty then [] else [
        ("callInputs", toJson ep.callInputs)]
      let returnFields : List (String × Json) := if ep.returns.isEmpty then [] else [
        ("returns", toJson (ep.returns.map fun returned => Json.mkObj [
          ("name", toJson returned.name), ("type", toJson (typeName returned.ty)),
          ("visibility", toJson ("public" : String)),
          ("expression", nativeExpressionJson returned.value)]))]
      let returnViewFields : List (String × Json) := if ep.returnViews.isEmpty then [] else [
        ("returnViews", returnViewsJson ep.returnViews)]
      let digestFields := (planDigests[nativePlanFile name ep]?).toList.map fun digest =>
        ("nativePlanSha256", toJson digest)
      pure (Json.mkObj (baseFields ++ digestFields ++ callInputFields ++ returnFields ++ returnViewFields))
    let constructorFields := match contract.constructor with
      | none => []
      | some ctor => [("constructor", constructorJson ctor)]
    Json.mkObj ([
      ("name", toJson name.toString),
      ("state", toJson (contract.state.map stateJson)),
      ("entrypoints", toJson entrypoints)] ++ constructorFields)
  let controlFields := if controls.isEmpty then [] else [
    ("hostControlPlans", toJson (controls.toList.map fun name => Json.mkObj [
      ("name", toJson name.toString), ("file", toJson (artifactName name ++ ".control.json")),
      ("nativeGuardQualified", toJson Bool.false)]))]
  let witnessFields := if witnessMetadata.isEmpty then [] else [("hostWitnessPlans", Json.arr witnessMetadata)]
  let explicitSelection := !roles.isEmpty || rustBindings
  let inventory := if !explicitSelection then [] else [("artifacts", Json.arr (lowered.map fun (role, file, content) =>
    Json.mkObj ([("role", toJson role.label), ("file", toJson file)] ++
      if role == .rustBinding then
        [("sha256", toJson (EntryPointHash.sha256Hex (content ++ "\n").toUTF8))]
      else [])))]
  let circuitSchemas := if emit .standalone then circuits else #[]
  let schemaVersion : Nat := if bindPlanBytes then 3 else if explicitSelection then 2 else 1
  let metadata := Json.mkObj ([
    ("schemaVersion", toJson schemaVersion), ("target", toJson profile.name),
    ("targetProfile", toJson profile),
    ("qualification", toJson ("unqualified-relation-and-state-description" : String)),
    ("deployable", toJson Bool.false),
    ("contracts", Json.arr contractMetadata),
    ("circuits", toJson (circuitSchemas.map fun (name, circuit) => circuitSchemaJson name circuit (emit .standalone)))] ++
    controlFields ++ witnessFields ++ inventory)
  let path : System.FilePath := directory
  liftIO <| IO.FS.createDirAll path
  if rustBindings then liftIO <| IO.FS.createDirAll (path / "bindings" / "rust")
  for (_, name, content) in lowered do
    liftIO <| IO.FS.writeFile (path / name) (content ++ "\n")
  liftIO <| IO.FS.writeFile (path / "noctium.json") (metadata.pretty ++ "\n")
  let nativeCount : Nat := contracts.foldl (fun total (_, contract) => total + contract.entrypoints.length) 0
  let standaloneCount := if emit .standalone then circuits.size else 0
  if controls.isEmpty then
    logInfo m!"emitted {standaloneCount} circuit relation(s), {nativeCount} native entrypoint relation(s), and state metadata to {displayDirectory}; not a deployable contract bundle"
  else
    logInfo m!"emitted {controls.size} host-only control plan(s), {standaloneCount} circuit relation(s), and {nativeCount} native entrypoint relation(s) to {displayDirectory}; structured native guards unavailable"

elab "#noctium_compile" directory:str : command =>
  compileArtifacts directory.getString TargetProfile.sourceBaseline

elab "#noctium_compile_target" directory:str profileJson:str displayDirectory:(str)? selection:(str)?
    bindings:(str)? optimization:(str)? : command => do
  let profile ← parseTargetProfile profileJson.getString
  let selection ← match selection with
    | none => pure []
    | some value =>
      match Json.parse value.getString >>= fromJson? >>= List.mapM ArtifactRole.parse with
      | .ok roles => pure roles
      | .error message => throwError "{message}"
  let target := (bindings.map (·.getString)).getD ""
  if !target.isEmpty && target != "rust" then throwError "unsupported binding target '{target}'"
  let rustBindings := target == "rust"
  let mode := (optimization.map (·.getString)).getD ""
  if !mode.isEmpty && mode != "dedup-range-checks" then throwError "unsupported optimization '{mode}'"
  match ArtifactRole.validateSelection selection rustBindings with
  | .ok _ =>
    let display := (displayDirectory.map (·.getString)).getD directory.getString
    compileArtifacts directory.getString profile display selection rustBindings (mode == "dedup-range-checks")
  | .error message => throwError "{message}"

end Noctium.Compiler
