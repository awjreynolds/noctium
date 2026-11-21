import Noctium.Disclosure
import Noctium.Helpers
import Noctium.Helpers.Specialization
import Noctium.ComponentDisclosure
import Noctium.Control
import Noctium.Witness
import Noctium.Modules
import Noctium.Crypto.Signatures
import Noctium.Backend.Impact
import Noctium.Types.Maybe
import Noctium.EntryPointHash
import Noctium.Wire
import Lean

namespace Noctium
open Lean Elab Command

/-- Declarations registered through the supported Noctium circuit surface. -/
structure CircuitInfo where
  declName : Name
  inputs : List (String × Ty)
  publicInputs : List (String × Ty)
  outputs : List (String × Ty)
  /-- Logical witness-circuit results retained when a grouped helper result is
  expanded into native leaves. The names point to typed Expr constants. -/
  logicalOutputs : List (String × Ty × Name) := []
  /-- The declared aggregate label and its checked return schema. -/
  aggregateOutputs : List (String × Name × List String) := []
  /-- Hosted call arguments are selected from source parameters, never callback slots. -/
  witnessCallArguments? : Option (List String) := none
  aggregateInputs : List CallInputView := []
  sourceProgram? : Option (Name × String) := none
  /-- Structured ledger bodies are rebuilt from their typed source at export. -/
  stateProgram? : Option (Name × String) := none
  specializationArtifact? : Option String := none
  deriving Inhabited

initialize circuitRegistry : SimplePersistentEnvExtension CircuitInfo (Array CircuitInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }
initialize contractRegistry : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

private structure CallInterface where
  contract : Name
  operation : String
  argumentFields : List (String × Ty)
  argumentViews : List (String × List (String × Ty))
  resultFields : List (String × Ty)
  resultViews : List (String × List (String × Ty))
  deriving Inhabited

/-- A named Lean declaration whose source metadata defines a checked contract ABI. -/
inductive ContractInterface where
  | declared

private partial def callViewLeafTypes : Types.Layout → List Ty
  | .unit => []
  | .scalar .nativeField => [.native]
  | .scalar .booleanField => [.bool]
  | .scalar (.boundedUnsignedField maximum) | .scalar (.enumTagField maximum) => [.uint maximum]
  | .scalar .byteField => [.uint 255]
  | .tuple items => items.flatMap callViewLeafTypes
  | .structure _ fields => fields.flatMap (callViewLeafTypes ∘ Prod.snd)
  | .vector length element => (List.replicate length (callViewLeafTypes element)).flatten
  | .bytes length _ => List.replicate length (.uint 255)
  | .enumeration _ _ maximum payloadLeaves _ _ => .uint maximum :: List.replicate payloadLeaves .native

initialize callInterfaceRegistry : SimplePersistentEnvExtension CallInterface (Array CallInterface) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

private inductive CallAbiPart where
  | scalar (type : Ty)
  | view (fields : List (Nat × Ty))
  | viewField
  deriving BEq

-- Keep physical field positions in the ABI shape independently of source labels.
private def callAbiShape (fields : List (String × Ty))
    (views : List (String × List (String × Ty))) : List CallAbiPart :=
  let fieldNames := fields.map Prod.fst
  fields.map fun (name, type) =>
    match views.find? (fun (_, members) => members.any (·.1 == name)) with
    | none => .scalar type
    | some (_, members) =>
      if members.head?.map Prod.fst == some name then
        .view (members.map fun (member, type) => (fieldNames.idxOf member, type))
      else .viewField

private def sameCallInterfaceShape (expected actual : CallInterface) : Bool :=
  expected.argumentViews.length == actual.argumentViews.length &&
  expected.resultViews.length == actual.resultViews.length &&
  callAbiShape expected.argumentFields expected.argumentViews ==
    callAbiShape actual.argumentFields actual.argumentViews &&
  callAbiShape expected.resultFields expected.resultViews ==
    callAbiShape actual.resultFields actual.resultViews

private def interfaceMethods (name : Name) : CommandElabM (Array CallInterface) := do
  pure ((callInterfaceRegistry.getState (← getEnv)).filter (·.contract == name))

private structure InterfaceImplementation where
  contract : Name
  interface : Name
  deriving Inhabited

initialize interfaceImplementationRegistry : SimplePersistentEnvExtension
    InterfaceImplementation (Array InterfaceImplementation) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize controlRegistry : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

structure WitnessInfo where
  circuitName : Name
  sourceName : Name
  exportName : String
  outputName : String := ""
  observationArtifact? : Option String := none
  deriving Inhabited

/-- Exact source constants registered as Noctium module definitions. -/
structure ModuleSourceInfo where
  sourceName : Name
  definitionName : Name
  deriving Inhabited

/-- A module contract declaration retains only source roots. Compiler checks
re-expand these roots and rebuild their concrete circuits for each invocation. -/
structure ModuleBuildInfo where
  contractName : Name
  requestName : Name
  deriving Inhabited

structure ModuleCircuitBuildInfo where
  source : Modules.ModuleCircuitSource
  declarationName : Name
  programName : Name
  program : Helpers.Program
  circuit : Circuit
  signatureArtifact : Helpers.Specialization.SignatureArtifact

structure ModuleBuildOutput where
  specialized : Modules.SpecializedModule
  contract : Contract
  programs : List (Name × Name × Helpers.Program)
  circuits : List ModuleCircuitBuildInfo

initialize witnessRegistry : SimplePersistentEnvExtension WitnessInfo (Array WitnessInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

/-- Reuse checked witness compilations within this elaboration environment. -/
initialize checkedWitnesses : EnvExtension (NameMap Witness.Compiled) ←
  registerEnvExtension (pure {})

initialize moduleSourceRegistry : SimplePersistentEnvExtension ModuleSourceInfo (Array ModuleSourceInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize moduleBuildRegistry : SimplePersistentEnvExtension ModuleBuildInfo (Array ModuleBuildInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

declare_syntax_cat nltype
scoped syntax "Native" : nltype
scoped syntax "Bool" : nltype
scoped syntax "UInt" num : nltype
scoped syntax "UIntRange" num : nltype
scoped syntax "Bytes32" : nltype
scoped syntax "Bytes" num : nltype
scoped syntax "OpaqueBytes" : nltype
scoped syntax "JubjubScalar" : nltype
scoped syntax "JubjubPoint" : nltype
scoped syntax "Secp256k1Base" : nltype
scoped syntax "Secp256k1Scalar" : nltype
scoped syntax "Secp256k1Point" : nltype
scoped syntax "Secp256r1Base" : nltype
scoped syntax "Secp256r1Scalar" : nltype
scoped syntax "Secp256r1Point" : nltype
scoped syntax "Curve25519Base" : nltype
scoped syntax "Curve25519Scalar" : nltype
scoped syntax "Curve25519Point" : nltype

declare_syntax_cat nlexpr
scoped syntax ident : nlexpr
scoped syntax num : nlexpr
scoped syntax "true" : nlexpr
scoped syntax "false" : nlexpr
scoped syntax "let" ident ":=" nlexpr "in" nlexpr : nlexpr
scoped syntax "assertThen(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "add(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "mul(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "sub(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "inv(" nlexpr ")" : nlexpr
scoped syntax "copyValue(" nlexpr ")" : nlexpr
scoped syntax "uint(" num ")" : nlexpr
scoped syntax "cast(" nltype "," nlexpr ")" : nlexpr
scoped syntax "default(" nltype ")" : nlexpr
scoped syntax "disclose(" nlexpr ")" : nlexpr
scoped syntax "boolAnd(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "boolOr(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "andThen(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "orElse(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "boolXor(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "eq(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "ite(" nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "select(" nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "poseidon2(" num "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "persistentHash32(" nlexpr ")" : nlexpr
scoped syntax "sha256(" nlexpr ")" : nlexpr
scoped syntax "sha512(" nlexpr ")" : nlexpr
scoped syntax "keccak256(" nlexpr ")" : nlexpr
scoped syntax "secp256k1EcdsaVerify(" nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "secp256r1EcdsaVerify(" nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "jubjubSchnorrVerify(" "[" nlexpr,* "]" "," nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "ed25519Verify(" nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "secp256k1EthereumAddress(" nlexpr ")" : nlexpr
scoped syntax "reverseBytes32(" nlexpr ")" : nlexpr
scoped syntax "bytes(" num "," str ")" : nlexpr
scoped syntax "reverseBytes(" nlexpr ")" : nlexpr
scoped syntax "sliceBytes(" nlexpr "," num "," num ")" : nlexpr
scoped syntax "concatBytes(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "bytes32(" str ")" : nlexpr
scoped syntax "persistentHashVector32(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "persistentHashNative(" nlexpr ")" : nlexpr
scoped syntax "persistentHashNativeVector(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "transientHashNativeVector(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "shieldedOutputNonce(" nlexpr ")" : nlexpr
declare_syntax_cat nlcallvalue
scoped syntax nlexpr : nlcallvalue
scoped syntax ident ":=" "fields(" nlexpr,* ")" : nlcallvalue
scoped syntax "callCommitment(" ident "," str "," nlexpr ","
  "[" nlcallvalue,* "]" "," "[" nlcallvalue,* "]" ")" : nlexpr
scoped syntax "callCommitment(" ident "," ident "," str "," nlexpr ","
  "[" nlcallvalue,* "]" "," "[" nlcallvalue,* "]" ")" : nlexpr
scoped syntax "persistentHashPoint(" nlexpr ")" : nlexpr
scoped syntax "hashToCurve(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "toBytes32(" nlexpr ")" : nlexpr
scoped syntax "fromBytes32(" nltype "," nlexpr ")" : nlexpr
scoped syntax "fromBytes(" nltype "," nlexpr ")" : nlexpr
scoped syntax "serialize(" nlexpr "," num ")" : nlexpr
scoped syntax "deserialize(" nltype "," nlexpr ")" : nlexpr
scoped syntax "byteAt(" nlexpr "," num ")" : nlexpr
scoped syntax "degradeToNative(" nlexpr ")" : nlexpr
scoped syntax "jubjubScalarFromNative(" nlexpr ")" : nlexpr
scoped syntax "jubjubScalarToNative(" nlexpr ")" : nlexpr
scoped syntax "jubjubMulGenerator(" nlexpr ")" : nlexpr
scoped syntax "jubjubMul(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "jubjubAdd(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "jubjubNeg(" nlexpr ")" : nlexpr
scoped syntax "jubjubX(" nlexpr ")" : nlexpr
scoped syntax "jubjubY(" nlexpr ")" : nlexpr
scoped syntax "jubjubFromCoordinates(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "secp256k1Base(" num ")" : nlexpr
scoped syntax "secp256k1Scalar(" num ")" : nlexpr
scoped syntax "secp256k1Point(" num "," num ")" : nlexpr
scoped syntax "secp256k1Identity()" : nlexpr
scoped syntax "secp256r1Base(" num ")" : nlexpr
scoped syntax "secp256r1Scalar(" num ")" : nlexpr
scoped syntax "secp256r1Point(" num "," num ")" : nlexpr
scoped syntax "secp256r1Identity()" : nlexpr
scoped syntax "curve25519Base(" num ")" : nlexpr
scoped syntax "curve25519Scalar(" num ")" : nlexpr
scoped syntax "curve25519Point(" num "," num ")" : nlexpr
scoped syntax "curve25519Identity()" : nlexpr
scoped syntax "foreignAdd(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "foreignSub(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "foreignMul(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "foreignNeg(" nlexpr ")" : nlexpr
scoped syntax "foreignInv(" nlexpr ")" : nlexpr
scoped syntax "curveMul(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "curveMulGenerator(" nlexpr ")" : nlexpr
scoped syntax "curveX(" nlexpr ")" : nlexpr
scoped syntax "curveY(" nlexpr ")" : nlexpr
scoped syntax "curveFromCoordinates(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "foreignToBytes(" nlexpr ")" : nlexpr
scoped syntax "foreignFromBytes(" nltype "," nlexpr ")" : nlexpr

declare_syntax_cat nlcstmt
scoped syntax "public" ident ":" nltype : nlcstmt
scoped syntax "private" ident ":" nltype : nlcstmt
scoped syntax "let" ident ":" nltype ":=" nlexpr : nlcstmt
scoped syntax "assert" nlexpr : nlcstmt
scoped syntax "output" ident ":" nltype ":=" nlexpr : nlcstmt
scoped syntax (name := circuitCommand) "noctium_circuit" ident "where" nlcstmt* "end" : command

declare_syntax_cat nlstate
scoped syntax "cell" ident ":" nltype : nlstate
scoped syntax "sealed" "cell" ident ":" nltype : nlstate
scoped syntax "sealed" "cell" ident ":" "OpaqueString" : nlstate
declare_syntax_cat nlconstructorparam
scoped syntax ident ":" nltype : nlconstructorparam
scoped syntax ident ":" "OpaqueString" : nlconstructorparam
declare_syntax_cat nlconstructorinit
scoped syntax "initialize" ident ":=" nlexpr : nlconstructorinit
scoped syntax "initialize" ident ":=" str : nlconstructorinit
scoped syntax "constructor" "(" nlconstructorparam,* ")" "where" nlconstructorinit* "end" : nlstate
scoped syntax "map" ident ":" nltype "=>" nltype : nlstate
scoped syntax "counter" ident : nlstate
declare_syntax_cat nlcompositefield
scoped syntax ident ":" nltype : nlcompositefield
scoped syntax "cell" ident ":" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "set" ident ":" "struct" ident "{" nlcompositefield* "}" : nlstate
declare_syntax_cat nlmerklespec
scoped syntax num ("of" nltype)? : nlmerklespec
scoped syntax num "of" "struct" ident "{" nlcompositefield* "}" : nlmerklespec
scoped syntax "merkleTree" ident ":" nlmerklespec : nlstate
scoped syntax "historicMerkleTree" ident ":" nlmerklespec : nlstate
scoped syntax "tree" ident ":" nltype "=>" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax ident ident ":" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" nltype "=>" ident "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" ident "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax ident ident ":" nltype : nlstate
scoped syntax "tree" ident ":" nltype "=>" ident nltype : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" ident nltype : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" "Counter" : nlstate
scoped syntax "tree" ident ":" nltype "=>" "Counter" : nlstate
scoped syntax "set" ident ":" nltype : nlstate
scoped syntax "tree" ident ":" nltype "=>" "Set" nltype : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" "Set" nltype : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" "MerkleTree" nlmerklespec : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" "HistoricMerkleTree" nlmerklespec : nlstate
scoped syntax "tree" ident ":" nltype "=>" "MerkleTree" nlmerklespec : nlstate
scoped syntax "tree" ident ":" nltype "=>" "HistoricMerkleTree" nlmerklespec : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" nltype : nlstate

declare_syntax_cat nlleaves
scoped syntax "fields(" nlexpr,* ")" : nlleaves

declare_syntax_cat nlledgervalue
scoped syntax nlexpr : nlledgervalue
scoped syntax nlleaves : nlledgervalue

declare_syntax_cat nlpath
scoped syntax ident : nlpath
scoped syntax nlpath "[" nlexpr "]" : nlpath

declare_syntax_cat nlupdate
scoped syntax "claimContractCall" "(" nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "claimContractCall" "(" nlexpr "," nlexpr ")" : nlupdate
scoped syntax "mintShielded" "(" nlexpr "," nlexpr ")" : nlupdate
scoped syntax "receiveShieldedToMap" "(" ident "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "insertShieldedCoinSet" "(" ident "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "writeShieldedCoinCell" "(" ident "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "spendShieldedFromMap" "(" ident "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "sendShieldedFromMap" "(" ident "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "relayShieldedImmediate" "(" nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "mintUnshielded" "(" nlexpr "," nlexpr ")" : nlupdate
scoped syntax "incUnshieldedInputs" "(" nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "incUnshieldedOutputs" "(" nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "claimUnshieldedCoinSpend" "(" nlexpr "," nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "requireContractCaller" "(" nlexpr ")" : nlupdate
scoped syntax "checkpoint" : nlupdate
declare_syntax_cat nleventfield
scoped syntax ident ":=" nlexpr : nleventfield
scoped syntax "emitEvent" "(" ident ")" : nlupdate
scoped syntax "emitEvent" "(" ident "," nleventfield,+ ")" : nlupdate

declare_syntax_cat nleffect
scoped syntax nlupdate : nleffect
scoped syntax "when" nlexpr nlupdate : nleffect
scoped syntax "read" nlpath "as" ident : nleffect
scoped syntax "readSelf" "as" ident : nleffect
scoped syntax "member" nlpath "as" ident : nleffect
scoped syntax "checkRoot" nlpath "against" nlexpr "as" ident : nleffect
scoped syntax "tokenBalance(" nlexpr "," nlexpr ")" "as" ident : nleffect
scoped syntax "tokenBalanceLt(" nlexpr "," nlexpr "," nlexpr ")" "as" ident : nleffect
scoped syntax "tokenBalanceGt(" nlexpr "," nlexpr "," nlexpr ")" "as" ident : nleffect
scoped syntax "headOrDefault" nlpath "as" "(" ident "," ident ")" : nleffect
scoped syntax "when" nlexpr "headOrDefault" nlpath "as" "(" ident "," ident ")" : nleffect
scoped syntax ident nlpath "as" ident : nleffect
scoped syntax "readCaller" "as" "(" ident "," ident "," ident "," ident ")" : nleffect
scoped syntax "when" nlexpr "readCaller" "as" "(" ident "," ident "," ident "," ident ")" : nleffect
scoped syntax "increment" nlpath "by" nlexpr : nleffect
scoped syntax "decrement" nlpath "by" nlexpr : nleffect
scoped syntax "reset" nlpath : nleffect
scoped syntax "insertDefault" nlpath : nleffect
scoped syntax "resetHistory" nlpath : nleffect
scoped syntax "insertHash" nlpath ":=" nlexpr : nleffect
scoped syntax "insertField" nlpath ":=" nlexpr : nleffect
scoped syntax "require" nlexpr : nleffect
scoped syntax "absent" ident "[" nlexpr "]" : nleffect
scoped syntax "write" ident ":=" nlexpr : nleffect
scoped syntax "insert" ident "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "insert" ident "[" nlexpr "]" ":=" "emptyMap" : nleffect
scoped syntax "insert" ident "[" nlexpr "]" "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "write" ident "[" nlexpr "]" "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "insert" ident "[" nlexpr "]" ":=" nlleaves : nleffect
scoped syntax "write" ident "[" nlexpr "]" ":=" nlleaves : nleffect
scoped syntax "insert" ident "[" nlexpr "]" "[" nlexpr "]" ":=" nlleaves : nleffect
scoped syntax "write" ident "[" nlexpr "]" "[" nlexpr "]" ":=" nlleaves : nleffect
scoped syntax "pushFront" nlpath ":=" nlledgervalue : nleffect
scoped syntax "popFront" nlpath : nleffect
scoped syntax "remove" nlpath : nleffect
scoped syntax "blockTimeBefore(" nlexpr ")" "as" ident : nleffect
scoped syntax "blockTimeAfter(" nlexpr ")" "as" ident : nleffect
scoped syntax "counterLessThan" nlpath "against" nlexpr "as" ident : nleffect
scoped syntax "insert" nlpath : nleffect
scoped syntax "when" nlexpr "write" ident ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "insert" ident "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "require" nlexpr : nleffect
scoped syntax "when" nlexpr "read" nlpath "as" ident : nleffect
scoped syntax "when" nlexpr "readSelf" "as" ident : nleffect
scoped syntax "when" nlexpr "member" nlpath "as" ident : nleffect
scoped syntax "when" nlexpr "checkRoot" nlpath "against" nlexpr "as" ident : nleffect
scoped syntax "when" nlexpr "tokenBalance(" nlexpr "," nlexpr ")" "as" ident : nleffect
scoped syntax "when" nlexpr "tokenBalanceLt(" nlexpr "," nlexpr "," nlexpr ")" "as" ident : nleffect
scoped syntax "when" nlexpr "tokenBalanceGt(" nlexpr "," nlexpr "," nlexpr ")" "as" ident : nleffect
scoped syntax "when" nlexpr "counterLessThan" nlpath "against" nlexpr "as" ident : nleffect
scoped syntax "when" nlexpr ident nlpath "as" ident : nleffect
scoped syntax "when" nlexpr "increment" nlpath "by" nlexpr : nleffect
scoped syntax "when" nlexpr "decrement" nlpath "by" nlexpr : nleffect
scoped syntax "when" nlexpr "reset" nlpath : nleffect
scoped syntax "when" nlexpr "insertDefault" nlpath : nleffect
scoped syntax "when" nlexpr "resetHistory" nlpath : nleffect
scoped syntax "when" nlexpr "insertHash" nlpath ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "insertField" nlpath ":=" nlexpr : nleffect
scoped syntax "insertHashIndex" nlpath "at" nlexpr ":=" nlexpr : nleffect
scoped syntax "insertFieldIndex" nlpath "at" nlexpr ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "insertHashIndex" nlpath "at" nlexpr ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "insertFieldIndex" nlpath "at" nlexpr ":=" nlexpr : nleffect
scoped syntax "insertLeaf" nlpath ":=" nlledgervalue : nleffect
scoped syntax "when" nlexpr "insertLeaf" nlpath ":=" nlledgervalue : nleffect
scoped syntax "insertLeafIndex" nlpath "at" nlexpr ":=" nlledgervalue : nleffect
scoped syntax "when" nlexpr "insertLeafIndex" nlpath "at" nlexpr ":=" nlledgervalue : nleffect
scoped syntax "insertLeafDefault" nlpath "at" nlexpr : nleffect
scoped syntax "when" nlexpr "insertLeafDefault" nlpath "at" nlexpr : nleffect
scoped syntax "when" nlexpr "pushFront" nlpath ":=" nlledgervalue : nleffect
scoped syntax "when" nlexpr "popFront" nlpath : nleffect
scoped syntax "when" nlexpr "remove" nlpath : nleffect
scoped syntax "when" nlexpr "blockTimeBefore(" nlexpr ")" "as" ident : nleffect
scoped syntax "when" nlexpr "blockTimeAfter(" nlexpr ")" "as" ident : nleffect
scoped syntax "when" nlexpr "insert" nlpath : nleffect

declare_syntax_cat nlstatement
scoped syntax nleffect : nlstatement
scoped syntax "if" nlexpr "then" "{" nlstatement* "}" "else" "{" nlstatement* "}" : nlstatement

declare_syntax_cat nlreturn
scoped syntax "return" ident ":" nltype ":=" nlexpr : nlreturn
scoped syntax "returnMaybe" ident "as" "(" ident "," ident ")" : nlreturn
scoped syntax "return" ident : nlreturn

declare_syntax_cat nlentry
scoped syntax "entry" ident "uses" ident "where" nlstatement* nlreturn* "end" : nlentry
scoped syntax "entry" ident "uses" ident ident "[" ident,* "]" "where" nlstatement* nlreturn* "end" : nlentry
scoped syntax "entry" ident "from" ident "entry" str "end" : nlentry
scoped syntax (name := contractCommand) "noctium_contract" ident "where" nlstate* nlentry* "end" : command

declare_syntax_cat nlinterfacefield
scoped syntax ident ":" nltype : nlinterfacefield
declare_syntax_cat nlinterfacevalue
scoped syntax nlinterfacefield : nlinterfacevalue
scoped syntax ident ":=" "fields(" nlinterfacefield,* ")" : nlinterfacevalue
declare_syntax_cat nlinterfaceentry
scoped syntax "entry" ident "accepts" "[" nlinterfacevalue,* "]"
  "yields" "[" nlinterfacevalue,* "]" : nlinterfaceentry
scoped syntax (name := interfaceCommand) "noctium_interface" ident "where"
  nlinterfaceentry* "end" : command
scoped syntax (name := implementsCommand) "noctium_implements" ident "implements" ident : command

open scoped Noctium

private def readTy (stx : TSyntax `nltype) : CommandElabM Ty :=
  match stx with
  | `(nltype| Native) => pure .native
  | `(nltype| Bool) => pure .bool
  | `(nltype| UInt $bits:num) =>
    match ScalarPolicy.sized bits.getNat with
    | .ok (.uint maximum) => pure (.uint maximum)
    | .error message => throwErrorAt stx message
    | _ => throwErrorAt stx "invalid unsigned width"
  | `(nltype| UIntRange $exclusive:num) =>
    match ScalarPolicy.bounded exclusive.getNat with
    | .ok (.uint maximum) => pure (.uint maximum)
    | .error message => throwErrorAt stx message
    | _ => throwErrorAt stx "invalid unsigned range"
  | `(nltype| Bytes32) => pure (.bytes 32)
  | `(nltype| Bytes $length:num) => do
    if length.getNat > Noctium.maxBytesLength then
      throwErrorAt length s!"byte string length exceeds the maximum of {Noctium.maxBytesLength}"
    pure (.bytes length.getNat)
  | `(nltype| OpaqueBytes) => pure .opaqueBytes
  | `(nltype| JubjubScalar) => pure .jubjubScalar
  | `(nltype| JubjubPoint) => pure .jubjubPoint
  | `(nltype| Secp256k1Base) => pure (.foreign (.base .secp256k1))
  | `(nltype| Secp256k1Scalar) => pure (.foreign (.scalar .secp256k1))
  | `(nltype| Secp256k1Point) => pure (.foreign (.point .secp256k1))
  | `(nltype| Secp256r1Base) => pure (.foreign (.base .secp256r1))
  | `(nltype| Secp256r1Scalar) => pure (.foreign (.scalar .secp256r1))
  | `(nltype| Secp256r1Point) => pure (.foreign (.point .secp256r1))
  | `(nltype| Curve25519Base) => pure (.foreign (.base .curve25519))
  | `(nltype| Curve25519Scalar) => pure (.foreign (.scalar .curve25519))
  | `(nltype| Curve25519Point) => pure (.foreign (.point .curve25519))
  | _ => throwErrorAt stx "unsupported Noctium type"

private def tyTerm : Ty → CommandElabM (TSyntax `term)
  | .native => `(Noctium.Ty.native)
  | .bool => `(Noctium.Ty.bool)
  | .uint maximum => `(Noctium.Ty.uint $(⟨Syntax.mkNumLit (toString maximum)⟩))
  | .bytes len => `(Noctium.Ty.bytes $(⟨Syntax.mkNumLit (toString len)⟩))
  | .opaqueBytes => `(Noctium.Ty.opaqueBytes)
  | .jubjubScalar => `(Noctium.Ty.jubjubScalar)
  | .jubjubPoint => `(Noctium.Ty.jubjubPoint)
  | .foreign (.base .secp256k1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.base Noctium.Foreign.Curve.secp256k1))
  | .foreign (.scalar .secp256k1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.secp256k1))
  | .foreign (.point .secp256k1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.point Noctium.Foreign.Curve.secp256k1))
  | .foreign (.base .secp256r1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.base Noctium.Foreign.Curve.secp256r1))
  | .foreign (.scalar .secp256r1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.secp256r1))
  | .foreign (.point .secp256r1) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.point Noctium.Foreign.Curve.secp256r1))
  | .foreign (.base .curve25519) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.base Noctium.Foreign.Curve.curve25519))
  | .foreign (.scalar .curve25519) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.scalar Noctium.Foreign.Curve.curve25519))
  | .foreign (.point .curve25519) => `(Noctium.Ty.foreign (Noctium.Foreign.Kind.point Noctium.Foreign.Curve.curve25519))

private def elaborateInterfaceValues (values : Array (TSyntax `nlinterfacevalue)) :
    CommandElabM (List (String × Ty) × List (String × List (String × Ty))) := do
  let mut fields : List (String × Ty) := []
  let mut views : List (String × List (String × Ty)) := []
  let mut labels : List String := []
  for value in values do
    let (label, members, isView) ← match value with
      | `(nlinterfacevalue| $field:nlinterfacefield) =>
        match field with
        | `(nlinterfacefield| $name:ident : $type:nltype) =>
          pure (name.getId.toString, [(name.getId.toString, ← readTy type)], Bool.false)
        | _ => throwErrorAt field "invalid contract interface field"
      | `(nlinterfacevalue| $label:ident := fields($items:nlinterfacefield,*)) => do
        unless items.getElems.size > 0 do
          throwErrorAt value "contract interface views must contain at least one field"
        let members : List (String × Ty) ← items.getElems.toList.mapM fun
            (item : TSyntax `nlinterfacefield) => do
          let `(nlinterfacefield| $name:ident : $type:nltype) := item
            | throwErrorAt item "invalid contract interface view field"
          pure (name.getId.toString, ← readTy type)
        pure (label.getId.toString, members, Bool.true)
      | _ => throwErrorAt value "invalid contract interface value"
    if labels.contains label then
      throwErrorAt value s!"duplicate contract interface value '{label}'"
    let memberNames := members.map Prod.fst
    unless uniqueNames memberNames do
      throwErrorAt value "duplicate contract interface field"
    if memberNames.any (fun name => fields.any (·.1 == name)) then
      throwErrorAt value "contract interface fields must have unique names"
    labels := label :: labels
    fields := fields ++ members
    if isView then views := views ++ [(label, members)]
  pure (fields, views)

private def foreignCurveTerm : Foreign.Curve → CommandElabM (TSyntax `term)
  | .secp256k1 => `(Noctium.Foreign.Curve.secp256k1)
  | .secp256r1 => `(Noctium.Foreign.Curve.secp256r1)
  | .curve25519 => `(Noctium.Foreign.Curve.curve25519)

private def foreignKindTerm : Foreign.Kind → CommandElabM (TSyntax `term)
  | .base curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.Kind.base $curve)
  | .scalar curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.Kind.scalar $curve)
  | .point curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.Kind.point $curve)

private def foreignFieldKindTerm : Foreign.FieldKind → CommandElabM (TSyntax `term)
  | .base curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.FieldKind.base $curve)
  | .scalar curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.FieldKind.scalar $curve)

private def foreignUnaryOpTerm : Foreign.UnaryOp → CommandElabM (TSyntax `term)
  | .neg kind => do
    let kind ← foreignKindTerm kind
    `(Noctium.Foreign.UnaryOp.neg $kind)
  | .inv kind => do
    let kind ← foreignFieldKindTerm kind
    `(Noctium.Foreign.UnaryOp.inv $kind)
  | .mulGenerator curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.mulGenerator $curve)
  | .x curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.x $curve)
  | .y curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.UnaryOp.y $curve)

private def foreignBinaryOpTerm : Foreign.BinaryOp → CommandElabM (TSyntax `term)
  | .add kind => do
    let kind ← foreignKindTerm kind
    `(Noctium.Foreign.BinaryOp.add $kind)
  | .sub kind => do
    let kind ← foreignKindTerm kind
    `(Noctium.Foreign.BinaryOp.sub $kind)
  | .mul kind => do
    let kind ← foreignFieldKindTerm kind
    `(Noctium.Foreign.BinaryOp.mul $kind)
  | .ecMul curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.BinaryOp.ecMul $curve)
  | .fromCoordinates curve => do
    let curve ← foreignCurveTerm curve
    `(Noctium.Foreign.BinaryOp.fromCoordinates $curve)

private def stringTerm (value : String) : TSyntax `term := ⟨Syntax.mkStrLit value⟩
private def natTerm (value : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString value)⟩

private def foreignPointExprTerm (stx : Syntax) (curve : Foreign.Curve)
    (x y : Nat) : CommandElabM (TSyntax `term) := do
  match Foreign.encodePoint curve (.affine x y) with
  | .ok _ => pure ()
  | .error message => throwErrorAt stx message
  let curve ← foreignCurveTerm curve
  let x := natTerm x
  let y := natTerm y
  `(Noctium.Expr.foreignPoint $curve (Noctium.Foreign.Point.affine $x $y))

private partial def natListTerm : List Nat → CommandElabM (TSyntax `term)
  | [] => `(([] : List Nat))
  | value :: rest => do
    let tail ← natListTerm rest
    `($(natTerm value) :: $tail)

private partial def exprListTerm : List (TSyntax `term) → CommandElabM (TSyntax `term)
  | [] => `(([] : List (Noctium.Expr (Noctium.Ty.bytes 32))))
  | value :: rest => do
    let tail ← exprListTerm rest
    `($value :: $tail)

private partial def pathKeyListTerm : List (TSyntax `term) → CommandElabM (TSyntax `term)
  | [] => `(([] : List Noctium.PathKey))
  | value :: rest => do
    let tail ← pathKeyListTerm rest
    `($value :: $tail)

private partial def stringListTerm : List (TSyntax `term) → CommandElabM (TSyntax `term)
  | [] => `(([] : List String))
  | value :: rest => do
    let tail ← stringListTerm rest
    `($value :: $tail)

private partial def nativeExprListTerm : List (TSyntax `term) → CommandElabM (TSyntax `term)
  | [] => `(([] : List (Noctium.Expr Noctium.Ty.native)))
  | value :: rest => do
    let tail ← nativeExprListTerm rest
    `($value :: $tail)

private def spanTerm (stx : Syntax) : CommandElabM (TSyntax `term) := do
  let fileMap ← getFileMap
  let pos := fileMap.toPosition (stx.getPos?.getD 0)
  let file ← getFileName
  `({ file := $(stringTerm file), line := $(natTerm pos.line),
      column := $(natTerm (pos.column + 1)) : Noctium.SourceSpan })

private abbrev Bindings := List (String × Ty × TSyntax `term)

private partial def syntaxIdentifiers : Syntax → List String
  | .ident _ _ name _ => [name.toString]
  | .node _ _ children => children.toList.flatMap syntaxIdentifiers
  | _ => []

private def freshLazyBooleanName (env : Bindings) (stx : TSyntax `nlexpr) : String := Id.run do
  let usedNames := env.map (fun binding => binding.1) ++ syntaxIdentifiers stx.raw
  let baseName := s!"$lazyBool{stx.raw.getPos?.getD 0}"
  let mut candidate := baseName
  let mut suffix := 0
  while usedNames.contains candidate do
    candidate := s!"{baseName}_local{suffix}"
    suffix := suffix + 1
  return candidate

private def callExpressions (role : String) (ordered : List (String × Ty))
    (groups : List (String × List (String × Ty)))
    (values : Array (TSyntax `nlcallvalue)) (site : Syntax) :
    CommandElabM (List (TSyntax `nlexpr × Ty)) := do
  let mut views := groups
  let grouped := views.flatMap fun (_, fields) => fields.map Prod.fst
  let mut scalars := ordered.filter fun (name, _) => !grouped.contains name
  let mut supplied := []
  for result in values do
    match result with
    | `(nlcallvalue| $label:ident := fields($values,*)) =>
      let labelName := label.getId.toString
      let some fields := views.lookup labelName
        | throwErrorAt label "unknown or repeated aggregate call {role} '{labelName}'"
      if fields.length != values.getElems.size then
        throwErrorAt result "callCommitment field count does not match aggregate {role} '{labelName}'"
      supplied := supplied ++ ((fields.zip values.getElems.toList).map fun ((name, ty), expr) =>
        (name, expr, ty))
      views := views.filter (·.1 != labelName)
    | `(nlcallvalue| $value:nlexpr) =>
      let (name, ty) :: rest := scalars
        | throwErrorAt site "callCommitment {role} count does not match the callee"
      supplied := (name, value, ty) :: supplied
      scalars := rest
    | _ => throwErrorAt result "unsupported call value"
  unless views.isEmpty && scalars.isEmpty do
    throwErrorAt site "callCommitment {role} count does not match the callee"
  ordered.mapM fun (name, _) => do
    let some value := supplied.lookup name
      | throwErrorAt site "missing committed {role} field '{name}'"
    pure value

private def coerceExpression (stx : Syntax) (found target : Ty) (value : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  if found == target then return value
  match found, target with
  | .uint m, .uint n =>
    unless m ≤ n do throwErrorAt stx "Noctium expression type mismatch; use an explicit narrowing cast"
    `(Noctium.Expr.cast $(← tyTerm target) $value)
  | .uint _, .native => `(Noctium.Expr.cast Noctium.Ty.native $value)
  | _, _ => throwErrorAt stx "Noctium expression type mismatch"

private def commonType (stx : Syntax) (left right : Ty) : CommandElabM Ty := do
  if left == right then return left
  match left, right with
  | .uint m, .uint n => pure (.uint (max m n))
  | .native, .uint _ | .uint _, .native => pure .native
  | _, _ => throwErrorAt stx "Noctium expression type mismatch"

private def wireCodecTerm (type : Ty) : CommandElabM (TSyntax `term) := do
  `((Noctium.Wire.scalarCodec $(← tyTerm type)).get (by decide))

/-- A new partial scalar operation must execute even beneath a total wrapper.
Mark every subtraction conservatively, including total native-field subtraction. -/
private partial def hasPartialScalar (stx : TSyntax `nlexpr) : _root_.Bool :=
  match stx with
  | `(nlexpr| cast($_:nltype, $_:nlexpr)) => Bool.true
  | `(nlexpr| sub($_:nlexpr, $_:nlexpr)) => Bool.true
  | `(nlexpr| inv($_:nlexpr)) => Bool.true
  | `(nlexpr| fromBytes32($_:nltype, $_:nlexpr))
  | `(nlexpr| deserialize($_:nltype, $_:nlexpr)) => Bool.true
  | `(nlexpr| serialize($value, $_:num)) => hasPartialScalar value
  | `(nlexpr| fromBytes($_:nltype, $value:nlexpr)) => hasPartialScalar value
  | `(nlexpr| assertThen($_:nlexpr, $_:nlexpr)) => Bool.true
  | `(nlexpr| let $_:ident := $value:nlexpr in $body:nlexpr) =>
    hasPartialScalar value || hasPartialScalar body
  | `(nlexpr| disclose($value)) => hasPartialScalar value
  | `(nlexpr| add($a, $b)) | `(nlexpr| mul($a, $b))
  | `(nlexpr| eq($a, $b)) | `(nlexpr| boolAnd($a, $b))
  | `(nlexpr| boolOr($a, $b)) | `(nlexpr| andThen($a, $b))
  | `(nlexpr| orElse($a, $b)) | `(nlexpr| boolXor($a, $b))
  | `(nlexpr| poseidon2($_:num, $a, $b)) =>
    hasPartialScalar a || hasPartialScalar b
  | `(nlexpr| persistentHash32($value)) => hasPartialScalar value
  | `(nlexpr| shieldedOutputNonce($value)) => hasPartialScalar value
  | `(nlexpr| sha256($value))
  | `(nlexpr| sha512($value)) | `(nlexpr| keccak256($value)) => hasPartialScalar value
  | `(nlexpr| bytes($_:num, $_:str)) => Bool.false
  | `(nlexpr| copyValue($value)) | `(nlexpr| reverseBytes($value)) => hasPartialScalar value
  | `(nlexpr| sliceBytes($value, $_:num, $_:num)) => Bool.true
  | `(nlexpr| concatBytes($left, $right)) =>
    hasPartialScalar left || hasPartialScalar right
  | `(nlexpr| reverseBytes32($value)) => hasPartialScalar value
  | `(nlexpr| persistentHashVector32([$values,*])) =>
    values.getElems.toList.any hasPartialScalar
  | `(nlexpr| persistentHashNative($value)) => hasPartialScalar value
  | `(nlexpr| persistentHashNativeVector([$values,*])) =>
    values.getElems.toList.any hasPartialScalar
  | `(nlexpr| callCommitment($_:ident, $_:str, $opening, [$inputs,*], [$outputs,*]))
  | `(nlexpr| callCommitment($_:ident, $_:ident, $_:str, $opening, [$inputs,*], [$outputs,*])) =>
    let partialValue (value : TSyntax `nlcallvalue) :=
      match value with
      | `(nlcallvalue| $value:nlexpr) => hasPartialScalar value
      | `(nlcallvalue| $_:ident := fields($values,*)) => values.getElems.any hasPartialScalar
      | _ => Bool.true
    hasPartialScalar opening || inputs.getElems.any partialValue || outputs.getElems.any partialValue
  | `(nlexpr| transientHashNativeVector([$values,*])) =>
    values.getElems.toList.any hasPartialScalar
  | `(nlexpr| persistentHashPoint($point)) => hasPartialScalar point
  | `(nlexpr| hashToCurve([$values,*])) => Bool.true
  | `(nlexpr| toBytes32($value)) => hasPartialScalar value
  | `(nlexpr| byteAt($value, $_:num)) => hasPartialScalar value
  | `(nlexpr| degradeToNative($value)) => hasPartialScalar value
  | `(nlexpr| jubjubScalarFromNative($value))
  | `(nlexpr| jubjubScalarToNative($value))
  | `(nlexpr| jubjubMulGenerator($value))
  | `(nlexpr| jubjubNeg($value))
  | `(nlexpr| jubjubX($value))
  | `(nlexpr| jubjubY($value)) => hasPartialScalar value
  | `(nlexpr| jubjubMul($point, $scalar))
  | `(nlexpr| jubjubAdd($point, $scalar)) =>
    hasPartialScalar point || hasPartialScalar scalar
  | `(nlexpr| jubjubFromCoordinates($_:nlexpr, $_:nlexpr)) => Bool.true
  | `(nlexpr| foreignAdd($_:nlexpr, $_:nlexpr))
  | `(nlexpr| foreignSub($_:nlexpr, $_:nlexpr))
  | `(nlexpr| foreignMul($_:nlexpr, $_:nlexpr))
  | `(nlexpr| foreignNeg($_:nlexpr))
  | `(nlexpr| foreignInv($_:nlexpr))
  | `(nlexpr| curveMul($_:nlexpr, $_:nlexpr))
  | `(nlexpr| curveMulGenerator($_:nlexpr))
  | `(nlexpr| curveX($_:nlexpr))
  | `(nlexpr| curveY($_:nlexpr))
  | `(nlexpr| curveFromCoordinates($_:nlexpr, $_:nlexpr))
  | `(nlexpr| foreignToBytes($_:nlexpr))
  | `(nlexpr| foreignFromBytes($_:nltype, $_:nlexpr))
  | `(nlexpr| secp256k1EcdsaVerify($_:nlexpr, $_:nlexpr, $_:nlexpr, $_:nlexpr))
  | `(nlexpr| secp256r1EcdsaVerify($_:nlexpr, $_:nlexpr, $_:nlexpr, $_:nlexpr))
  | `(nlexpr| ed25519Verify($_:nlexpr, $_:nlexpr, $_:nlexpr, $_:nlexpr))
  | `(nlexpr| secp256k1EthereumAddress($_:nlexpr)) => Bool.true
  | `(nlexpr| jubjubSchnorrVerify([$messages,*], $_:nlexpr, $_:nlexpr, $_:nlexpr)) => Bool.true
  | `(nlexpr| select($c, $a, $b)) | `(nlexpr| ite($c, $a, $b)) =>
    hasPartialScalar c || hasPartialScalar a || hasPartialScalar b
  | _ => Bool.false

private partial def expression (env : Bindings) (stx : TSyntax `nlexpr) :
    CommandElabM (Ty × TSyntax `term) := do
  match stx with
  | `(nlexpr| $id:ident) =>
    match env.find? (fun p => p.1 == id.getId.toString) with
    | some (_, ty, value) => pure (ty, value)
    | none => throwErrorAt id "unknown Noctium value '{id.getId}'"
  | `(nlexpr| $n:num) => pure (.native, ← `(Noctium.Expr.native $n))
  | `(nlexpr| true) => pure (.bool, ← `(Noctium.Expr.bool Bool.true))
  | `(nlexpr| false) => pure (.bool, ← `(Noctium.Expr.bool Bool.false))
  | `(nlexpr| let $id:ident := $value:nlexpr in $body:nlexpr) => do
    let (valueTy, value) ← expression env value
    let typeTerm ← tyTerm valueTy
    let valueRef ← `(Noctium.Expr.ref (ty := $typeTerm) $(stringTerm id.getId.toString))
    let bodyEnv := (id.getId.toString, valueTy, valueRef) :: env
    let (bodyTy, body) ← expression bodyEnv body
    pure (bodyTy, ← `(Noctium.Expr.letE $(stringTerm id.getId.toString) $value $body))
  | `(nlexpr| assertThen($condition, $body)) => do
    let condition ← expected env condition .bool
    let (bodyTy, body) ← expression env body
    pure (bodyTy, ← `(Noctium.Expr.assertE $condition $body))
  | `(nlexpr| uint($n:num)) =>
    match ScalarPolicy.validate (.uint n.getNat) with
    | .error message => throwErrorAt stx message
    | .ok _ => pure (.uint n.getNat, ← `(Noctium.Expr.uint $n $n))
  | `(nlexpr| cast($target:nltype, $value:nlexpr)) =>
    let target ← readTy target
    let (source, value) ← expression env value
    if target.isOpaqueBytes || source.isOpaqueBytes then
      throwErrorAt stx "OpaqueBytes do not support scalar casts"
    if target.isJubjub || source.isJubjub || target.isForeign || source.isForeign then
      throwErrorAt stx "curve values require explicit typed conversions"
    pure (target, ← `(Noctium.Expr.cast $(← tyTerm target) $value))
  | `(nlexpr| default($target:nltype)) =>
    let target ← readTy target
    match target with
    | .native => pure (.native, ← `(Noctium.Expr.native 0))
    | .bool => pure (.bool, ← `(Noctium.Expr.bool Bool.false))
    | .uint maximum => pure (target, ← `(Noctium.Expr.uint $(natTerm maximum) 0))
    | .bytes _ => throwErrorAt stx "byte strings have no scalar default expression"
    | .opaqueBytes => throwErrorAt stx "OpaqueBytes have no generic default expression"
    | .jubjubScalar | .jubjubPoint => throwErrorAt stx "Jubjub values have no generic default expression"
    | .foreign _ => throwErrorAt stx "foreign values have no generic default expression"
  | `(nlexpr| disclose($value)) =>
    let (ty, value) ← expression env value
    pure (ty, ← `(Noctium.Expr.disclose $(← spanTerm stx) $value))
  | `(nlexpr| add($a, $b)) =>
    arithmetic env stx .add a b
  | `(nlexpr| mul($a, $b)) =>
    arithmetic env stx .mul a b
  | `(nlexpr| sub($a, $b)) =>
    arithmetic env stx .sub a b
  | `(nlexpr| inv($value)) => do
    let (ty, value) ← expression env value
    unless ty == .native || ty == .jubjubScalar do
      throwErrorAt stx "inv accepts only Native and JubjubScalar values"
    pure (ty, ← `(Noctium.Expr.inv $value))
  | `(nlexpr| toBytes32($value)) => do
    let (source, value) ← expression env value
    unless source == .native || source == .jubjubScalar || source == .jubjubPoint do
      throwErrorAt stx "toBytes32 accepts only Native, JubjubScalar or JubjubPoint"
    pure (.bytes 32, ← `(Noctium.Expr.toBytes32 $value))
  | `(nlexpr| fromBytes32($target:nltype, $value)) => do
    let target ← readTy target
    unless target == .native || target == .jubjubScalar || target == .jubjubPoint do
      throwErrorAt stx "fromBytes32 supports only Native, JubjubScalar or JubjubPoint"
    let value ← expected env value (.bytes 32)
    pure (target, ← `(Noctium.Expr.fromBytes32 (target := $(← tyTerm target)) $value))
  | `(nlexpr| fromBytes($target:nltype, $value)) => do
    let target ← readTy target
    unless target == .native || target == .jubjubScalar do
      throwErrorAt stx "fromBytes supports only Native and JubjubScalar"
    let (valueTy, value) ← expression env value
    let .bytes length := valueTy
      | throwErrorAt stx "fromBytes requires a Bytes expression"
    if length > maxBytesLength then
      throwErrorAt stx s!"byte string length exceeds the maximum of {maxBytesLength}"
    pure (target, ← `(Noctium.Expr.fromBytes (target := $(← tyTerm target)) $value))
  | `(nlexpr| serialize($value, $size:num)) => do
    let (ty, value) ← expression env value
    let some width := Wire.scalarWidth ty
      | throwErrorAt stx "serialize requires a scalar or fixed bytes"
    let length := size.getNat
    unless width ≤ length && length ≤ maxBytesLength do
      throwErrorAt size s!"serialize requires a byte length from {width} through {maxBytesLength}"
    let codec ← wireCodecTerm ty
    pure (.bytes length, ← `(Noctium.Wire.ScalarCodec.serialize $codec $value
      $(natTerm length) (by decide)))
  | `(nlexpr| deserialize($target:nltype, $value)) => do
    let ty ← readTy target
    let some width := Wire.scalarWidth ty
      | throwErrorAt target "deserialize requires a scalar or fixed bytes"
    let (sourceTy, value) ← expression env value
    let .bytes length := sourceTy | throwErrorAt stx "deserialize requires a Bytes expression"
    unless width ≤ length do
      throwErrorAt stx s!"deserialize requires at least {width} bytes"
    pure (ty, ← `(Noctium.Wire.ScalarCodec.deserialize $(← wireCodecTerm ty) $value))
  | `(nlexpr| byteAt($value, $index:num)) => do
    let (valueTy, value) ← expression env value
    let .bytes length := valueTy
      | throwErrorAt stx "byteAt requires a Bytes expression"
    unless index.getNat < length do
      throwErrorAt index s!"byte index must be less than the byte string length {length}"
    pure (.uint 255, ← `(Noctium.Expr.bytesAt $value $(natTerm index.getNat)))
  | `(nlexpr| eq($a, $b)) =>
    let (ta, a) ← expression env a
    let (tb, b) ← expression env b
    if ta.isBytes || tb.isBytes then do
      if ta == .bytes 32 || tb == .bytes 32 then do
        unless ta == .bytes 32 && tb == .bytes 32 do
          throwErrorAt stx "Bytes32 equality requires two Bytes32 expressions"
        let aHigh ← `(Noctium.Expr.bytesField $a 0)
        let bHigh ← `(Noctium.Expr.bytesField $b 0)
        let aLow ← `(Noctium.Expr.bytesField $a 1)
        let bLow ← `(Noctium.Expr.bytesField $b 1)
        let highEqual ← `(Noctium.Expr.eq $aHigh $bHigh)
        let lowEqual ← `(Noctium.Expr.eq $aLow $bLow)
        let falseValue ← `(Noctium.Expr.bool Bool.false)
        pure (.bool, ← `(Noctium.Expr.select $highEqual $lowEqual $falseValue))
      else do
        let .bytes length := ta
          | throwErrorAt stx "byte equality requires two same-length Bytes expressions"
        unless tb == .bytes length do
          throwErrorAt stx "byte equality requires two same-length Bytes expressions"
        if length == 0 then do
          let usedNames := env.map (fun binding => binding.1)
          let mut index := 0
          let mut leftName := s!"$byteEq{index}"
          while usedNames.contains leftName do
            index := index + 1
            leftName := s!"$byteEq{index}"
          index := index + 1
          let mut rightName := s!"$byteEq{index}"
          while usedNames.contains rightName || rightName == leftName do
            index := index + 1
            rightName := s!"$byteEq{index}"
          pure (.bool, ← `(Noctium.Expr.letE $(stringTerm leftName) $a
            (Noctium.Expr.letE $(stringTerm rightName) $b (Noctium.Expr.bool Bool.true))))
        else do
          let mut equal ← `(Noctium.Expr.bool Bool.true)
          for chunk in List.range ((length + 30) / 31) do
            let aField ← `(Noctium.Expr.bytesField $a $(natTerm chunk))
            let bField ← `(Noctium.Expr.bytesField $b $(natTerm chunk))
            let chunkEqual ← `(Noctium.Expr.eq $aField $bField)
            equal ← `(Noctium.Expr.select $chunkEqual $equal (Noctium.Expr.bool Bool.false))
          pure (.bool, equal)
    else do
      let ty ← commonType stx ta tb
      let a ← coerceExpression stx ta ty a
      let b ← coerceExpression stx tb ty b
      pure (.bool, ← `(Noctium.Expr.eq $a $b))
  | `(nlexpr| boolAnd($left, $right)) => do
    let left ← expected env left .bool
    let right ← expected env right .bool
    pure (.bool, ← `(Noctium.Expr.boolAnd $left $right))
  | `(nlexpr| boolOr($left, $right)) => do
    let left ← expected env left .bool
    let right ← expected env right .bool
    pure (.bool, ← `(Noctium.Expr.boolOr $left $right))
  | `(nlexpr| andThen($left, $right)) => do
    let left ← expected env left .bool
    let (rightTy, right) ← expression env right
    unless rightTy == .bool do throwErrorAt stx "andThen requires a Bool right operand"
    let name := freshLazyBooleanName env stx
    let leftRef ← `(Noctium.Expr.ref (ty := Noctium.Ty.bool) $(stringTerm name))
    let safeRight ← `(Noctium.GuardedExpression.totalize $leftRef $right)
    let falseValue ← `(Noctium.Expr.bool Bool.false)
    pure (.bool, ← `(Noctium.Expr.letE $(stringTerm name) $left
      (Noctium.Expr.select $leftRef $safeRight $falseValue)))
  | `(nlexpr| orElse($left, $right)) => do
    let left ← expected env left .bool
    let (rightTy, right) ← expression env right
    unless rightTy == .bool do throwErrorAt stx "orElse requires a Bool right operand"
    let name := freshLazyBooleanName env stx
    let leftRef ← `(Noctium.Expr.ref (ty := Noctium.Ty.bool) $(stringTerm name))
    let inactiveRightGuard ← `(Noctium.Expr.eq $leftRef (Noctium.Expr.bool Bool.false))
    let safeRight ← `(Noctium.GuardedExpression.totalize $inactiveRightGuard $right)
    let trueValue ← `(Noctium.Expr.bool Bool.true)
    pure (.bool, ← `(Noctium.Expr.letE $(stringTerm name) $left
      (Noctium.Expr.select $leftRef $trueValue $safeRight)))
  | `(nlexpr| boolXor($left, $right)) => do
    let left ← expected env left .bool
    let right ← expected env right .bool
    pure (.bool, ← `(Noctium.Expr.boolXor $left $right))
  | `(nlexpr| select($c, $a, $b)) =>
    let c ← expected env c .bool
    let (ta, a) ← expression env a
    let (tb, b) ← expression env b
    let ty ← commonType stx ta tb
    let a ← coerceExpression stx ta ty a
    let b ← coerceExpression stx tb ty b
    pure (ty, ← `(Noctium.Expr.select $c $a $b))
  | `(nlexpr| ite($condition, $thenValue, $elseValue)) => do
    let condition ← expected env condition .bool
    let (thenTy, thenValue) ← expression env thenValue
    let (elseTy, elseValue) ← expression env elseValue
    let ty ← commonType stx thenTy elseTy
    let thenValue ← coerceExpression stx thenTy ty thenValue
    let elseValue ← coerceExpression stx elseTy ty elseValue
    let name := freshLazyBooleanName env stx
    let conditionRef ← `(Noctium.Expr.ref (ty := Noctium.Ty.bool) $(stringTerm name))
    let inactiveGuard ← `(Noctium.Expr.eq $conditionRef (Noctium.Expr.bool Bool.false))
    let safeThen ← `(Noctium.GuardedExpression.totalize $conditionRef $thenValue)
    let safeElse ← `(Noctium.GuardedExpression.totalize $inactiveGuard $elseValue)
    pure (ty, ← `(Noctium.Expr.letE $(stringTerm name) $condition
      (Noctium.Expr.select $conditionRef $safeThen $safeElse)))
  | `(nlexpr| poseidon2($domain:num, $a, $b)) =>
    let a ← expected env a .native
    let b ← expected env b .native
    pure (.native, ← `(Noctium.Expr.poseidon2 $domain $a $b))
  | `(nlexpr| persistentHash32($value)) => do
    let (valueTy, value) ← expression env value
    unless valueTy == .bytes 32 do
      throwErrorAt stx "persistentHash32 requires a Bytes32 expression"
    pure (.bytes 32, ← `(Noctium.Expr.persistentHash32 $value))
  | `(nlexpr| sha256($value)) => do
    let (valueTy, value) ← expression env value
    let .bytes _ := valueTy
      | throwErrorAt stx "sha256 requires a Bytes expression"
    pure (.bytes 32, ← `(Noctium.Expr.sha256 $value))
  | `(nlexpr| sha512($value)) => do
    let (valueTy, value) ← expression env value
    let .bytes _ := valueTy
      | throwErrorAt stx "sha512 requires a Bytes expression"
    pure (.bytes 64, ← `(Noctium.Expr.sha512 $value))
  | `(nlexpr| keccak256($value)) => do
    let (valueTy, value) ← expression env value
    match valueTy with
    | .bytes _ => pure (.bytes 32, ← `(Noctium.Expr.keccak256 $value))
    | .foreign (.point .secp256k1) =>
      pure (.bytes 32, ← `(Noctium.Expr.keccak256Secp256k1Point $value))
    | .foreign (.point _) => throwErrorAt stx "keccak256 point overload supports Secp256k1Point"
    | _ => throwErrorAt stx "keccak256 requires a Bytes or Secp256k1Point expression"
  | `(nlexpr| secp256k1EcdsaVerify($msgHash, $r, $s, $pk)) => do
    let msgHash ← expected env msgHash (.bytes 32)
    let r ← expected env r (.foreign (.scalar .secp256k1))
    let s ← expected env s (.foreign (.scalar .secp256k1))
    let pk ← expected env pk (.foreign (.point .secp256k1))
    pure (.bool, ← `(Noctium.Crypto.secp256k1EcdsaVerify $msgHash $r $s $pk))
  | `(nlexpr| secp256r1EcdsaVerify($msgHash, $r, $s, $pk)) => do
    let msgHash ← expected env msgHash (.bytes 32)
    let r ← expected env r (.foreign (.scalar .secp256r1))
    let s ← expected env s (.foreign (.scalar .secp256r1))
    let pk ← expected env pk (.foreign (.point .secp256r1))
    pure (.bool, ← `(Noctium.Crypto.secp256r1EcdsaVerify $msgHash $r $s $pk))
  | `(nlexpr| jubjubSchnorrVerify([$message,*], $announcement, $response, $pk)) => do
    let sourceMessages := message.getElems.toList
    unless sourceMessages.length + 4 ≤ 1024 do
      throwErrorAt stx "jubjubSchnorrVerify challenge input exceeds 1024 Native fields"
    let messages ← sourceMessages.mapM fun value => expected env value .native
    let messageList ← nativeExprListTerm messages
    let announcement ← expected env announcement .jubjubPoint
    let response ← expected env response .native
    let pk ← expected env pk .jubjubPoint
    pure (.bool, ← `(Noctium.Crypto.jubjubSchnorrVerify $messageList $announcement $response $pk))
  | `(nlexpr| ed25519Verify($message, $r, $s, $pk)) => do
    let (messageTy, message) ← expression env message
    let .bytes length := messageTy
      | throwErrorAt stx "ed25519Verify requires a Bytes message"
    unless length + 64 ≤ 1024 do
      throwErrorAt stx "ed25519Verify input exceeds 1024 bytes"
    let r ← expected env r (.foreign (.point .curve25519))
    let s ← expected env s (.foreign (.scalar .curve25519))
    let pk ← expected env pk (.foreign (.point .curve25519))
    pure (.bool, ← `(Noctium.Crypto.ed25519Verify $message $r $s $pk))
  | `(nlexpr| secp256k1EthereumAddress($pk)) => do
    let pk ← expected env pk (.foreign (.point .secp256k1))
    pure (.bytes 20, ← `(Noctium.Crypto.secp256k1EthereumAddress $pk))
  | `(nlexpr| bytes($length:num, $literal:str)) => do
    let length := length.getNat
    if length > Noctium.maxBytesLength then
      throwErrorAt stx s!"byte string length exceeds the maximum of {Noctium.maxBytesLength}"
    let bytes := literal.getString.toUTF8.data.toList.map UInt8.toNat
    if bytes.length > length then
      throwErrorAt literal s!"byte string literal exceeds its declared length {length}"
    let values ← natListTerm (bytes ++ List.replicate (length - bytes.length) 0)
    pure (.bytes length, ← `(Noctium.Expr.bytesLiteral $(natTerm length) $values))
  | `(nlexpr| copyValue($value)) => do
    let (ty, value) ← expression env value
    pure (ty, ← `(Noctium.Expr.copyValue $value))
  | `(nlexpr| reverseBytes($value)) => do
    let (valueTy, value) ← expression env value
    let .bytes _ := valueTy
      | throwErrorAt stx "reverseBytes requires a Bytes expression"
    pure (valueTy, ← `(Noctium.Expr.reverseBytes $value))
  | `(nlexpr| sliceBytes($value, $start:num, $stop:num)) => do
    let (valueTy, value) ← expression env value
    let .bytes length := valueTy
      | throwErrorAt stx "sliceBytes requires a Bytes expression"
    let start := start.getNat
    let stop := stop.getNat
    unless start ≤ stop && stop ≤ length do
      throwErrorAt stx s!"byte slice bounds must satisfy 0 ≤ start ≤ end ≤ {length}"
    pure (.bytes (stop - start), ← `(Noctium.Expr.sliceBytes $value $(natTerm start) $(natTerm stop)))
  | `(nlexpr| concatBytes($left, $right)) => do
    let (leftTy, left) ← expression env left
    let (rightTy, right) ← expression env right
    let (.bytes leftLength, .bytes rightLength) := (leftTy, rightTy)
      | throwErrorAt stx "concatBytes requires two Bytes expressions"
    let length := leftLength + rightLength
    if length > Noctium.maxBytesLength then
      throwErrorAt stx s!"concatenated byte string length exceeds the maximum of {Noctium.maxBytesLength}"
    pure (.bytes length, ← `(Noctium.Expr.concatBytes $left $right))
  | `(nlexpr| reverseBytes32($value)) => do
    let value ← expected env value (.bytes 32)
    pure (.bytes 32, ← `(Noctium.Expr.reverseBytes32 $value))
  | `(nlexpr| shieldedOutputNonce($value)) => do
    let value ← expected env value (.bytes 32)
    pure (.bytes 32, ← `(Noctium.Wire.shieldedOutputNonce $value))
  | `(nlexpr| bytes32($literal:str)) => do
    let bytes := literal.getString.toUTF8.data.toList.map UInt8.toNat
    if bytes.length > 32 then throwErrorAt stx "Bytes32 string literal exceeds 32 UTF-8 bytes"
    let padded := bytes ++ List.replicate (32 - bytes.length) 0
    let values ← natListTerm padded
    pure (.bytes 32, ← `(Noctium.Expr.bytes32Literal $values))
  | `(nlexpr| persistentHashVector32([$values,*])) => do
    let expressions ← values.getElems.toList.mapM fun value => do
      let (valueTy, value) ← expression env value
      unless valueTy == .bytes 32 do
        throwErrorAt value "persistentHashVector32 accepts only Bytes32 elements"
      pure value
    unless expressions.length ≥ 1 && expressions.length ≤ 32 do
      throwErrorAt stx "persistentHashVector32 requires 1 to 32 Bytes32 elements"
    let valueList ← exprListTerm expressions
    pure (.bytes 32, ← `(Noctium.Expr.persistentHashVector32 $valueList))
  | `(nlexpr| persistentHashNative($value)) => do
    let (valueTy, value) ← expression env value
    unless valueTy == .native do
      throwErrorAt stx "persistentHashNative requires a Native field expression"
    pure (.bytes 32, ← `(Noctium.Expr.persistentHashNative $value))
  | `(nlexpr| persistentHashNativeVector([$values,*])) => do
    let expressions ← values.getElems.toList.mapM fun value => do
      let (valueTy, value) ← expression env value
      unless valueTy == .native do
        throwErrorAt value "persistentHashNativeVector accepts only Native fields"
      pure value
    unless expressions.length ≥ 1 && expressions.length ≤ 32 do
      throwErrorAt stx "persistentHashNativeVector requires 1 to 32 Native fields"
    let valueList ← nativeExprListTerm expressions
    pure (.bytes 32, ← `(Noctium.Expr.persistentHashNativeVector $valueList))
  | `(nlexpr| callCommitment($callee:ident, $interface:ident, $entrypoint:str,
      $opening, [$inputs,*], [$outputs,*])) => do
    let contract ← liftCoreM <| resolveGlobalConstNoOverload callee
    let interfaceName ← liftCoreM <| resolveGlobalConstNoOverload interface
    let implementations := interfaceImplementationRegistry.getState (← getEnv)
    unless implementations.any (fun item =>
        item.contract == contract && item.interface == interfaceName) do
      throwErrorAt interface s!"contract '{contract}' does not implement interface '{interfaceName}'"
    let interfaces := callInterfaceRegistry.getState (← getEnv)
    let some interface := interfaces.find? (fun item =>
        item.contract == interfaceName && item.operation == entrypoint.getString)
      | throwErrorAt entrypoint s!"interface '{interfaceName}' has no entry '{entrypoint.getString}'"
    commitmentHash env interface opening inputs.getElems outputs.getElems stx
  | `(nlexpr| callCommitment($callee:ident, $entrypoint:str, $opening, [$inputs,*], [$outputs,*])) => do
    let contract ← liftCoreM <| resolveGlobalConstNoOverload callee
    let envState ← getEnv
    unless (contractRegistry.getState envState).contains contract do
      throwErrorAt callee "callCommitment requires a declared callee contract"
    let interfaces := callInterfaceRegistry.getState envState
    let some interface := interfaces.find? (fun item =>
        item.contract == contract && item.operation == entrypoint.getString)
      | throwErrorAt entrypoint "callCommitment requires a declared callee entrypoint"
    commitmentHash env interface opening inputs.getElems outputs.getElems stx
  | `(nlexpr| transientHashNativeVector([$values,*])) => do
    let sourceValues := values.getElems.toList
    unless sourceValues.length ≤ Types.defaultLimits.maxVectorLength do
      throwErrorAt stx s!"transient hash input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    let values ← sourceValues.mapM fun value => do
      let (valueTy, expression) ← expression env value
      unless valueTy == .native do
        throwErrorAt value "transientHashNativeVector accepts only Native fields"
      pure expression
    let valueList ← nativeExprListTerm values
    pure (.native, ← `(Noctium.Expr.transientHash $valueList))
  | `(nlexpr| persistentHashPoint($point)) => do
    let point ← expected env point .jubjubPoint
    let x ← `(Noctium.Expr.jubjubCoordinate $point 0)
    let y ← `(Noctium.Expr.jubjubCoordinate $point 1)
    let valueList ← nativeExprListTerm [x, y]
    pure (.bytes 32, ← `(Noctium.Expr.persistentHashNativeVector $valueList))
  | `(nlexpr| degradeToNative($value)) => do
    let (valueTy, value) ← expression env value
    unless valueTy == .bytes 32 do
      throwErrorAt stx "degradeToNative requires a Bytes32 expression"
    -- Match the ledger's transient-crypto degradation, which takes field_vec()[1].
    pure (.native, ← `(Noctium.Expr.bytesField $value 1))
  | `(nlexpr| jubjubScalarFromNative($value)) => do
    let value ← expected env value .native
    pure (.jubjubScalar, ← `(Noctium.Expr.jubjubScalarFromNative $value))
  | `(nlexpr| jubjubScalarToNative($value)) => do
    let value ← expected env value .jubjubScalar
    pure (.native, ← `(Noctium.Expr.jubjubScalarToNative $value))
  | `(nlexpr| jubjubMulGenerator($scalar)) => do
    let scalar ← expected env scalar .jubjubScalar
    pure (.jubjubPoint, ← `(Noctium.Expr.jubjubMulGenerator $scalar))
  | `(nlexpr| jubjubMul($point, $scalar)) => do
    let point ← expected env point .jubjubPoint
    let scalar ← expected env scalar .jubjubScalar
    pure (.jubjubPoint, ← `(Noctium.Expr.jubjubMul $point $scalar))
  | `(nlexpr| jubjubAdd($left, $right)) => do
    let left ← expected env left .jubjubPoint
    let right ← expected env right .jubjubPoint
    pure (.jubjubPoint, ← `(Noctium.Expr.jubjubAdd $left $right))
  | `(nlexpr| jubjubNeg($point)) => do
    let point ← expected env point .jubjubPoint
    pure (.jubjubPoint, ← `(Noctium.Expr.jubjubNeg $point))
  | `(nlexpr| jubjubX($point)) => do
    let point ← expected env point .jubjubPoint
    pure (.native, ← `(Noctium.Expr.jubjubCoordinate $point 0))
  | `(nlexpr| jubjubY($point)) => do
    let point ← expected env point .jubjubPoint
    pure (.native, ← `(Noctium.Expr.jubjubCoordinate $point 1))
  | `(nlexpr| jubjubFromCoordinates($x, $y)) => do
    let x ← expected env x .native
    let y ← expected env y .native
    pure (.jubjubPoint, ← `(Noctium.Expr.jubjubFromCoordinates $x $y))
  | `(nlexpr| secp256k1Base($value:num)) => do
    unless value.getNat < Foreign.Curve.baseModulus .secp256k1 do
      throwErrorAt value "Secp256k1Base literal is not canonical"
    pure (.foreign (.base .secp256k1), ← `(Noctium.Expr.foreignBase Noctium.Foreign.Curve.secp256k1 $value))
  | `(nlexpr| secp256k1Scalar($value:num)) => do
    unless value.getNat < Foreign.Curve.scalarModulus .secp256k1 do
      throwErrorAt value "Secp256k1Scalar literal is not canonical"
    pure (.foreign (.scalar .secp256k1), ← `(Noctium.Expr.foreignScalar Noctium.Foreign.Curve.secp256k1 $value))
  | `(nlexpr| secp256k1Point($x:num, $y:num)) => do
    let point ← foreignPointExprTerm stx .secp256k1 x.getNat y.getNat
    pure (.foreign (.point .secp256k1), point)
  | `(nlexpr| secp256k1Identity()) =>
    pure (.foreign (.point .secp256k1), ← `(Noctium.Expr.foreignIdentity Noctium.Foreign.Curve.secp256k1))
  | `(nlexpr| secp256r1Base($value:num)) => do
    unless value.getNat < Foreign.Curve.baseModulus .secp256r1 do
      throwErrorAt value "Secp256r1Base literal is not canonical"
    pure (.foreign (.base .secp256r1), ← `(Noctium.Expr.foreignBase Noctium.Foreign.Curve.secp256r1 $value))
  | `(nlexpr| secp256r1Scalar($value:num)) => do
    unless value.getNat < Foreign.Curve.scalarModulus .secp256r1 do
      throwErrorAt value "Secp256r1Scalar literal is not canonical"
    pure (.foreign (.scalar .secp256r1), ← `(Noctium.Expr.foreignScalar Noctium.Foreign.Curve.secp256r1 $value))
  | `(nlexpr| secp256r1Point($x:num, $y:num)) => do
    let point ← foreignPointExprTerm stx .secp256r1 x.getNat y.getNat
    pure (.foreign (.point .secp256r1), point)
  | `(nlexpr| secp256r1Identity()) =>
    pure (.foreign (.point .secp256r1), ← `(Noctium.Expr.foreignIdentity Noctium.Foreign.Curve.secp256r1))
  | `(nlexpr| curve25519Base($value:num)) => do
    unless value.getNat < Foreign.Curve.baseModulus .curve25519 do
      throwErrorAt value "Curve25519Base literal is not canonical"
    pure (.foreign (.base .curve25519), ← `(Noctium.Expr.foreignBase Noctium.Foreign.Curve.curve25519 $value))
  | `(nlexpr| curve25519Scalar($value:num)) => do
    unless value.getNat < Foreign.Curve.scalarModulus .curve25519 do
      throwErrorAt value "Curve25519Scalar literal is not canonical"
    pure (.foreign (.scalar .curve25519), ← `(Noctium.Expr.foreignScalar Noctium.Foreign.Curve.curve25519 $value))
  | `(nlexpr| curve25519Point($x:num, $y:num)) => do
    let point ← foreignPointExprTerm stx .curve25519 x.getNat y.getNat
    pure (.foreign (.point .curve25519), point)
  | `(nlexpr| curve25519Identity()) =>
    pure (.foreign (.point .curve25519), ← `(Noctium.Expr.foreignIdentity Noctium.Foreign.Curve.curve25519))
  | `(nlexpr| foreignAdd($left, $right)) => do
    let (leftTy, left) ← expression env left
    let (rightTy, right) ← expression env right
    let (.foreign kind, .foreign rightKind) := (leftTy, rightTy)
      | throwErrorAt stx "foreignAdd requires two foreign values"
    unless kind == rightKind do throwErrorAt stx "foreignAdd requires matching curve and role"
    let operation ← foreignBinaryOpTerm (.add kind)
    pure (.foreign kind, ← `(Noctium.Expr.foreignBinary $operation $left $right))
  | `(nlexpr| foreignSub($left, $right)) => do
    let (leftTy, left) ← expression env left
    let (rightTy, right) ← expression env right
    let (.foreign kind, .foreign rightKind) := (leftTy, rightTy)
      | throwErrorAt stx "foreignSub requires two foreign values"
    unless kind == rightKind do throwErrorAt stx "foreignSub requires matching curve and role"
    let operation ← foreignBinaryOpTerm (.sub kind)
    pure (.foreign kind, ← `(Noctium.Expr.foreignBinary $operation $left $right))
  | `(nlexpr| foreignMul($left, $right)) => do
    let (leftTy, left) ← expression env left
    let (rightTy, right) ← expression env right
    let (.foreign kind, .foreign rightKind) := (leftTy, rightTy)
      | throwErrorAt stx "foreignMul requires two foreign field values"
    unless kind == rightKind do throwErrorAt stx "foreignMul requires matching curve and field role"
    let some fieldKind := kind.fieldKind?
      | throwErrorAt stx "foreignMul does not accept point values"
    let operation ← foreignBinaryOpTerm (.mul fieldKind)
    pure (.foreign kind, ← `(Noctium.Expr.foreignBinary $operation $left $right))
  | `(nlexpr| foreignNeg($value)) => do
    let (ty, value) ← expression env value
    let .foreign kind := ty
      | throwErrorAt stx "foreignNeg requires a foreign value"
    let operation ← foreignUnaryOpTerm (.neg kind)
    pure (ty, ← `(Noctium.Expr.foreignUnary $operation $value))
  | `(nlexpr| foreignInv($value)) => do
    let (ty, value) ← expression env value
    let .foreign kind := ty
      | throwErrorAt stx "foreignInv requires a foreign field value"
    let some fieldKind := kind.fieldKind?
      | throwErrorAt stx "foreignInv does not accept point values"
    let operation ← foreignUnaryOpTerm (.inv fieldKind)
    pure (ty, ← `(Noctium.Expr.foreignUnary $operation $value))
  | `(nlexpr| curveMul($point, $scalar)) => do
    let (pointTy, point) ← expression env point
    let (scalarTy, scalar) ← expression env scalar
    let .foreign (.point curve) := pointTy
      | throwErrorAt point "curveMul requires a curve point as its first argument"
    let .foreign (.scalar scalarCurve) := scalarTy
      | throwErrorAt scalar "curveMul requires a matching curve scalar"
    unless curve == scalarCurve do throwErrorAt stx "curveMul requires matching curve families"
    let operation ← foreignBinaryOpTerm (.ecMul curve)
    pure (pointTy, ← `(Noctium.Expr.foreignBinary $operation $point $scalar))
  | `(nlexpr| curveMulGenerator($scalar)) => do
    let (scalarTy, scalar) ← expression env scalar
    let .foreign (.scalar curve) := scalarTy
      | throwErrorAt stx "curveMulGenerator requires a foreign curve scalar"
    let operation ← foreignUnaryOpTerm (.mulGenerator curve)
    pure (.foreign (.point curve), ← `(Noctium.Expr.foreignUnary $operation $scalar))
  | `(nlexpr| curveX($point)) => do
    let (pointTy, point) ← expression env point
    let .foreign (.point curve) := pointTy
      | throwErrorAt stx "curveX requires a foreign curve point"
    let operation ← foreignUnaryOpTerm (.x curve)
    pure (.foreign (.base curve), ← `(Noctium.Expr.foreignUnary $operation $point))
  | `(nlexpr| curveY($point)) => do
    let (pointTy, point) ← expression env point
    let .foreign (.point curve) := pointTy
      | throwErrorAt stx "curveY requires a foreign curve point"
    let operation ← foreignUnaryOpTerm (.y curve)
    pure (.foreign (.base curve), ← `(Noctium.Expr.foreignUnary $operation $point))
  | `(nlexpr| curveFromCoordinates($x, $y)) => do
    let (xTy, x) ← expression env x
    let (yTy, y) ← expression env y
    let (.foreign (.base curve), .foreign (.base yCurve)) := (xTy, yTy)
      | throwErrorAt stx "curveFromCoordinates requires two foreign base-field values"
    unless curve == yCurve do throwErrorAt stx "curveFromCoordinates requires matching curve families"
    let operation ← foreignBinaryOpTerm (.fromCoordinates curve)
    pure (.foreign (.point curve), ← `(Noctium.Expr.foreignBinary $operation $x $y))
  | `(nlexpr| foreignToBytes($value)) => do
    let (valueTy, value) ← expression env value
    let .foreign kind := valueTy
      | throwErrorAt stx "foreignToBytes requires a foreign curve value"
    pure (.bytes kind.byteLength, ← `(Noctium.Expr.foreignToBytes $value))
  | `(nlexpr| foreignFromBytes($target:nltype, $value)) => do
    let target ← readTy target
    let .foreign kind := target
      | throwErrorAt stx "foreignFromBytes target must be a foreign curve type"
    let (valueTy, value) ← expression env value
    let byteLength ← match valueTy with
      | .bytes byteLength => pure byteLength
      | _ => throwErrorAt stx "foreignFromBytes requires a Bytes expression"
    if byteLength > maxBytesLength then
      throwErrorAt stx s!"byte string length exceeds the maximum of {maxBytesLength}"
    if let .point _ := kind then
      unless byteLength == kind.byteLength do
        throwErrorAt stx s!"foreign point decoding requires Bytes {kind.byteLength}"
    let kindTerm ← foreignKindTerm kind
    pure (target, ← `(Noctium.Expr.foreignFromBytes $kindTerm $value))
  | `(nlexpr| hashToCurve([$values,*])) => do
    let sourceValues := values.getElems.toList
    unless sourceValues.length ≤ Types.defaultLimits.maxVectorLength do
      throwErrorAt stx s!"hashToCurve input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    let values ← sourceValues.mapM fun value => expected env value .native
    let valueList ← nativeExprListTerm values
    pure (.jubjubPoint, ← `(Noctium.Expr.hashToCurve $valueList))
  | _ => throwErrorAt stx "unsupported Noctium expression"
where
  expected (env : Bindings) (stx : TSyntax `nlexpr) (ty : Ty) : CommandElabM (TSyntax `term) := do
    if let .uint maximum := ty then
      if let `(nlexpr| $n:num) := stx then
        unless n.getNat ≤ maximum do throwErrorAt stx "unsigned constant exceeds its type"
        return ← `(Noctium.Expr.uint $(natTerm maximum) $n)
    let (found, value) ← expression env stx
    coerceExpression stx found ty value
  commitmentHash (env : Bindings) (interface : CallInterface)
      (opening : TSyntax `nlexpr) (inputs outputs : Array (TSyntax `nlcallvalue))
      (stx : TSyntax `nlexpr) : CommandElabM (Ty × TSyntax `term) := do
    let arguments ← callExpressions "argument" interface.argumentFields interface.argumentViews inputs stx
    let results ← callExpressions "result" interface.resultFields interface.resultViews outputs stx
    let payload := [(opening, Ty.native)] ++ arguments ++ results
    let mut bindings := []
    let mut fields : Array (TSyntax `term) := #[]
    for ((part, ty), index) in payload.zipIdx do
      let value ← expected env part ty
      -- Pick a local name outside the incoming environment before expanding ABI projections.
      let name := ((List.range (env.length + 1)).map fun suffix =>
        s!"_noctium_call_{index}_{suffix}").find? fun name =>
          !env.any (fun binding => binding.1 == name)
      let some name := name | throwErrorAt part "cannot allocate call commitment binding"
      let nameTerm := stringTerm name
      let typeTerm ← tyTerm ty
      let ref ← `(Noctium.Expr.ref (ty := $typeTerm) $nameTerm)
      fields := fields.push (← `(Noctium.Expr.nativeCallFields $ref))
      bindings := (nameTerm, value) :: bindings
    let body ← `(Noctium.Expr.transientHash (List.flatten [$fields,*]))
    let result ← bindings.foldlM (init := body) fun body (name, value) =>
      `(Noctium.Expr.letE $name $value $body)
    pure (.native, result)
  arithmetic (env : Bindings) (stx : Syntax) (op : ScalarPolicy.Binary)
      (left right : TSyntax `nlexpr) : CommandElabM (Ty × TSyntax `term) := do
    let (lt, left) ← expression env left
    let (rt, right) ← expression env right
    let result ← match ScalarPolicy.infer op lt.scalarKind rt.scalarKind with
      | .ok result => pure result
      | .error message => throwErrorAt stx message
    match result with
    | .native =>
      let left ← coerceExpression stx lt .native left
      let right ← coerceExpression stx rt .native right
      let term ← match op with
        | .add => `(Noctium.Expr.add $left $right)
        | .sub => `(Noctium.Expr.sub $left $right)
        | .mul => `(Noctium.Expr.mul $left $right)
      pure (.native, term)
    | .uint maximum =>
      let term ← match op with
        | .add => `(Noctium.Expr.uadd $left $right)
        | .sub => `(Noctium.Expr.usub $left $right)
        | .mul => `(Noctium.Expr.umul $left $right)
      pure (.uint maximum, term)
    | .opaqueBytes => throwErrorAt stx "OpaqueBytes do not support scalar arithmetic"
    | .bool => throwErrorAt stx "invalid arithmetic result type"
    | .bytes _ => throwErrorAt stx "Bytes32 does not support arithmetic"
    | .jubjubScalar | .jubjubPoint =>
      throwErrorAt stx "Jubjub values do not support scalar arithmetic"
    | .foreign _ => throwErrorAt stx "foreign values require a qualified curve operation"

private def checkedExpression (env : Bindings) (stx : TSyntax `nlexpr) (ty : Ty) :
    CommandElabM (TSyntax `term) := do
  if let .uint maximum := ty then
    if let `(nlexpr| $n:num) := stx then
      unless n.getNat ≤ maximum do throwErrorAt stx "unsigned constant exceeds its type"
      return ← `(Noctium.Expr.uint $(natTerm maximum) $n)
  let (found, value) ← expression env stx
  coerceExpression stx found ty value

private def checkedLedgerFieldValues (env : Bindings) (payload : TSyntax `nlleaves)
    (fields : List (String × Ty)) : CommandElabM (List (Ty × TSyntax `term)) := do
  let `(nlleaves| fields($items:nlexpr,*)) := payload
    | throwErrorAt payload "ledger record payload expects fields(...)"
  let items := items.getElems.toList
  unless items.length == fields.length do
    throwErrorAt payload "ledger record field count does not match its checked layout"
  (items.zip fields).mapM fun (item, _, ty) => do
    pure (ty, ← checkedExpression env item ty)

private def elaborateLedgerFieldValues (env : Bindings) (payload : TSyntax `nlleaves)
    (fields : List (String × Ty)) : CommandElabM (TSyntax `term) := do
  let values ← (← checkedLedgerFieldValues env payload fields).mapM fun (ty, value) => do
    `(Noctium.LedgerFieldExpr.mk $(← tyTerm ty) $value)
  let values := values.toArray
  `(([$values,*] : List Noctium.LedgerFieldExpr))

private partial def lowerTreePath (env : Bindings) (schema : LedgerValueType)
    (keys : List (TSyntax `nlexpr)) :
    CommandElabM (List (TSyntax `term) × LedgerValueType) := do
  match schema, keys with
  | value, [] => pure ([], value)
  | .scalar _, _ :: _ => throwError "nested map path continues through a scalar value"
  | .set _, _ :: _ => throwError "set members have no readable value"
  | .shieldedCoinSet .., _ :: _ => throwError "qualified shielded coin Set members have no readable value"
  | .counter, _ :: _ => throwError "nested map path continues through a Counter value"
  | .composite .., _ :: _ => throwError "nested map path continues through a composite value"
  | .«list» .., _ :: _ => throwError "nested map path continues through a list value"
  | .merkleTree .., _ :: _ => throwError "nested map path continues through a MerkleTree value"
  | .map keyTy child, key :: rest => do
    let lowered ← checkedExpression env key keyTy
    let (tail, result) ← lowerTreePath env child rest
    pure ((← `(Noctium.PathKey.mk $(← tyTerm keyTy) $lowered)) :: tail, result)

private def pathKeysTerm (keys : List (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let list ← pathKeyListTerm keys
  `(($list : List Noctium.PathKey))

private def lowerCollectionEntryPath (env : Bindings) (schema : LedgerValueType)
    (keys : List (TSyntax `nlexpr)) :
    CommandElabM (TSyntax `term × LedgerValueType) := do
  let some finalKey := keys.getLast? | throwError "map or set operation requires a key"
  let (parents, parent) ← lowerTreePath env schema (keys.take (keys.length - 1))
  let some keyTy := parent.collectionKey?
    | throwErrorAt finalKey "entry path must select a map or set"
  let value ← checkedExpression env finalKey keyTy
  let key ← `(Noctium.PathKey.mk $(← tyTerm keyTy) $value)
  pure (← pathKeysTerm (parents ++ [key]), parent)

private partial def sourcePathParts (path : TSyntax `nlpath) :
    CommandElabM (TSyntax `ident × List (TSyntax `nlexpr)) := do
  match path with
  | `(nlpath| $storage:ident) => pure (storage, [])
  | `(nlpath| $parent:nlpath[$key:nlexpr]) => do
    let (storage, keys) ← sourcePathParts parent
    pure (storage, keys ++ [key])
  | _ => throwErrorAt path "invalid recursive state path"

private def lowerMerkleTreePath (schema : List (String × StateKind)) (env : Bindings)
    (path : TSyntax `nlpath) :
    CommandElabM (TSyntax `ident × TSyntax `term × Nat × _root_.Bool × _root_.Bool) := do
  let (storage, sourceKeys) ← sourcePathParts path
  match schema.lookup storage.getId.toString with
  | some (.merkleTree depth) => do
    unless sourceKeys.isEmpty do
      throwErrorAt path "root MerkleTree operations do not accept a key path"
    unless 2 ≤ depth && depth ≤ 32 do
      throwErrorAt path "MerkleTree depth must be between 2 and 32"
    pure (storage, ← pathKeysTerm [], depth, Bool.false, Bool.false)
  | some (.historicMerkleTree depth) => do
    unless sourceKeys.isEmpty do
      throwErrorAt path "root HistoricMerkleTree operations do not accept a key path"
    unless 2 ≤ depth && depth ≤ 32 do
      throwErrorAt path "MerkleTree depth must be between 2 and 32"
    pure (storage, ← pathKeysTerm [], depth, Bool.true, Bool.false)
  | some (.tree treeSchema) => do
    unless 1 ≤ sourceKeys.length && sourceKeys.length ≤ 12 do
      throwErrorAt path "nested MerkleTree paths require one to twelve map keys"
    let (keys, selected) ← lowerTreePath env treeSchema sourceKeys
    let .merkleTree depth historic := selected
      | throwErrorAt path "nested path does not select a MerkleTree"
    unless 2 ≤ depth && depth ≤ 32 do
      throwErrorAt path "MerkleTree depth must be between 2 and 32"
    pure (storage, ← pathKeysTerm keys, depth, historic, Bool.true)
  | _ => throwErrorAt storage "MerkleTree operation requires a MerkleTree leaf or state"

private def treeStateSchema (schema : List (String × StateKind)) (storage : TSyntax `ident) :
    CommandElabM LedgerValueType := do
  match schema.lookup storage.getId.toString with
  | some (.tree value) => pure value
  | _ => throwErrorAt storage "nested path requires a declared recursive tree state"

private def statePathSchema (schema : List (String × StateKind)) (storage : TSyntax `ident) :
    CommandElabM LedgerValueType := do
  let some value := (schema.lookup storage.getId.toString).bind StateKind.pathSchema
    | throwErrorAt storage "state path requires a declared map or recursive tree"
  pure value

private def lowerListPath (schema : List (String × StateKind)) (env : Bindings)
    (path : TSyntax `nlpath) :
    CommandElabM (TSyntax `ident × TSyntax `term × Types.CompositeType × List (String × Ty)) := do
  let (storage, sourceKeys) ← sourcePathParts path
  unless sourceKeys.length ≤ 13 do
    throwErrorAt path "List paths support at most 13 map keys"
  let treeSchema ← treeStateSchema schema storage
  let (keys, value) ← lowerTreePath env treeSchema sourceKeys
  let .«list» environment type := value
    | throwErrorAt path "List operation path must select a List value"
  let fields ← match LedgerValueType.listElementFields environment type with
    | .ok fields => pure fields
    | .error message => throwErrorAt path message
  pure (storage, ← pathKeysTerm keys, type, fields)

private def counterPathTerm (env : Bindings) (schema : LedgerValueType)
    (keys : List (TSyntax `nlexpr)) : CommandElabM (TSyntax `term) := do
  let (path, result) ← lowerTreePath env schema keys
  let .counter := result | throwError "Counter operation path must select a Counter value"
  pathKeysTerm path

private def ensureFresh (env : Bindings) (id : TSyntax `ident) : CommandElabM Unit := do
  if env.any (fun p => p.1 == id.getId.toString) then
    throwErrorAt id "duplicate Noctium value '{id.getId}'"

private def failDisclosure (diagnostic : Diagnostic) : CommandElabM Unit :=
  throwError "{diagnostic.span.file}:{diagnostic.span.line}:{diagnostic.span.column}: {diagnostic.message}"

/-- Evaluate only the typed AST definitions constructed by these elaborators. -/
private unsafe def checkGeneratedCircuit (name : Name) : CommandElabM Unit := do
  let value ← evalConstCheck Circuit ``Circuit name
  match Disclosure.circuit value with
  | .ok _ => pure ()
  | .error diagnostic => failDisclosure diagnostic

private unsafe def checkGeneratedContract (name : Name) : CommandElabM Unit := do
  let value ← evalConstCheck Contract ``Contract name
  match value.validate Capabilities.source with
  | .error diagnostic => failDisclosure diagnostic
  | .ok _ =>
    match Disclosure.contract value with
    | .error diagnostic => failDisclosure diagnostic
    | .ok _ =>
      for entrypoint in value.entrypoints do
        let resultViews ← entrypoint.returnViews.mapM fun view => do
          let checked ← match Types.checkedLayout {} view.environment view.type entrypoint.span with
            | .ok checked => pure checked
            | .error diagnostic => throwError diagnostic.message
          pure (view.name, view.fields.zip (callViewLeafTypes checked.value))
        modifyEnv fun env => callInterfaceRegistry.addEntry env {
          contract := name, operation := entrypoint.name
          argumentFields := entrypoint.callArguments.map fun input => (input.name, input.ty)
          argumentViews := entrypoint.callInputViews.map fun view => (view.name, view.fields)
          resultFields := entrypoint.returns.map fun result => (result.name, result.ty)
          resultViews
        }

@[command_elab circuitCommand] def elabCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_circuit $name:ident where $stmts:nlcstmt* end) =>
    let mut env : Bindings := []
    let mut inputs : Array (TSyntax `term) := #[]
    let mut inputInfo := []
    let mut publicInputInfo := []
    let mut outputs : Array (TSyntax `term) := #[]
    let mut outputInfo : List (String × Ty) := []
    let mut constraints : Array (TSyntax `term) := #[]
    for stmt in stmts do
      match stmt with
      | `(nlcstmt| public $id:ident : $ty:nltype)
      | `(nlcstmt| private $id:ident : $ty:nltype) =>
        ensureFresh env id
        let t ← readTy ty
        let tt ← tyTerm t
        let isPublic := stmt.raw[0].getAtomVal == "public"
        let visibility ← if isPublic then `(Noctium.Visibility.public) else `(Noctium.Visibility.private)
        let span ← spanTerm stmt
        inputs := inputs.push (← `({ name := $(stringTerm id.getId.toString), ty := $tt, visibility := $visibility, span := $span : Noctium.Input }))
        env := (id.getId.toString, t, ← `(@Noctium.Expr.ref $tt $(stringTerm id.getId.toString))) :: env
        inputInfo := inputInfo ++ [(id.getId.toString, t)]
        if isPublic then publicInputInfo := publicInputInfo ++ [(id.getId.toString, t)]
      | `(nlcstmt| let $id:ident : $ty:nltype := $value:nlexpr) =>
        ensureFresh env id
        let t ← readTy ty
        let retain := (match t with | .uint _ => Bool.true | _ => Bool.false) || hasPartialScalar value
        let value ← checkedExpression env value t
        if retain then
          -- Equality keeps partial range/underflow checks in unused bindings.
          -- Byte expressions have no equality operator on the source surface, so
          -- retain their evaluation in a typed let whose body is true.
          match t with
          | .bytes _ =>
            constraints := constraints.push
              (← `(Noctium.Expr.letE "$byteRetain" $value (Noctium.Expr.bool Bool.true)))
          | _ =>
            constraints := constraints.push (← `(Noctium.Expr.eq $value $value))
        env := (id.getId.toString, t, value) :: env
      | `(nlcstmt| assert $value:nlexpr) =>
        constraints := constraints.push (← checkedExpression env value .bool)
      | `(nlcstmt| output $id:ident : $ty:nltype := $value:nlexpr) =>
        if outputInfo.any (fun p => p.1 == id.getId.toString) || inputInfo.any (fun p => p.1 == id.getId.toString) then
          throwErrorAt id "duplicate Noctium output '{id.getId}'"
        let t ← readTy ty
        let tt ← tyTerm t
        let value ← checkedExpression env value t
        let span ← spanTerm stmt
        outputs := outputs.push (← `({ name := $(stringTerm id.getId.toString), ty := $tt, value := $value, span := $span : Noctium.Output }))
        outputInfo := outputInfo ++ [(id.getId.toString, t)]
      | _ => throwErrorAt stmt "unsupported Noctium circuit statement"
    let span ← spanTerm stx
    let fullName := (← getCurrNamespace) ++ name.getId
    elabCommand (← `(def $name : Noctium.Circuit := { name := $(stringTerm fullName.toString), inputs := [$inputs,*], outputs := [$outputs,*], constraints := [$constraints,*], span := $span }))
    unsafe checkGeneratedCircuit fullName
    modifyEnv fun e => circuitRegistry.addEntry e {declName := fullName, inputs := inputInfo, publicInputs := publicInputInfo, outputs := outputInfo}
  | _ => throwUnsupportedSyntax

private def addReferences (env : Bindings) (items : List (String × Ty)) : CommandElabM Bindings := do
  let mut env := env
  for (name, ty) in items do
    if env.any (fun p => p.1 == name) then throwError "ambiguous circuit input/output '{name}'"
    env := (name, ty, ← `(@Noctium.Expr.ref $(← tyTerm ty) $(stringTerm name))) :: env
  pure env

/-- Check and quote a source expression against an explicit typed alias
environment. Authoring uses this to retain logical expressions across aggregate
output expansion without adding physical circuit outputs. -/
def quoteSourceExpression (env : List (String × Ty × TSyntax `term))
    (stx : TSyntax `nlexpr) (ty : Ty) : CommandElabM (TSyntax `term) :=
  checkedExpression env stx ty

private def addLogicalReferences (env : Bindings)
    (items : List (String × Ty × Name)) : CommandElabM Bindings := do
  let mut env := env
  for (name, ty, declaration) in items do
    if env.any (fun p => p.1 == name) then
      throwError "ambiguous logical output alias '{name}'"
    let value : TSyntax `term := ⟨mkIdent declaration⟩
    env := (name, ty, value) :: env
  pure env

private def addReferenceAs (env : Bindings) (sourceName internalName : String) (ty : Ty) :
    CommandElabM Bindings := do
  pure ((sourceName, ty, ← `(@Noctium.Expr.ref $(← tyTerm ty) $(stringTerm internalName))) :: env)

private inductive MerkleLeafType where
  | scalar (ty : Ty)
  | record (fields : List (String × Ty))
  deriving BEq

private structure EntryEffects where
  env : Bindings
  merkleLeafTypes : List (String × MerkleLeafType) := []
  terms : Array (TSyntax `term) := #[]
  spans : Array (TSyntax `term) := #[]
  guards : Array (TSyntax `term) := #[]
  returns : Array (TSyntax `term) := #[]
  returnViews : Array (TSyntax `term) := #[]
  nextLocal : Nat := 0
  usedLocalNames : List String := []

private def explicitEffectGuard (effect : TSyntax `nleffect) : Option (TSyntax `nlexpr) :=
  match effect with
  | `(nleffect| when $condition:nlexpr $update:nlupdate) => some condition
  | `(nleffect| when $condition:nlexpr write $_state:ident := $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr insert $_state:ident [ $_key:nlexpr ] := $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr require $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr read $_path:nlpath as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr readSelf as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr member $_path:nlpath as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr checkRoot $_path:nlpath against $_expected:nlexpr as $_dest:ident) =>
    some condition
  | `(nleffect| when $condition:nlexpr tokenBalance($_:nlexpr, $_:nlexpr) as $_:ident)
  | `(nleffect| when $condition:nlexpr tokenBalanceLt($_:nlexpr, $_:nlexpr, $_:nlexpr) as $_:ident)
  | `(nleffect| when $condition:nlexpr tokenBalanceGt($_:nlexpr, $_:nlexpr, $_:nlexpr) as $_:ident) => some condition
  | `(nleffect| when $condition:nlexpr headOrDefault $_:nlpath as ($_:ident, $_:ident)) => some condition
  | `(nleffect| when $condition:nlexpr $_operation:ident $_path:nlpath as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr increment $_path:nlpath by $_amount:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr decrement $_path:nlpath by $_amount:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr reset $_path:nlpath) => some condition
  | `(nleffect| when $condition:nlexpr insertDefault $_path:nlpath) => some condition
  | `(nleffect| when $condition:nlexpr resetHistory $_path:nlpath) => some condition
  | `(nleffect| when $condition:nlexpr insertField $_path:nlpath := $_leaf:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr insertHash $_path:nlpath := $_hash:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr insertHashIndex $_path:nlpath at $_index:nlexpr := $_hash:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr insertFieldIndex $_path:nlpath at $_index:nlexpr := $_leaf:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr insertLeaf $_path:nlpath := $_leaf:nlledgervalue) => some condition
  | `(nleffect| when $condition:nlexpr insertLeafIndex $_path:nlpath at $_index:nlexpr := $_leaf:nlledgervalue) => some condition
  | `(nleffect| when $condition:nlexpr insertLeafDefault $_path:nlpath at $_index:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr pushFront $_path:nlpath := $_payload:nlledgervalue) => some condition
  | `(nleffect| when $condition:nlexpr popFront $_path:nlpath) => some condition
  | `(nleffect| when $condition:nlexpr remove $_path:nlpath) => some condition
  | `(nleffect| when $condition:nlexpr blockTimeBefore($_deadline:nlexpr) as $_dest:ident)
  | `(nleffect| when $condition:nlexpr blockTimeAfter($_deadline:nlexpr) as $_dest:ident) =>
    some condition
  | `(nleffect| when $condition:nlexpr counterLessThan $_path:nlpath against $_threshold:nlexpr as $_destination:ident) =>
    some condition
  | `(nleffect| when $condition:nlexpr readCaller as ($_present:ident, $_isContract:ident, $_contract:ident, $_user:ident)) => some condition
  | _ => none

private def effectGuardTerm (env : Bindings) (parent : Option (TSyntax `term))
    (effect : TSyntax `nleffect) : CommandElabM (TSyntax `term) := do
  let explicit ← match explicitEffectGuard effect with
    | none => pure none
    | some condition => pure (some (← checkedExpression env condition .bool))
  match parent, explicit with
  | none, none => `(none)
  | none, some condition => `(some $condition)
  | some parent, none => `(some $parent)
  | some parent, some condition =>
    `(some (Noctium.Backend.Impact.activityGuardWithin $parent $condition))

private def merkleForeignFieldWidths : Foreign.Kind → List Nat
  | .base _ | .scalar .secp256k1 | .scalar .secp256r1 => [24, 8]
  | .scalar .curve25519 => [26, 7]
  | .point .curve25519 => [24, 8, 24, 8]
  | .point .secp256k1 | .point .secp256r1 => [24, 8, 24, 8, 32]

private def merkleLeafWidth : Ty → Option Nat
  | .native => some 32
  | .bool => some 1
  | .uint maximum => some (maximum.log2 / 8 + 1)
  | .bytes length => some length
  | .jubjubPoint => some 64
  | .foreign kind => some (merkleForeignFieldWidths kind).sum
  | _ => none

private partial def concatMerkleLeafBytes : List (TSyntax `term) → CommandElabM (TSyntax `term)
  | [] => `(Noctium.Expr.bytesLiteral 0 [])
  | [bytes] => pure bytes
  | chunks => do
    -- Balance concatenation to bound the byte materialized at each level.
    let mid := chunks.length / 2
    let left ← concatMerkleLeafBytes (chunks.take mid)
    let right ← concatMerkleLeafBytes (chunks.drop mid)
    `(Noctium.Expr.concatBytes $left $right)

private def encodeMerkleLeafScalar (ty : Ty) (value : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  match ty with
  | .native => `(Noctium.Expr.toBytes32 $value)
  | .bool => `(Noctium.Expr.select $value
      (Noctium.Expr.bytesLiteral 1 [1]) (Noctium.Expr.bytesLiteral 1 [0]))
  | .uint maximum => `(Noctium.Expr.sliceBytes
      (Noctium.Expr.toBytes32 (Noctium.Expr.cast Noctium.Ty.native $value)) 0
      $(natTerm (maximum.log2 / 8 + 1)))
  | .bytes _ => pure value
  | .jubjubPoint => do
    let x ← `(Noctium.Expr.jubjubCoordinate $value 0)
    let y ← `(Noctium.Expr.jubjubCoordinate $value 1)
    let xBytes ← `(Noctium.Expr.toBytes32 $x)
    let yBytes ← `(Noctium.Expr.toBytes32 $y)
    `(Noctium.Expr.concatBytes $xBytes $yBytes)
  | .foreign kind => do
    let chunks ← (merkleForeignFieldWidths kind).zipIdx.mapM fun (width, index) => do
      let field ← `(Noctium.Expr.foreignEncodedField $value $(natTerm index))
      let bytes ← `(Noctium.Expr.toBytes32 $field)
      `(Noctium.Expr.sliceBytes $bytes 0 $(natTerm width))
    concatMerkleLeafBytes chunks
  | _ => throwError "unsupported MerkleTree leaf type"

private def merkleLeafHash (values : List (Ty × TSyntax `term)) :
    CommandElabM (TSyntax `term) := do
  let chunks ← values.mapM fun (ty, value) => encodeMerkleLeafScalar ty value
  let domain ← `(Noctium.Expr.bytesLiteral 6 [109, 100, 110, 58, 108, 104])
  let bytes ← concatMerkleLeafBytes (domain :: chunks)
  `(Noctium.Expr.sha256 $bytes)

private def merkleLeafValues (env : Bindings) (ty : MerkleLeafType)
    (leaf : Option (TSyntax `nlledgervalue)) : CommandElabM (List (Ty × TSyntax `term)) := do
  match leaf with
  | none =>
    let types := match ty with | .scalar scalar => [scalar] | .record fields => fields.map Prod.snd
    types.mapM fun field => do
      pure (field, ← `(Noctium.GuardedExpression.zeroValue $(← tyTerm field)))
  | some payload =>
    match ty with
    | .scalar scalar => do
      let `(nlledgervalue| $value:nlexpr) := payload
        | throwErrorAt payload "scalar MerkleTree leaf expects one expression"
      pure [(scalar, ← checkedExpression env value scalar)]
    | .record fields => do
      let `(nlledgervalue| $values:nlleaves) := payload
        | throwErrorAt payload "record MerkleTree leaf expects fields(...)"
      checkedLedgerFieldValues env values fields

private def merkleWriteTerm (storage : TSyntax `ident) (keys hash : TSyntax `term)
    (nested : _root_.Bool) (index : Option (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let name := stringTerm storage.getId.toString
  match nested, index with
  | Bool.false, none => `(Noctium.Effect.merkleTreeInsertHash $name $hash)
  | Bool.true, none => `(Noctium.Effect.merkleTreeInsertHashAt $name $keys $hash)
  | Bool.false, some index => `(Noctium.Effect.merkleTreeInsertHashIndex $name $hash $index)
  | Bool.true, some index => `(Noctium.Effect.merkleTreeInsertHashIndexAt $name $keys $hash $index)

private def elaborateTypedMerkleWrite (schema : List (String × StateKind)) (path : TSyntax `nlpath)
    (leaf : Option (TSyntax `nlledgervalue)) (index : Option (TSyntax `nlexpr)) (fieldOnly : _root_.Bool)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, _, _, nested) ← lowerMerkleTreePath schema state.env path
  let some ty := state.merkleLeafTypes.lookup storage.getId.toString
    | throwErrorAt path "MerkleTree path is missing its declared leaf type"
  if fieldOnly && ty != .scalar .native then
    throwErrorAt path "insertField requires a Native MerkleTree leaf"
  let hash ← merkleLeafHash (← merkleLeafValues state.env ty leaf)
  let index ← index.mapM fun index => checkedExpression state.env index (.uint (2 ^ 64 - 1))
  let term ← merkleWriteTerm storage keys hash nested index
  pure {state with terms := state.terms.push term}

private def chooseBranchLocalName (env : Bindings) (used : List String) (next : Nat)
    (namePrefix : String := "noctium_if_local_") :
    String × Nat := Id.run do
  let mut candidateIndex := next
  let mut candidate := s!"{namePrefix}{candidateIndex}"
  while env.any (fun binding => binding.1 == candidate) || used.contains candidate do
    candidateIndex := candidateIndex + 1
    candidate := s!"{namePrefix}{candidateIndex}"
  return (candidate, candidateIndex + 1)

private def freshReadName (depth : Nat) (state : EntryEffects) (destination : TSyntax `ident) :
    CommandElabM (String × EntryEffects) := do
  ensureFresh state.env destination
  let sourceName := destination.getId.toString
  if depth == 0 then return (sourceName, state)
  let (internalName, nextLocal) :=
    chooseBranchLocalName state.env state.usedLocalNames state.nextLocal
  return (internalName, {state with nextLocal, usedLocalNames := internalName :: state.usedLocalNames})

private def bindReadName (state : EntryEffects) (sourceName internalName : String) (ty : Ty) :
    CommandElabM EntryEffects := do
  let env ← if sourceName == internalName then addReferences state.env [(sourceName, ty)]
    else addReferenceAs state.env sourceName internalName ty
  pure {state with env}

private def bindLedgerRecordFields (state : EntryEffects) (destination : TSyntax `ident)
    (depth : Nat) (fields : List (String × Ty)) :
    CommandElabM (EntryEffects × TSyntax `term) := do
  let mut updated := state
  let mut destinations := #[]
  for (field, ty) in fields do
    let sourceName := s!"{destination.getId}_{field}"
    if updated.env.any (fun binding => binding.1 == sourceName) then
      throwErrorAt destination s!"duplicate ledger record read field {sourceName}"
    let internalName ← if depth == 0 then pure sourceName else do
      let (candidate, nextLocal) := chooseBranchLocalName updated.env
        updated.usedLocalNames updated.nextLocal
      updated := {updated with nextLocal, usedLocalNames := candidate :: updated.usedLocalNames}
      pure candidate
    updated ← bindReadName updated sourceName internalName ty
    destinations := destinations.push (← `(($(stringTerm internalName), $(← tyTerm ty))))
  pure (updated, ← `(([$destinations,*] : List (String × Noctium.Ty))))

private def elaborateTokenBalanceRead (state : EntryEffects) (depth : Nat)
    (destination : TSyntax `ident) (color tag : TSyntax `nlexpr)
    (comparison : Option (_root_.Bool × TSyntax `nlexpr)) :
    CommandElabM EntryEffects := do
  let (readName, updated) ← freshReadName depth state destination
  let color ← checkedExpression updated.env color (.bytes 32)
  let tag ← checkedExpression updated.env tag .bool
  let (resultTy, query) ← match comparison with
    | none => pure (.uint balanceMaximum, ← `(Noctium.BalanceQuery.exact))
    | some (less, source) => do
      let limit ← checkedExpression updated.env source (.uint balanceMaximum)
      let direction ← if less then `(Bool.true) else `(Bool.false)
      pure (.bool, ← `(Noctium.BalanceQuery.compare $direction $limit))
  let term ← `(Noctium.Effect.readTokenBalance $(stringTerm readName) $color $tag $query)
  let updated := {updated with terms := updated.terms.push term}
  bindReadName updated destination.getId.toString readName resultTy
private def elaborateBlockTimeRead (state : EntryEffects) (depth : Nat)
    (destination : TSyntax `ident) (before : _root_.Bool) (deadline : TSyntax `nlexpr) :
    CommandElabM EntryEffects := do
  let value ← checkedExpression state.env deadline (.uint (2 ^ 64 - 1))
  let (name, updated) ← freshReadName depth state destination
  let direction ← if before then `(Bool.true) else `(Bool.false)
  let term ← `(Noctium.Effect.blockTimeCompare $(stringTerm name) $direction $value)
  bindReadName {updated with terms := updated.terms.push term}
    destination.getId.toString name .bool

private def elaborateCounterLessThan (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (threshold : TSyntax `nlexpr)
    (destination : TSyntax `ident) (depth : Nat) (state : EntryEffects) :
    CommandElabM EntryEffects := do
  let (storage, sourceKeys) ← sourcePathParts path
  let treeSchema ← treeStateSchema schema storage
  let keys ← counterPathTerm state.env treeSchema sourceKeys
  let threshold ← checkedExpression state.env threshold (.uint (2 ^ 64 - 1))
  let (readName, updated) ← freshReadName depth state destination
  let term ← `(Noctium.Effect.counterLessThan
    $(stringTerm storage.getId.toString) $(stringTerm readName) $keys $threshold)
  bindReadName {updated with terms := updated.terms.push term}
    destination.getId.toString readName .bool

private def elaborateTreeRead (storage destination : TSyntax `ident)
    (keys : List (TSyntax `nlexpr))
    (treeSchema : LedgerValueType) (depth : Nat) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (path, result) ← lowerTreePath state.env treeSchema keys
  let keys ← pathKeysTerm path
  match result with
  | .scalar valueTy => do
    let (readName, updated) ← freshReadName depth state destination
    let term ← `(Noctium.Effect.readPath $(stringTerm storage.getId.toString)
      $(stringTerm readName) $keys $(← tyTerm valueTy))
    let updated := {updated with terms := updated.terms.push term}
    bindReadName updated destination.getId.toString readName valueTy
  | .composite environment (.structure typeId) => do
    let fields ← match LedgerValueType.recordFields environment (.structure typeId) with
      | .ok fields => pure fields
      | .error _ => match LedgerValueType.shieldedCoinRecordFields environment (.structure typeId) with
        | .ok fields => pure fields
        | .error message => throwErrorAt destination message
    let (readName, updated) ← freshReadName depth state destination
    let (updated, destinations) ← bindLedgerRecordFields updated destination depth fields
    let typeTerm ← `(Noctium.Types.CompositeType.structure $(stringTerm typeId))
    let term ← `(Noctium.Effect.readCompositePath
      $(stringTerm storage.getId.toString) $(stringTerm readName) $keys $typeTerm $destinations)
    pure {updated with terms := updated.terms.push term}
  | .composite .. => throwErrorAt destination "native composite ledger reads require a named structure"
  | .map .. => throwErrorAt destination "nested map read must select a scalar or composite value"
  | .set _ => throwErrorAt destination "Set members do not have readable values"
  | .shieldedCoinSet .. => throwErrorAt destination "Set members do not have readable values"
  | .«list» .. => throwErrorAt destination "List reads require head or length"
  | .merkleTree .. => throwErrorAt destination "MerkleTree values are read through their operations"
  | .counter => do
    let (readName, updated) ← freshReadName depth state destination
    let pathTerm ← pathKeysTerm path
    let ty := Ty.uint (2 ^ 64 - 1)
    let term ← `(Noctium.Effect.counterRead
      $(stringTerm storage.getId.toString) $(stringTerm readName) $pathTerm)
    let updated := {updated with terms := updated.terms.push term}
    bindReadName updated destination.getId.toString readName ty

private def elaborateCounterAdjust (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (subtract : _root_.Bool)
    (amount : TSyntax `nlexpr) (state : EntryEffects) : CommandElabM EntryEffects := do
  let maximum := 2 ^ 32 - 1
  let value ← match amount with
    | `(nlexpr| $n:num) => do
      unless n.getNat ≤ maximum do
        throwErrorAt amount "Counter adjustment exceeds the native u32 immediate"
      `(Noctium.Expr.uint $(natTerm maximum) $n)
    | _ => do
      let value ← checkedExpression state.env amount (.uint (2 ^ 16 - 1))
      `(Noctium.Expr.cast $(← tyTerm (.uint maximum)) $value)
  let (storage, keys) ← sourcePathParts path
  let treeSchema ← treeStateSchema schema storage
  let path ← counterPathTerm state.env treeSchema keys
  let direction ← if subtract then `(Bool.true) else `(Bool.false)
  let term ← `(Noctium.Effect.counterAdjust
    $(stringTerm storage.getId.toString) $path $direction $value)
  pure {state with terms := state.terms.push term}

private def elaborateListLength (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (destinationId : TSyntax `ident)
    (depth : Nat) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, _, _) ← lowerListPath schema state.env path
  let (readName, updated) ← freshReadName depth state destinationId
  let term ← `(Noctium.Effect.listLength
    $(stringTerm storage.getId.toString) $(stringTerm readName) $keys)
  let updated := {updated with terms := updated.terms.push term}
  bindReadName updated destinationId.getId.toString readName (.uint (2 ^ 64 - 1))

private def listElementTypeTerm (source : Syntax) (type : Types.CompositeType) :
    CommandElabM (TSyntax `term) := do
  match type with
  | .scalar ty => `(Noctium.Types.CompositeType.scalar $(← tyTerm ty))
  | .structure id => `(Noctium.Types.CompositeType.structure $(stringTerm id))
  | _ => throwErrorAt source "List elements must be scalar values or named records"

private def elaborateListHead (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (destination : TSyntax `ident) (depth : Nat)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, type, fields) ← lowerListPath schema state.env path
  let (readName, updated) ← freshReadName depth state destination
  let (updated, destinations) ← match type with
    | .scalar ty => do
      let updated ← bindReadName updated destination.getId.toString readName ty
      pure (updated, ← `([($(stringTerm readName), $(← tyTerm ty))]))
    | _ => bindLedgerRecordFields updated destination depth fields
  let typeTerm ← listElementTypeTerm path type
  let term ← `(Noctium.Effect.listHead
    $(stringTerm storage.getId.toString) $(stringTerm readName) $keys $typeTerm $destinations)
  pure {updated with terms := updated.terms.push term}

private def listLengthIsZero (storage : TSyntax `ident) (keys : TSyntax `term)
    (stem : String) (state : EntryEffects) :
    CommandElabM (EntryEffects × TSyntax `term) := do
  let (lengthName, nextLocal) := chooseBranchLocalName state.env
    state.usedLocalNames state.nextLocal stem
  let lengthEffect ← `(Noctium.Effect.listLength
    $(stringTerm storage.getId.toString) $(stringTerm lengthName) $keys)
  let maximum := 2 ^ 64 - 1
  let lengthType ← tyTerm (.uint maximum)
  let lengthRef ← `(@Noctium.Expr.ref $lengthType $(stringTerm lengthName))
  let zero ← `(Noctium.Expr.uint $(natTerm maximum) 0)
  let isZero ← `(Noctium.Expr.eq $lengthRef $zero)
  pure ({state with
    terms := state.terms.push lengthEffect
    nextLocal
    usedLocalNames := lengthName :: state.usedLocalNames}, isZero)

private def elaborateListHeadOrDefault (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (present record : TSyntax `ident) (depth : Nat)
    (guard span : TSyntax `term) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, _, _) ← lowerListPath schema state.env path
  ensureFresh state.env present
  let (state, isZero) ← listLengthIsZero storage keys "noctiumOptionalHeadLength" state
  let presentValue ← `(Noctium.Expr.eq $isZero (Noctium.Expr.bool Bool.false))
  let headGuard ← match guard with
    | `(term| none) => `(some $presentValue)
    | `(term| some $outer) =>
      `(some (Noctium.Backend.Impact.activityGuardWithin $outer $presentValue))
    | _ => throwError "invalid optional List head effect guard"
  let presentName := present.getId.toString
  let updated : EntryEffects := {
    state with
    env := (presentName, .bool, presentValue) :: state.env
    spans := state.spans.push span |>.push span
    guards := state.guards.push guard |>.push headGuard
  }
  elaborateListHead schema path record depth updated

private def elaborateListPushFront (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (payload : TSyntax `nlledgervalue)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, type, fields) ← lowerListPath schema state.env path
  let valuesTerm ← match payload with
    | `(nlledgervalue| $item:nlexpr) => do
      let .scalar ty := type
        | throwErrorAt payload "record List pushFront expects fields(...)"
      let value ← checkedExpression state.env item ty
      `([Noctium.LedgerFieldExpr.mk $(← tyTerm ty) $value])
    | `(nlledgervalue| $items:nlleaves) => do
      if let .scalar _ := type then
        throwErrorAt payload "scalar List pushFront expects one value expression"
      elaborateLedgerFieldValues state.env items fields
    | _ => throwErrorAt payload "expected a List element"
  let typeTerm ← listElementTypeTerm path type
  let term ← `(Noctium.Effect.listPushFront
    $(stringTerm storage.getId.toString) $keys $typeTerm $valuesTerm)
  pure {state with terms := state.terms.push term}

private def elaborateListPopFront (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, _, _) ← lowerListPath schema state.env path
  let term ← `(Noctium.Effect.listPopFront $(stringTerm storage.getId.toString) $keys)
  pure {state with terms := state.terms.push term}

private def collectionResetTerm (path : TSyntax `nlpath) (storage : TSyntax `ident)
    (keys : TSyntax `term) (keyCount : Nat) (value : LedgerValueType)
    (mapDefault : _root_.Bool := Bool.false) :
    CommandElabM (TSyntax `term) := do
  let name := stringTerm storage.getId.toString
  match value with
  | .counter => `(Noctium.Effect.counterReset $name $keys)
  | .«list» .. =>
    unless keyCount ≤ 13 do throwErrorAt path "List paths support at most 13 map keys"
    `(Noctium.Effect.listReset $name $keys)
  | .map .. | .set _ => `(Noctium.Effect.emptyMapPath $name $keys)
  | .merkleTree depth historic =>
    unless 1 ≤ keyCount && keyCount ≤ 12 do
      throwErrorAt path "nested MerkleTree paths require one to twelve map keys"
    unless 2 ≤ depth && depth ≤ 32 do
      throwErrorAt path "MerkleTree depth must be between 2 and 32"
    let historyTerm ← if historic then `(Bool.true) else `(Bool.false)
    let emptyHistory ← if historic && mapDefault then `(Bool.true) else `(Bool.false)
    `(Noctium.Effect.merkleTreeResetAt $name $keys $(natTerm depth) $historyTerm $emptyHistory)
  | _ => throwErrorAt path "reset requires a Counter, List, Map, Set or MerkleTree value"

private def elaborateReset (schema : List (String × StateKind)) (path : TSyntax `nlpath)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, sourceKeys) ← sourcePathParts path
  if let some depth := (schema.lookup storage.getId.toString).bind StateKind.merkleTreeDepth? then
    unless sourceKeys.isEmpty do
      throwErrorAt path "root MerkleTree reset does not accept a key path"
    unless 2 ≤ depth && depth ≤ 32 do
      throwErrorAt path "MerkleTree depth must be between 2 and 32"
    let term ← `(Noctium.Effect.merkleTreeReset $(stringTerm storage.getId.toString))
    return {state with terms := state.terms.push term}
  if let some (.cell ty) := schema.lookup storage.getId.toString then
    unless sourceKeys.isEmpty do throwErrorAt path "cell reset does not accept a key path"
    let type ← tyTerm ty
    let value ← `(Noctium.GuardedExpression.zeroValue $type)
    let term ← `(Noctium.Effect.writeCell $(stringTerm storage.getId.toString) $type $value)
    return {state with terms := state.terms.push term}
  let treeSchema ← statePathSchema schema storage
  let (keys, value) ← lowerTreePath state.env treeSchema sourceKeys
  let keys ← pathKeysTerm keys
  let term ← collectionResetTerm path storage keys sourceKeys.length value
  pure {state with terms := state.terms.push term}

private def elaborateMapDefault (schema : List (String × StateKind)) (path : TSyntax `nlpath)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, sourceKeys) ← sourcePathParts path
  let name := stringTerm storage.getId.toString
  let term ← if let some (.map keyTy valueTy) := schema.lookup storage.getId.toString then do
    let [key] := sourceKeys | throwErrorAt path "insertDefault on a direct Map requires one key"
    let key ← checkedExpression state.env key keyTy
    let type ← tyTerm valueTy
    `(Noctium.Effect.writeMap $name $(← tyTerm keyTy) $type $key
      (Noctium.GuardedExpression.zeroValue $type))
  else do
    let stateSchema ← statePathSchema schema storage
    let (keys, parent) ← lowerCollectionEntryPath state.env stateSchema sourceKeys
    let .map _ value := parent | throwErrorAt path "insertDefault requires a Map entry"
    match value with
    | .scalar ty => do
      let type ← tyTerm ty
      `(Noctium.Effect.writePath $name $keys $type (Noctium.GuardedExpression.zeroValue $type))
    | .composite environment (.structure id) => do
      let fields ← match LedgerValueType.recordFields environment (.structure id) with
        | .ok fields => pure fields
        | .error message => throwErrorAt path message
      let values ← fields.toArray.mapM fun (_, ty) => do
        let type ← tyTerm ty
        `(Noctium.LedgerFieldExpr.mk $type (Noctium.GuardedExpression.zeroValue $type))
      `(Noctium.Effect.writeCompositePath $name $keys
        (Noctium.Types.CompositeType.structure $(stringTerm id)) [$values,*])
    | .composite .. => throwErrorAt path "insertDefault requires a named ledger record"
    | value => collectionResetTerm path storage keys sourceKeys.length value Bool.true
  pure {state with terms := state.terms.push term}

private def elaborateCompositePathWrite (schema : List (String × StateKind))
    (storage : TSyntax `ident) (keys : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (state : EntryEffects) : CommandElabM EntryEffects := do
  let treeSchema ← treeStateSchema schema storage
  let (path, result) ← lowerTreePath state.env treeSchema keys
  let (.composite environment type) := result
    | throwErrorAt payload "composite write must select a composite record"
  let fields ← match LedgerValueType.recordFields environment type with
    | .ok fields => pure fields
    | .error message => throwErrorAt payload message
  let valueList ← elaborateLedgerFieldValues state.env payload fields
  let pathTerm ← pathKeysTerm path
  let typeTerm ← match type with
    | .structure id => `(Noctium.Types.CompositeType.structure $(stringTerm id))
    | _ => throwErrorAt payload "composite writes currently require a named structure"
  let term ← `(Noctium.Effect.writeCompositePath
    $(stringTerm storage.getId.toString) $pathTerm $typeTerm $valueList)
  pure {state with terms := state.terms.push term}

private def elaborateMapRemove (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, sourceKeys) ← sourcePathParts path
  let stateSchema ← statePathSchema schema storage
  let (keys, _) ← lowerCollectionEntryPath state.env stateSchema sourceKeys
  let term ← `(Noctium.Effect.removePath $(stringTerm storage.getId.toString) $keys)
  pure {state with terms := state.terms.push term}

private def elaborateSetInsert (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, sourceKeys) ← sourcePathParts path
  let stateSchema ← statePathSchema schema storage
  let (keys, parent) ← lowerCollectionEntryPath state.env stateSchema sourceKeys
  let .set _ := parent | throwErrorAt path "insert without a value requires a Set"
  let term ← `(Noctium.Effect.setInsert $(stringTerm storage.getId.toString) $keys)
  pure {state with terms := state.terms.push term}

private def elaborateNamedPathRead (schema : List (String × StateKind))
    (operation : String) (path : TSyntax `nlpath) (destination : TSyntax `ident)
    (depth : Nat) (guard : TSyntax `term) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, sourceKeys) ← sourcePathParts path
  match operation with
  | "length" => elaborateListLength schema path destination depth state
  | "isEmpty" => do
    unless sourceKeys.length < 16 do
      throwErrorAt path "map or set emptiness path exceeds the native index limit"
    let valueType ← statePathSchema schema storage
    let (keys, selected) ← lowerTreePath state.env valueType sourceKeys
    if let .«list» .. := selected then
      unless sourceKeys.length ≤ 13 do
        throwErrorAt path "List paths support at most 13 map keys"
      ensureFresh state.env destination
      let (updated, isZero) ← listLengthIsZero storage (← pathKeysTerm keys)
        "noctiumListEmptyLength" state
      let empty ← match guard with
        | `(term| none) => pure isZero
        | `(term| some $condition) =>
          `(Noctium.Backend.Impact.activityGuardWithin $condition $isZero)
        | _ => throwError "invalid List emptiness effect guard"
      return {updated with env := (destination.getId.toString, .bool, empty) :: updated.env}
    unless selected.collectionKey?.isSome do
      throwErrorAt path "isEmpty path must select a Map or Set"
    let (readName, updated) ← freshReadName depth state destination
    let pathTerm ← pathKeysTerm keys
    let term ← `(Noctium.Effect.mapIsEmpty
      $(stringTerm storage.getId.toString) $(stringTerm readName) $pathTerm)
    let updated := {updated with terms := updated.terms.push term}
    bindReadName updated destination.getId.toString readName .bool
  | "size" => do
    unless sourceKeys.length < 16 do
      throwErrorAt path "map or set size path exceeds the native index limit"
    let valueType ← statePathSchema schema storage
    let (keys, selected) ← lowerTreePath state.env valueType sourceKeys
    unless selected.collectionKey?.isSome do
      throwErrorAt path "size path must select a Map or Set"
    let (readName, updated) ← freshReadName depth state destination
    let pathTerm ← pathKeysTerm keys
    let term ← `(Noctium.Effect.mapSize
      $(stringTerm storage.getId.toString) $(stringTerm readName) $pathTerm)
    let updated := {updated with terms := updated.terms.push term}
    bindReadName updated destination.getId.toString readName (.uint (2 ^ 64 - 1))
  | "head" => elaborateListHead schema path destination depth state
  | "isFull" => do
    let (treeState, keys, _, _, nested) ← lowerMerkleTreePath schema state.env path
    let (readName, updated) ← freshReadName depth state destination
    let term ← if nested then
      `(Noctium.Effect.merkleTreeIsFullAt
        $(stringTerm treeState.getId.toString) $keys $(stringTerm readName))
    else
      `(Noctium.Effect.merkleTreeIsFull
        $(stringTerm treeState.getId.toString) $(stringTerm readName))
    bindReadName {updated with terms := updated.terms.push term}
      destination.getId.toString readName .bool
  | "read" =>
    match schema.lookup storage.getId.toString with
    | some (.cell ty) => do
      unless sourceKeys.isEmpty do
        throwErrorAt path "cell reads do not accept a key path"
      let (readName, updated) ← freshReadName depth state destination
      let term ← `(Noctium.Effect.readCell
        $(stringTerm storage.getId.toString) $(stringTerm readName) $(← tyTerm ty))
      let updated := {updated with terms := updated.terms.push term}
      bindReadName updated destination.getId.toString readName ty
    | some (.map keyTy valueTy) => do
      let [key] := sourceKeys | throwErrorAt path "map reads require exactly one key"
      let (readName, updated) ← freshReadName depth state destination
      let loweredKey ← checkedExpression updated.env key keyTy
      let term ← `(Noctium.Effect.readMap
        $(stringTerm storage.getId.toString) $(stringTerm readName)
        $(← tyTerm keyTy) $(← tyTerm valueTy) $loweredKey)
      let updated := {updated with terms := updated.terms.push term}
      bindReadName updated destination.getId.toString readName valueTy
    | some (.tree treeSchema) =>
      elaborateTreeRead storage destination sourceKeys treeSchema depth state
    | some .opaqueString =>
      throwErrorAt storage "OpaqueString constructor metadata cannot be read by entrypoints"
    | _ => throwErrorAt storage "read requires a declared state cell or recursive tree"
  | "member" =>
    match schema.lookup storage.getId.toString with
    | some (.map keyTy valueTy) => do
      let [key] := sourceKeys | throwErrorAt path "map membership requires exactly one key"
      let (readName, updated) ← freshReadName depth state destination
      let loweredKey ← checkedExpression updated.env key keyTy
      let term ← `(Noctium.Effect.readMember
        $(stringTerm storage.getId.toString) $(stringTerm readName)
        $(← tyTerm keyTy) $(← tyTerm valueTy) $loweredKey)
      let updated := {updated with terms := updated.terms.push term}
      bindReadName updated destination.getId.toString readName .bool
    | some (.tree treeSchema) => do
      unless sourceKeys.length > 0 do
        throwErrorAt path "tree membership requires at least one key"
      let (keys, _) ← lowerCollectionEntryPath state.env treeSchema sourceKeys
      let (readName, updated) ← freshReadName depth state destination
      let term ← `(Noctium.Effect.memberPath
        $(stringTerm storage.getId.toString) $(stringTerm readName) $keys)
      let updated := {updated with terms := updated.terms.push term}
      bindReadName updated destination.getId.toString readName .bool
    | _ => throwErrorAt storage "membership requires a declared state map"
  | _ => throwErrorAt path "unsupported Noctium state query"

private partial def typedClaimOperation (value : TSyntax `nlexpr) : Option String :=
  match value with
  | `(nlexpr| callCommitment($_:ident, $operation:str, $_, [$_,*], [$_,*])) => some operation.getString
  | `(nlexpr| callCommitment($_:ident, $_:ident, $operation:str, $_, [$_,*], [$_,*])) =>
    some operation.getString
  | `(nlexpr| disclose($inner)) => typedClaimOperation inner
  | _ => none

private def eventKind (name : TSyntax `ident) : CommandElabM (EventKind × TSyntax `term) := do
  match name.getId.toString with
  | "ShieldedSpend" => pure (.shieldedSpend, ← `(Noctium.EventKind.shieldedSpend))
  | "ShieldedReceive" => pure (.shieldedReceive, ← `(Noctium.EventKind.shieldedReceive))
  | "ShieldedMint" => pure (.shieldedMint, ← `(Noctium.EventKind.shieldedMint))
  | "ShieldedBurn" => pure (.shieldedBurn, ← `(Noctium.EventKind.shieldedBurn))
  | "UnshieldedSpend" => pure (.unshieldedSpend, ← `(Noctium.EventKind.unshieldedSpend))
  | "UnshieldedReceive" => pure (.unshieldedReceive, ← `(Noctium.EventKind.unshieldedReceive))
  | "UnshieldedMint" => pure (.unshieldedMint, ← `(Noctium.EventKind.unshieldedMint))
  | "UnshieldedBurn" => pure (.unshieldedBurn, ← `(Noctium.EventKind.unshieldedBurn))
  | "Paused" => pure (.paused, ← `(Noctium.EventKind.paused))
  | "Unpaused" => pure (.unpaused, ← `(Noctium.EventKind.unpaused))
  | "Misc" => pure (.misc, ← `(Noctium.EventKind.misc))
  | _ => throwErrorAt name "unknown standard event"

private def serializeEventField (env : Bindings) (source : TSyntax `nlexpr) :
    EventFieldType → CommandElabM (TSyntax `term)
  | .bytes length => checkedExpression env source (.bytes length)
  | .flag => do
    let value ← checkedExpression env source .bool
    `(Noctium.Wire.ScalarCodec.encode $(← wireCodecTerm .bool) $value)
  | .amount => do
    let ty := Ty.uint (2 ^ 128 - 1)
    let value ← checkedExpression env source ty
    `(Noctium.Wire.ScalarCodec.encode $(← wireCodecTerm ty) $value)

private partial def concatenateEventFields : List (Nat × TSyntax `term) →
    CommandElabM (TSyntax `term)
  | [] => `(Noctium.Expr.bytesLiteral 0 [])
  | [(_, field)] => pure field
  | fields => do
    -- A balanced tree keeps wide fields from being encoded after every small one.
    let middle := (fields.length + 1) / 2
    let leftFields := fields.take middle
    let rightFields := fields.drop middle
    let left ← concatenateEventFields leftFields
    let right ← concatenateEventFields rightFields
    `(Noctium.Expr.concatBytes
      (leftLength := $(quote (leftFields.map Prod.fst).sum))
      (rightLength := $(quote (rightFields.map Prod.fst).sum)) $left $right)

private def elaborateEvent (env : Bindings) (event : TSyntax `ident)
    (fields : Array (TSyntax `nleventfield)) : CommandElabM (TSyntax `term) := do
  let (kind, kindTerm) ← eventKind event
  let mut values : List (String × TSyntax `nlexpr) := []
  for field in fields do
    let `(nleventfield| $name:ident := $value:nlexpr) := field
      | throwErrorAt field "expected a named event field"
    let key := name.getId.toString
    unless (kind.fields.lookup key).isSome do
      throwErrorAt name "unknown field '{key}' for event '{event.getId}'"
    if (values.lookup key).isSome then
      throwErrorAt name "duplicate event field '{key}'"
    values := (key, value) :: values
  let encoded ← kind.fields.mapM fun (name, ty) => do
    let some value := values.lookup name | throwErrorAt event "missing event field '{name}'"
    pure (ty.width, ← serializeEventField env value ty)
  let payload ← concatenateEventFields encoded
  `(Noctium.Effect.emitEvent $kindTerm $payload)

private def elaborateEffect (schema : List (String × StateKind))
    (parent : Option (TSyntax `term)) (depth : Nat) (state : EntryEffects)
    (effect : TSyntax `nleffect) : CommandElabM EntryEffects := do
  let optionalHead? : Option (TSyntax `nlpath × TSyntax `ident × TSyntax `ident) :=
    match effect with
    | `(nleffect| headOrDefault $path:nlpath as ($present:ident, $record:ident)) =>
      some (path, present, record)
    | `(nleffect| when $_:nlexpr headOrDefault $path:nlpath as ($present:ident, $record:ident)) =>
      some (path, present, record)
    | _ => none
  if let some (path, present, record) := optionalHead? then
    let guard ← effectGuardTerm state.env parent effect
    let span ← spanTerm effect
    return ← elaborateListHeadOrDefault schema path present record depth guard span state
  let guard ← effectGuardTerm state.env parent effect
  let span ← spanTerm effect
  let mut state := {state with
    spans := state.spans.push span
    guards := state.guards.push guard}
  match effect with
  | `(nleffect| $update:nlupdate)
  | `(nleffect| when $_:nlexpr $update:nlupdate) =>
    match update with
    | `(nlupdate| claimContractCall($address:nlexpr, $payload:nlexpr)) => do
      let some operation := typedClaimOperation payload
        | throwErrorAt payload "two-argument claimContractCall requires callCommitment, optionally wrapped in disclose"
      let address ← checkedExpression state.env address (.bytes 32)
      let commitment ← checkedExpression state.env payload .native
      let digest ← natListTerm (EntryPointHash.hash operation)
      let term ← `(Noctium.Effect.claimContractCall $address (Noctium.Expr.bytes32Literal $digest) $commitment)
      state := {state with terms := state.terms.push term}
    | `(nlupdate| claimContractCall($address:nlexpr, $entryPointHash:nlexpr, $commitment:nlexpr)) => do
      let address ← checkedExpression state.env address (.bytes 32)
      let entryPointHash ← checkedExpression state.env entryPointHash (.bytes 32)
      let commitment ← checkedExpression state.env commitment .native
      let term ← `(Noctium.Effect.claimContractCall $address $entryPointHash $commitment)
      state := {state with terms := state.terms.push term}
    | `(nlupdate| mintShielded($domain:nlexpr, $amount:nlexpr)) => do
      let domain ← checkedExpression state.env domain (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint (2 ^ 64 - 1))
      let term ← `(Noctium.Effect.mintShielded $domain $amount)
      state := {state with terms := state.terms.push term}
    | `(nlupdate| relayShieldedImmediate($nonce:nlexpr, $color:nlexpr,
        $amount:nlexpr, $recipient:nlexpr)) => do
      unless depth == 0 do
        throwErrorAt update "relayShieldedImmediate must be unguarded"
      match guard with
      | `(term| none) => pure ()
      | _ => throwErrorAt update "relayShieldedImmediate must be unguarded"
      let nonce ← checkedExpression state.env nonce (.bytes 32)
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint (2 ^ 128 - 1))
      let recipient ← checkedExpression state.env recipient (.bytes 32)
      let addressName := s!"noctium_relay_address_{state.terms.size}"
      unless state.env.all (fun binding => binding.1 != addressName) do
        throwErrorAt update "reserved relayShieldedImmediate binding collides with an existing read"
      let addressTerm ← `(Noctium.Effect.readContractAddress $(stringTerm addressName))
      state := {state with terms := state.terms.push addressTerm}
      state ← bindReadName state addressName addressName (.bytes 32)
      let selfAddress ← `(@Noctium.Expr.ref (Noctium.Ty.bytes 32) $(stringTerm addressName))
      let relayTerm ← `(Noctium.Effect.relayShieldedImmediate
        $nonce $color $amount $recipient $selfAddress)
      let noGuard ← `(none)
      state := {state with
        terms := state.terms.push relayTerm
        spans := state.spans.push span
        guards := state.guards.push noGuard}
    | `(nlupdate| insertShieldedCoinSet($storage:ident, $nonce:nlexpr,
        $color:nlexpr, $amount:nlexpr)) => do
      unless depth == 0 do
        throwErrorAt update "insertShieldedCoinSet must be unguarded"
      match guard with
      | `(term| none) => pure ()
      | _ => throwErrorAt update "insertShieldedCoinSet must be unguarded"
      let treeSchema ← treeStateSchema schema storage
      let .shieldedCoinSet environment recordType := treeSchema
        | throwErrorAt storage "insertShieldedCoinSet requires a root QualifiedShieldedCoinInfo Set"
      match LedgerValueType.shieldedCoinRecordFields environment recordType with
      | .ok _ => pure ()
      | .error message => throwErrorAt storage message
      let nonce ← checkedExpression state.env nonce (.bytes 32)
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint (2 ^ 128 - 1))
      let addressName := s!"noctium_coin_set_address_{state.terms.size}"
      unless state.env.all (fun binding => binding.1 != addressName) do
        throwErrorAt update "reserved insertShieldedCoinSet binding collides with an existing read"
      let addressTerm ← `(Noctium.Effect.readContractAddress $(stringTerm addressName))
      state := {state with terms := state.terms.push addressTerm}
      state ← bindReadName state addressName addressName (.bytes 32)
      let selfAddress ← `(@Noctium.Expr.ref (Noctium.Ty.bytes 32) $(stringTerm addressName))
      let insertTerm ← `(Noctium.Effect.insertShieldedCoinSet
        $(stringTerm storage.getId.toString) $nonce $color $amount $selfAddress)
      let noGuard ← `(none)
      state := {state with
        terms := state.terms.push insertTerm
        spans := state.spans.push span
        guards := state.guards.push noGuard}
    | `(nlupdate| writeShieldedCoinCell($storage:ident, $nonce:nlexpr,
        $color:nlexpr, $amount:nlexpr)) => do
      unless depth == 0 do
        throwErrorAt update "writeShieldedCoinCell must be unguarded"
      match guard with
      | `(term| none) => pure ()
      | _ => throwErrorAt update "writeShieldedCoinCell must be unguarded"
      let treeSchema ← treeStateSchema schema storage
      let .composite environment recordType := treeSchema
        | throwErrorAt storage "writeShieldedCoinCell requires a root qualified coin Cell"
      match LedgerValueType.shieldedCoinRecordFields environment recordType with
      | .ok _ => pure ()
      | .error message => throwErrorAt storage message
      let nonce ← checkedExpression state.env nonce (.bytes 32)
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint (2 ^ 128 - 1))
      let addressName := s!"noctium_coin_cell_address_{state.terms.size}"
      unless state.env.all (fun binding => binding.1 != addressName) do
        throwErrorAt update "reserved writeShieldedCoinCell binding collides with an existing read"
      let addressTerm ← `(Noctium.Effect.readContractAddress $(stringTerm addressName))
      state := {state with terms := state.terms.push addressTerm}
      state ← bindReadName state addressName addressName (.bytes 32)
      let selfAddress ← `(@Noctium.Expr.ref (Noctium.Ty.bytes 32) $(stringTerm addressName))
      let writeTerm ← `(Noctium.Effect.writeShieldedCoinCell
        $(stringTerm storage.getId.toString) $nonce $color $amount $selfAddress)
      let noGuard ← `(none)
      state := {state with
        terms := state.terms.push writeTerm
        spans := state.spans.push span
        guards := state.guards.push noGuard}
    | `(nlupdate| receiveShieldedToMap($storage:ident, $nonce:nlexpr,
        $color:nlexpr, $amount:nlexpr)) => do
      unless depth == 0 do
        throwErrorAt update "receiveShieldedToMap must be unguarded"
      match guard with
      | `(term| none) => pure ()
      | _ => throwErrorAt update "receiveShieldedToMap must be unguarded"
      let treeSchema ← treeStateSchema schema storage
      let .map keyTy (.composite ..) := treeSchema
        | throwErrorAt storage "receiveShieldedToMap requires a root Bytes32-keyed tree Map"
      unless keyTy == .bytes 32 do
        throwErrorAt storage "receiveShieldedToMap map key must be Bytes32"
      let nonceSyntax := nonce
      let nonce ← checkedExpression state.env nonceSyntax (.bytes 32)
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint (2 ^ 128 - 1))
      let (path, _) ← lowerTreePath state.env treeSchema [nonceSyntax]
      let keys ← pathKeysTerm path
      let memberName := s!"noctium_receive_member_{state.terms.size}"
      let addressName := s!"noctium_receive_address_{state.terms.size}"
      unless state.env.all (fun binding => binding.1 != memberName && binding.1 != addressName) do
        throwErrorAt update "reserved receiveShieldedToMap binding collides with an existing read"
      let memberTerm ← `(Noctium.Effect.memberPath
        $(stringTerm storage.getId.toString) $(stringTerm memberName) $keys)
      state := {state with terms := state.terms.push memberTerm}
      state ← bindReadName state memberName memberName .bool
      let absentCondition ← `(Noctium.Expr.eq
        (Noctium.Expr.ref $(stringTerm memberName)) (Noctium.Expr.bool Bool.false))
      let requireTerm ← `(Noctium.Effect.require $absentCondition)
      state := {state with terms := state.terms.push requireTerm}
      let addressTerm ← `(Noctium.Effect.readContractAddress $(stringTerm addressName))
      state := {state with terms := state.terms.push addressTerm}
      state ← bindReadName state addressName addressName (.bytes 32)
      let selfAddress ← `(@Noctium.Expr.ref (Noctium.Ty.bytes 32) $(stringTerm addressName))
      let receiveTerm ← `(Noctium.Effect.receiveShieldedToMap
        $(stringTerm storage.getId.toString) $nonce $color $amount $selfAddress)
      let noGuard ← `(none)
      state := {state with
        terms := state.terms.push receiveTerm
        spans := state.spans.push span |>.push span |>.push span
        guards := state.guards.push noGuard |>.push noGuard |>.push noGuard}
    | `(nlupdate| spendShieldedFromMap($storage:ident, $nonce:nlexpr, $recipient:nlexpr)) => do
      unless depth == 0 do
        throwErrorAt update "spendShieldedFromMap must be unguarded"
      match guard with
      | `(term| none) => pure ()
      | _ => throwErrorAt update "spendShieldedFromMap must be unguarded"
      let treeSchema ← treeStateSchema schema storage
      let .map keyTy (.composite environment recordType) := treeSchema
        | throwErrorAt storage "spendShieldedFromMap requires a root Bytes32-keyed tree Map"
      unless keyTy == .bytes 32 do
        throwErrorAt storage "spendShieldedFromMap map key must be Bytes32"
      let fields ← match LedgerValueType.shieldedCoinRecordFields environment recordType with
        | .ok fields => pure fields
        | .error message => throwErrorAt storage message
      unless fields.map Prod.fst == ["nonce", "color", "value", "mtIndex"] do
        throwErrorAt storage "spendShieldedFromMap requires the exact shielded coin field order"
      let recipientValue ← checkedExpression state.env recipient (.bytes 32)
      let coinName := s!"noctium_spend_coin_{state.terms.size}"
      let coin := mkIdent (Name.mkSimple coinName)
      state ← elaborateTreeRead storage coin [nonce] treeSchema depth state
      let nonceFieldName := coinName ++ "_nonce"
      let colorFieldName := coinName ++ "_color"
      let amountFieldName := coinName ++ "_value"
      let nonceField := mkIdent (Name.mkSimple nonceFieldName)
      let colorField := mkIdent (Name.mkSimple colorFieldName)
      let amountField := mkIdent (Name.mkSimple amountFieldName)
      let nonceFieldSyntax ← `(nlexpr| $nonceField:ident)
      let colorFieldSyntax ← `(nlexpr| $colorField:ident)
      let amountFieldSyntax ← `(nlexpr| $amountField:ident)
      let nonceRecord ← checkedExpression state.env nonceFieldSyntax (.bytes 32)
      let color ← checkedExpression state.env colorFieldSyntax (.bytes 32)
      let amount ← checkedExpression state.env amountFieldSyntax (.uint (2 ^ 128 - 1))
      let equalitySyntax ← `(nlexpr| eq($nonceFieldSyntax, $nonce))
      let equality ← checkedExpression state.env equalitySyntax .bool
      let requireTerm ← `(Noctium.Effect.require $equality)
      state := {state with terms := state.terms.push requireTerm}
      let addressName := s!"noctium_spend_address_{state.terms.size}"
      unless state.env.all (fun binding => binding.1 != addressName) do
        throwErrorAt update "reserved spendShieldedFromMap binding collides with an existing read"
      let addressTerm ← `(Noctium.Effect.readContractAddress $(stringTerm addressName))
      state := {state with terms := state.terms.push addressTerm}
      state ← bindReadName state addressName addressName (.bytes 32)
      let selfAddress ← `(@Noctium.Expr.ref (Noctium.Ty.bytes 32) $(stringTerm addressName))
      let spendTerm ← `(Noctium.Effect.spendShieldedFromMap
        $(stringTerm storage.getId.toString) $nonceRecord $color $amount $recipientValue $selfAddress)
      state := {state with terms := state.terms.push spendTerm}
      let (path, _) ← lowerTreePath state.env treeSchema [nonce]
      let keys ← pathKeysTerm path
      let removeTerm ← `(Noctium.Effect.removePath $(stringTerm storage.getId.toString) $keys)
      let noGuard ← `(none)
      state := {state with
        terms := state.terms.push removeTerm
        spans := state.spans.push span |>.push span |>.push span |>.push span
        guards := state.guards.push noGuard |>.push noGuard |>.push noGuard |>.push noGuard}
    | `(nlupdate| sendShieldedFromMap($storage:ident, $nonce:nlexpr,
        $sendAmount:nlexpr, $recipient:nlexpr)) => do
      unless depth == 0 do
        throwErrorAt update "sendShieldedFromMap must be unguarded"
      match guard with
      | `(term| none) => pure ()
      | _ => throwErrorAt update "sendShieldedFromMap must be unguarded"
      let treeSchema ← treeStateSchema schema storage
      let .map keyTy (.composite environment recordType) := treeSchema
        | throwErrorAt storage "sendShieldedFromMap requires a root Bytes32-keyed tree Map"
      unless keyTy == .bytes 32 do
        throwErrorAt storage "sendShieldedFromMap map key must be Bytes32"
      let fields ← match LedgerValueType.shieldedCoinRecordFields environment recordType with
        | .ok fields => pure fields
        | .error message => throwErrorAt storage message
      unless fields.map Prod.fst == ["nonce", "color", "value", "mtIndex"] do
        throwErrorAt storage "sendShieldedFromMap requires the exact shielded coin field order"
      let sendAmountValue ← checkedExpression state.env sendAmount (.uint (2 ^ 128 - 1))
      let recipientValue ← checkedExpression state.env recipient (.bytes 32)
      let coinName := s!"noctium_send_coin_{state.terms.size}"
      let coin := mkIdent (Name.mkSimple coinName)
      state ← elaborateTreeRead storage coin [nonce] treeSchema depth state
      let nonceFieldName := coinName ++ "_nonce"
      let colorFieldName := coinName ++ "_color"
      let amountFieldName := coinName ++ "_value"
      let nonceField := mkIdent (Name.mkSimple nonceFieldName)
      let colorField := mkIdent (Name.mkSimple colorFieldName)
      let amountField := mkIdent (Name.mkSimple amountFieldName)
      let nonceFieldSyntax ← `(nlexpr| $nonceField:ident)
      let colorFieldSyntax ← `(nlexpr| $colorField:ident)
      let amountFieldSyntax ← `(nlexpr| $amountField:ident)
      let nonceRecord ← checkedExpression state.env nonceFieldSyntax (.bytes 32)
      let color ← checkedExpression state.env colorFieldSyntax (.bytes 32)
      let inputAmount ← checkedExpression state.env amountFieldSyntax (.uint (2 ^ 128 - 1))
      let equalitySyntax ← `(nlexpr| eq($nonceFieldSyntax, $nonce))
      let equality ← checkedExpression state.env equalitySyntax .bool
      let requireTerm ← `(Noctium.Effect.require $equality)
      state := {state with terms := state.terms.push requireTerm}
      let sendAddressName := s!"noctium_send_address_{state.terms.size}"
      unless state.env.all (fun binding => binding.1 != sendAddressName) do
        throwErrorAt update "reserved sendShieldedFromMap binding collides with an existing read"
      let sendAddressTerm ← `(Noctium.Effect.readContractAddress $(stringTerm sendAddressName))
      state := {state with terms := state.terms.push sendAddressTerm}
      state ← bindReadName state sendAddressName sendAddressName (.bytes 32)
      let sendSelfAddress ← `(@Noctium.Expr.ref (Noctium.Ty.bytes 32) $(stringTerm sendAddressName))
      let sendTerm ← `(Noctium.Effect.sendShieldedFromMap
        $(stringTerm storage.getId.toString) $nonceRecord $color $inputAmount
        $sendAmountValue $recipientValue $sendSelfAddress)
      state := {state with terms := state.terms.push sendTerm}
      let (path, _) ← lowerTreePath state.env treeSchema [nonce]
      let keys ← pathKeysTerm path
      let removeTerm ← `(Noctium.Effect.removePath $(stringTerm storage.getId.toString) $keys)
      state := {state with terms := state.terms.push removeTerm}

      let changeNonce ← `(Noctium.Wire.shieldedChangeNonce $nonceRecord)
      let changeAmount ← `(Noctium.Expr.usub $inputAmount $sendAmountValue)
      let changeKey ← `(Noctium.PathKey.mk (Noctium.Ty.bytes 32) $changeNonce)
      let changeKeys ← pathKeysTerm [changeKey]
      let changeMemberName := s!"noctium_send_change_member_{state.terms.size}"
      unless state.env.all (fun binding => binding.1 != changeMemberName) do
        throwErrorAt update "reserved change membership binding collides with an existing read"
      let memberTerm ← `(Noctium.Effect.memberPath
        $(stringTerm storage.getId.toString) $(stringTerm changeMemberName) $changeKeys)
      state := {state with terms := state.terms.push memberTerm}
      state ← bindReadName state changeMemberName changeMemberName .bool
      let absentCondition ← `(Noctium.Expr.eq
        (Noctium.Expr.ref $(stringTerm changeMemberName)) (Noctium.Expr.bool Bool.false))
      let absentTerm ← `(Noctium.Effect.require $absentCondition)
      state := {state with terms := state.terms.push absentTerm}
      let receiveTerm ← `(Noctium.Effect.receiveShieldedToMap
        $(stringTerm storage.getId.toString) $changeNonce $color $changeAmount $sendSelfAddress)
      let noGuard ← `(none)
      state := {state with
        terms := state.terms.push receiveTerm
        spans := state.spans.push span |>.push span |>.push span |>.push span
          |>.push span |>.push span |>.push span
        guards := state.guards.push noGuard |>.push noGuard |>.push noGuard |>.push noGuard
          |>.push noGuard |>.push noGuard |>.push noGuard}
    | `(nlupdate| mintUnshielded($domain:nlexpr, $amount:nlexpr)) => do
      let domain ← checkedExpression state.env domain (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint (2 ^ 64 - 1))
      let term ← `(Noctium.Effect.mintUnshielded $domain $amount)
      state := {state with terms := state.terms.push term}
    | `(nlupdate| incUnshieldedInputs($color:nlexpr, $amount:nlexpr, $isUnshielded:nlexpr)) => do
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint balanceMaximum)
      let isUnshielded ← checkedExpression state.env isUnshielded .bool
      let term ← `(Noctium.Effect.incUnshieldedInputs $color $amount $isUnshielded)
      state := {state with terms := state.terms.push term}
    | `(nlupdate| incUnshieldedOutputs($color:nlexpr, $amount:nlexpr, $isUnshielded:nlexpr)) => do
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint balanceMaximum)
      let isUnshielded ← checkedExpression state.env isUnshielded .bool
      let term ← `(Noctium.Effect.incUnshieldedOutputs $color $amount $isUnshielded)
      state := {state with terms := state.terms.push term}
    | `(nlupdate| claimUnshieldedCoinSpend($color:nlexpr, $amount:nlexpr,
        $isUnshielded:nlexpr, $isContract:nlexpr, $recipient:nlexpr)) => do
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint balanceMaximum)
      let isUnshielded ← checkedExpression state.env isUnshielded .bool
      let isContract ← checkedExpression state.env isContract .bool
      let recipient ← checkedExpression state.env recipient (.bytes 32)
      let term ← `(Noctium.Effect.claimUnshieldedCoinSpend
        $color $amount $isUnshielded $isContract $recipient)
      state := {state with terms := state.terms.push term}
    | `(nlupdate| requireContractCaller($address:nlexpr)) => do
      let address ← checkedExpression state.env address (.bytes 32)
      let term ← `(Noctium.Effect.requireContractCaller $address)
      state := {state with terms := state.terms.push term}
    | `(nlupdate| checkpoint) =>
      state := {state with terms := state.terms.push (← `(Noctium.Effect.checkpoint))}
    | `(nlupdate| emitEvent($event:ident)) => do
      let term ← elaborateEvent state.env event #[]
      state := {state with terms := state.terms.push term}
    | `(nlupdate| emitEvent($event:ident, $fields:nleventfield,*)) => do
      let term ← elaborateEvent state.env event fields.getElems
      state := {state with terms := state.terms.push term}
    | _ => throwErrorAt update "unsupported Noctium update"
  | `(nleffect| require $value:nlexpr) =>
    let condition ← checkedExpression state.env value .bool
    let term ← `(Noctium.Effect.require $condition)
    state := {state with terms := state.terms.push term}
  | `(nleffect| when $_:nlexpr require $value:nlexpr) =>
    let condition ← checkedExpression state.env value .bool
    let term ← `(Noctium.Effect.require $condition)
    state := {state with terms := state.terms.push term}
  | `(nleffect| readCaller as ($presentName:ident, $isContractName:ident, $contractName:ident, $userName:ident))
  | `(nleffect| when $_:nlexpr readCaller as ($presentName:ident, $isContractName:ident, $contractName:ident, $userName:ident)) => do
    let mut names := []
    for (destination, ty) in [(presentName, Ty.bool), (isContractName, .bool),
        (contractName, .bytes 32), (userName, .bytes 32)] do
      let (name, updated) ← freshReadName depth state destination
      state ← bindReadName updated destination.getId.toString name ty
      names := names ++ [stringTerm name]
    let term ← `(Noctium.Effect.readCaller {
      present := $(names[0]!), isContract := $(names[1]!),
      contractAddress := $(names[2]!), userAddress := $(names[3]!)})
    state := {state with terms := state.terms.push term}
  | `(nleffect| tokenBalance($color:nlexpr, $tag:nlexpr) as $destination:ident)
  | `(nleffect| when $_:nlexpr tokenBalance($color:nlexpr, $tag:nlexpr) as $destination:ident) =>
    state ← elaborateTokenBalanceRead state depth destination color tag none
  | `(nleffect| tokenBalanceLt($color:nlexpr, $tag:nlexpr, $limit:nlexpr) as $destination:ident)
  | `(nleffect| when $_:nlexpr tokenBalanceLt($color:nlexpr, $tag:nlexpr, $limit:nlexpr) as $destination:ident) =>
    state ← elaborateTokenBalanceRead state depth destination color tag (some (Bool.true, limit))
  | `(nleffect| tokenBalanceGt($color:nlexpr, $tag:nlexpr, $limit:nlexpr) as $destination:ident)
  | `(nleffect| when $_:nlexpr tokenBalanceGt($color:nlexpr, $tag:nlexpr, $limit:nlexpr) as $destination:ident) =>
    state ← elaborateTokenBalanceRead state depth destination color tag (some (Bool.false, limit))
  | `(nleffect| counterLessThan $path:nlpath against $threshold:nlexpr as $destination:ident)
  | `(nleffect| when $_:nlexpr counterLessThan $path:nlpath against $threshold:nlexpr as $destination:ident) =>
    state ← elaborateCounterLessThan schema path threshold destination depth state
  | `(nleffect| read $path:nlpath as $destination:ident)
  | `(nleffect| when $_:nlexpr read $path:nlpath as $destination:ident) =>
    state := ← elaborateNamedPathRead schema "read" path destination depth guard state
  | `(nleffect| readSelf as $destination:ident)
  | `(nleffect| when $_:nlexpr readSelf as $destination:ident) => do
    let (readName, updated) ← freshReadName depth state destination
    let term ← `(Noctium.Effect.readContractAddress $(stringTerm readName))
    state := ← bindReadName {updated with terms := updated.terms.push term}
      destination.getId.toString readName (.bytes 32)
  | `(nleffect| member $path:nlpath as $destination:ident)
  | `(nleffect| when $_:nlexpr member $path:nlpath as $destination:ident) =>
    state := ← elaborateNamedPathRead schema "member" path destination depth guard state
  | `(nleffect| blockTimeBefore($deadline) as $destination:ident)
  | `(nleffect| when $_:nlexpr blockTimeBefore($deadline) as $destination:ident) =>
    state := ← elaborateBlockTimeRead state depth destination Bool.true deadline
  | `(nleffect| blockTimeAfter($deadline) as $destination:ident)
  | `(nleffect| when $_:nlexpr blockTimeAfter($deadline) as $destination:ident) =>
    state := ← elaborateBlockTimeRead state depth destination Bool.false deadline
  | `(nleffect| checkRoot $path:nlpath against $expected:nlexpr as $destination:ident)
  | `(nleffect| when $_:nlexpr checkRoot $path:nlpath against $expected:nlexpr as $destination:ident) => do
    let (storage, keys, _, _, nested) ← lowerMerkleTreePath schema state.env path
    let loweredExpected ← checkedExpression state.env expected .native
    let (readName, updated) ← freshReadName depth state destination
    let term ← if nested then
      `(Noctium.Effect.merkleTreeCheckRootAt
        $(stringTerm storage.getId.toString) $keys $loweredExpected $(stringTerm readName))
    else
      `(Noctium.Effect.merkleTreeCheckRoot
        $(stringTerm storage.getId.toString) $loweredExpected $(stringTerm readName))
    state := ← bindReadName {updated with terms := updated.terms.push term}
      destination.getId.toString readName .bool
  | `(nleffect| $operation:ident $path:nlpath as $destination:ident)
  | `(nleffect| when $_:nlexpr $operation:ident $path:nlpath as $destination:ident) =>
    state := ← elaborateNamedPathRead schema operation.getId.toString path destination depth guard state
  | `(nleffect| write $storage:ident := $value:nlexpr)
  | `(nleffect| when $_:nlexpr write $storage:ident := $value:nlexpr) => do
    let some (.cell ty) := schema.lookup storage.getId.toString
      | throwErrorAt storage "write requires a declared state cell"
    let loweredValue ← checkedExpression state.env value ty
    let term ← `(Noctium.Effect.writeCell
      $(stringTerm storage.getId.toString) $(← tyTerm ty) $loweredValue)
    state := {state with terms := state.terms.push term}
  | `(nleffect| insertHash $path:nlpath := $hash:nlexpr)
  | `(nleffect| when $_:nlexpr insertHash $path:nlpath := $hash:nlexpr) => do
    let (storage, keys, _, _, nested) ← lowerMerkleTreePath schema state.env path
    let hash ← checkedExpression state.env hash (.bytes 32)
    let term ← merkleWriteTerm storage keys hash nested none
    state := {state with terms := state.terms.push term}
  | `(nleffect| insertHashIndex $path:nlpath at $index:nlexpr := $hash:nlexpr)
  | `(nleffect| when $_:nlexpr insertHashIndex $path:nlpath at $index:nlexpr := $hash:nlexpr) => do
    let (storage, keys, _, _, nested) ← lowerMerkleTreePath schema state.env path
    let index ← checkedExpression state.env index (.uint (2 ^ 64 - 1))
    let hash ← checkedExpression state.env hash (.bytes 32)
    let term ← merkleWriteTerm storage keys hash nested (some index)
    state := {state with terms := state.terms.push term}
  | `(nleffect| insertField $path:nlpath := $leaf:nlexpr)
  | `(nleffect| when $_:nlexpr insertField $path:nlpath := $leaf:nlexpr) => do
    let payload ← `(nlledgervalue| $leaf:nlexpr)
    state := ← elaborateTypedMerkleWrite schema path (some payload) none Bool.true state
  | `(nleffect| insertFieldIndex $path:nlpath at $index:nlexpr := $leaf:nlexpr)
  | `(nleffect| when $_:nlexpr insertFieldIndex $path:nlpath at $index:nlexpr := $leaf:nlexpr) => do
    let payload ← `(nlledgervalue| $leaf:nlexpr)
    state := ← elaborateTypedMerkleWrite schema path (some payload) (some index) Bool.true state
  | `(nleffect| insertLeaf $path:nlpath := $leaf:nlledgervalue)
  | `(nleffect| when $_:nlexpr insertLeaf $path:nlpath := $leaf:nlledgervalue) =>
    state := ← elaborateTypedMerkleWrite schema path (some leaf) none Bool.false state
  | `(nleffect| insertLeafIndex $path:nlpath at $index:nlexpr := $leaf:nlledgervalue)
  | `(nleffect| when $_:nlexpr insertLeafIndex $path:nlpath at $index:nlexpr := $leaf:nlledgervalue) =>
    state := ← elaborateTypedMerkleWrite schema path (some leaf) (some index) Bool.false state
  | `(nleffect| insertLeafDefault $path:nlpath at $index:nlexpr)
  | `(nleffect| when $_:nlexpr insertLeafDefault $path:nlpath at $index:nlexpr) =>
    state := ← elaborateTypedMerkleWrite schema path none (some index) Bool.false state
  | `(nleffect| insert $storage:ident [ $key:nlexpr ] := $value:nlexpr)
  | `(nleffect| when $_:nlexpr insert $storage:ident [ $key:nlexpr ] := $value:nlexpr) => do
    let term ← match schema.lookup storage.getId.toString with
      | some (.map keyTy valueTy) => do
        let loweredKey ← checkedExpression state.env key keyTy
        let loweredValue ← checkedExpression state.env value valueTy
        `(Noctium.Effect.writeMap
          $(stringTerm storage.getId.toString) $(← tyTerm keyTy) $(← tyTerm valueTy)
          $loweredKey $loweredValue)
      | some (.tree _) => do
        let treeSchema ← treeStateSchema schema storage
        let (path, selected) ← lowerTreePath state.env treeSchema [key]
        unless selected == .scalar .opaqueBytes do
          throwErrorAt storage "single-key tree insertion currently supports only OpaqueBytes leaves"
        let loweredValue ← checkedExpression state.env value .opaqueBytes
        let keys ← pathKeysTerm path
        `(Noctium.Effect.insertPath $(stringTerm storage.getId.toString) $keys
          Noctium.Ty.opaqueBytes $loweredValue)
      | _ => throwErrorAt storage "insert requires a declared state map or OpaqueBytes tree"
    state := {state with terms := state.terms.push term}
  | `(nleffect| insert $storage:ident [$owner:nlexpr] := emptyMap) => do
    let schema ← treeStateSchema schema storage
    let (path, result) ← lowerTreePath state.env schema [owner]
    let .map _ _ := result | throwErrorAt effect "emptyMap assignment must select a map value"
    let keys ← pathKeysTerm path
    let term ← `(Noctium.Effect.emptyMapPath $(stringTerm storage.getId.toString) $keys)
    state := {state with terms := state.terms.push term}
  | `(nleffect| insert $storage:ident [ $key:nlexpr ] := $payload:nlleaves)
  | `(nleffect| write $storage:ident [ $key:nlexpr ] := $payload:nlleaves) => do
    state ← elaborateCompositePathWrite schema storage [key] payload state
  | `(nleffect| insert $storage:ident [ $owner:nlexpr ] [ $spender:nlexpr ] := $payload:nlleaves)
  | `(nleffect| write $storage:ident [ $owner:nlexpr ] [ $spender:nlexpr ] := $payload:nlleaves) => do
    state ← elaborateCompositePathWrite schema storage [owner, spender] payload state
  | `(nleffect| insert $storage:ident [$owner:nlexpr] [$spender:nlexpr] := $value:nlexpr)
  | `(nleffect| write $storage:ident [$owner:nlexpr] [$spender:nlexpr] := $value:nlexpr) => do
    let schema ← treeStateSchema schema storage
    let (path, result) ← lowerTreePath state.env schema [owner, spender]
    let .scalar ty := result | throwErrorAt effect "nested scalar write must select a scalar value"
    let loweredValue ← checkedExpression state.env value ty
    let keys ← pathKeysTerm path
    let term ← if effect.raw[0].getAtomVal == "insert" then
      `(Noctium.Effect.insertPath $(stringTerm storage.getId.toString) $keys $(← tyTerm ty) $loweredValue)
      else `(Noctium.Effect.writePath $(stringTerm storage.getId.toString) $keys $(← tyTerm ty) $loweredValue)
    state := {state with terms := state.terms.push term}
  | `(nleffect| increment $path:nlpath by $amount:nlexpr)
  | `(nleffect| when $_:nlexpr increment $path:nlpath by $amount:nlexpr) =>
    state := ← elaborateCounterAdjust schema path Bool.false amount state
  | `(nleffect| decrement $path:nlpath by $amount:nlexpr)
  | `(nleffect| when $_:nlexpr decrement $path:nlpath by $amount:nlexpr) =>
    state := ← elaborateCounterAdjust schema path Bool.true amount state
  | `(nleffect| pushFront $path:nlpath := $payload:nlledgervalue)
  | `(nleffect| when $_:nlexpr pushFront $path:nlpath := $payload:nlledgervalue) =>
    state := ← elaborateListPushFront schema path payload state
  | `(nleffect| popFront $path:nlpath)
  | `(nleffect| when $_:nlexpr popFront $path:nlpath) =>
    state := ← elaborateListPopFront schema path state
  | `(nleffect| remove $path:nlpath)
  | `(nleffect| when $_:nlexpr remove $path:nlpath) =>
    state := ← elaborateMapRemove schema path state
  | `(nleffect| insert $path:nlpath)
  | `(nleffect| when $_:nlexpr insert $path:nlpath) =>
    state := ← elaborateSetInsert schema path state
  | `(nleffect| insertDefault $path:nlpath)
  | `(nleffect| when $_:nlexpr insertDefault $path:nlpath) =>
    state := ← elaborateMapDefault schema path state
  | `(nleffect| reset $path:nlpath)
  | `(nleffect| when $_:nlexpr reset $path:nlpath) =>
    state := ← elaborateReset schema path state
  | `(nleffect| resetHistory $path:nlpath)
  | `(nleffect| when $_:nlexpr resetHistory $path:nlpath) => do
    let (storage, keys, _, historic, nested) ← lowerMerkleTreePath schema state.env path
    unless historic do throwErrorAt path "resetHistory requires a declared HistoricMerkleTree"
    let term ← if nested then
      `(Noctium.Effect.merkleTreeResetHistoryAt
        $(stringTerm storage.getId.toString) $keys)
    else
      `(Noctium.Effect.merkleTreeResetHistory $(stringTerm storage.getId.toString))
    state := {state with terms := state.terms.push term}
  | `(nleffect| absent $storage:ident [ $key:nlexpr ]) => do
    if depth > 0 then throwErrorAt effect "absent queries inside if/else blocks are unsupported"
    let some (.map keyTy _) := schema.lookup storage.getId.toString
      | throwErrorAt storage "absent requires a declared state map"
    let loweredKey ← checkedExpression state.env key keyTy
    let term ← `(Noctium.Effect.requireAbsent
      $(stringTerm storage.getId.toString) $(← tyTerm keyTy) $loweredKey)
    state := {state with terms := state.terms.push term}
  | _ => throwErrorAt effect "unsupported Noctium state effect"
  pure state

private partial def elaborateStatements (schema : List (String × StateKind))
    (parent : Option (TSyntax `term)) (depth : Nat)
    (statements : Array (TSyntax `nlstatement)) (initial : EntryEffects) :
    CommandElabM EntryEffects := do
  let mut state := initial
  for statement in statements do
    match statement with
    | `(nlstatement| $effect:nleffect) =>
      state ← elaborateEffect schema parent depth state effect
    | `(nlstatement| if $condition:nlexpr then { $thenStatements:nlstatement* }
        else { $elseStatements:nlstatement* }) => do
      let condition ← checkedExpression state.env condition .bool
      let parentExpression ← match parent with
        | some expression => pure expression
        | none => `(Noctium.Expr.bool Bool.true)
      let thenPath : Option (TSyntax `term) := some (←
        `(Noctium.Backend.Impact.activityGuardWithin
          $parentExpression $condition))
      let negated ← `(Noctium.Expr.eq $condition (Noctium.Expr.bool Bool.false))
      let elsePath : Option (TSyntax `term) := some (←
        `(Noctium.Backend.Impact.activityGuardWithin
          $parentExpression $negated))
      let branchEnv := state.env
      let afterThen ← elaborateStatements schema thenPath (depth + 1) thenStatements state
      let afterElse ← elaborateStatements schema elsePath (depth + 1) elseStatements
        {afterThen with env := branchEnv}
      state := {afterElse with env := branchEnv}
    | _ => throwErrorAt statement "unsupported Noctium state statement"
  pure state

private def maybeReturnBinding (environment : Bindings) (name : String) :
    Option (Ty × TSyntax `term) := do
  let (_, ty, expression) ← environment.find? (fun binding => binding.1 == name)
  pure (ty, expression)

private def elaborateMaybeReturn (contractName : String) (label : TSyntax `ident)
    (presentName payloadName : TSyntax `ident) (statement : TSyntax `nlreturn)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let labelName := label.getId.toString
  let presentBindingName := presentName.getId.toString
  let payloadBindingName := payloadName.getId.toString
  let some (.bool, presentExpression) := maybeReturnBinding state.env presentBindingName
    | throwErrorAt presentName "returnMaybe tag must reference a Bool binding"
  let some (payloadType, payloadExpression) := maybeReturnBinding state.env payloadBindingName
    | throwErrorAt payloadName "returnMaybe payload must reference a scalar binding"
  let typeId ← match Noctium.Types.Maybe.scalarTypeId contractName payloadType with
    | .ok value => pure value
    | .error message => throwErrorAt statement message
  let _environment ← match Noctium.Types.Maybe.scalarEnvironment typeId payloadType with
    | .ok value => pure value
    | .error message => throwErrorAt statement message
  let fieldTypes ← match Noctium.Types.Maybe.scalarFieldTypes payloadType with
    | .ok value => pure value
    | .error message => throwErrorAt statement message
  let typeIdTerm := stringTerm typeId
  let span ← spanTerm statement
  let mut fieldTerms := #[]
  for (fieldName, fieldTy) in fieldTypes do
    let fieldNameTerm := stringTerm fieldName
    let fieldType ← `(Noctium.Types.CompositeType.scalar $(← tyTerm fieldTy))
    fieldTerms := fieldTerms.push (← `({ name := $fieldNameTerm, type := $fieldType, span := $span : Noctium.Types.Field }))
  let structureTerm ← `({ id := $typeIdTerm, fields := [$fieldTerms,*], span := $span : Noctium.Types.StructDecl })
  let environmentTerm ← `({ structures := [$structureTerm] : Noctium.Types.CompositeEnv })
  let payloadDefault ← match payloadType with
    | .native => `(Noctium.Expr.native 0)
    | .bool => `(Noctium.Expr.bool Bool.false)
    | .uint maximum => `(Noctium.Expr.uint $(natTerm maximum) 0)
    | _ => throwErrorAt statement "returnMaybe payload must be a scalar"
  let canonicalPayload ← `(Noctium.Expr.select $presentExpression $payloadExpression $payloadDefault)
  let isSomeReturnName := s!"{labelName}_is_some"
  let payloadReturnName := s!"{labelName}_value"
  for returnName in [isSomeReturnName, payloadReturnName] do
    if state.env.any (fun binding => binding.1 == returnName) then
      throwErrorAt label s!"structured return field '{returnName}' collides with an input or read binding"
  let isSomeReturn ← `({ name := $(stringTerm isSomeReturnName), ty := Noctium.Ty.native, value := (Noctium.Expr.cast Noctium.Ty.native $presentExpression), span := $span : Noctium.Output })
  let payloadReturn ← `({ name := $(stringTerm payloadReturnName), ty := Noctium.Ty.native, value := (Noctium.Expr.cast Noctium.Ty.native $canonicalPayload), span := $span : Noctium.Output })
  let compositeType ← `(Noctium.Types.CompositeType.structure $typeIdTerm)
  let view ← `({ name := $(stringTerm labelName), environment := $environmentTerm, type := $compositeType, fields := [$(stringTerm isSomeReturnName), $(stringTerm payloadReturnName)] : Noctium.ReturnView })
  pure {state with
    returns := state.returns.push isSomeReturn |>.push payloadReturn
    returnViews := state.returnViews.push view}

private def elaborateReturns (contractName : String) (statements : Array (TSyntax `nlreturn))
    (info : CircuitInfo) (initial : EntryEffects) : CommandElabM EntryEffects := do
  let mut state := initial
  let mut labels : List String := []
  for statement in statements do
    match statement with
    | `(nlreturn| returnMaybe $label:ident as ($present:ident, $payload:ident)) => do
      let labelName := label.getId.toString
      if labels.contains labelName then
        throwErrorAt label "duplicate entry return label '{labelName}'"
      if state.env.any (fun binding => binding.1 == labelName) then
        throwErrorAt label "entry return label '{labelName}' collides with an input or read binding"
      state ← elaborateMaybeReturn contractName label present payload statement state
      labels := labelName :: labels
    | `(nlreturn| return $label:ident : $returnTy:nltype := $value:nlexpr) => do
      let labelName := label.getId.toString
      if labels.contains labelName then
        throwErrorAt label "duplicate entry return label '{labelName}'"
      if state.env.any (fun binding => binding.1 == labelName) then
        throwErrorAt label "entry return label '{labelName}' collides with an input or read binding"
      labels := labelName :: labels
      let ty ← readTy returnTy
      let value ← checkedExpression state.env value ty
      let span ← spanTerm statement
      state := {state with returns := state.returns.push (← `({
        name := $(stringTerm labelName), ty := $(← tyTerm ty), value := $value,
        span := $span : Noctium.Output }))}
    | `(nlreturn| return $label:ident) => do
      let labelName := label.getId.toString
      let some (_, schema, sourceFields) := info.aggregateOutputs.find? (·.1 == labelName)
        | throwErrorAt label "unknown aggregate circuit output '{labelName}'"
      if labels.contains labelName then
        throwErrorAt label "duplicate entry return label '{labelName}'"
      if state.env.any (fun binding => binding.1 == labelName) then
        throwErrorAt label "entry return label '{labelName}' collides with an input or read binding"
      labels := labelName :: labels
      let span ← spanTerm statement
      let mut fields := #[]
      for name in sourceFields do
        unless info.outputs.lookup name == some Ty.native do
          throwErrorAt label "aggregate return requires Native fields"
        let (physical, nextLocal) := chooseBranchLocalName state.env state.usedLocalNames state.nextLocal
        let field := stringTerm physical
        let returnTerm ← `({
          name := $field
          ty := Noctium.Ty.native
          value := @Noctium.Expr.ref Noctium.Ty.native $(stringTerm name)
          span := $span : Noctium.Output })
        state := {
          state with
          nextLocal
          usedLocalNames := physical :: state.usedLocalNames
          returns := state.returns.push returnTerm
        }
        fields := fields.push field
      let view ← `({ $(mkIdent schema) with fields := [$fields,*] : Noctium.ReturnView })
      state := {state with returnViews := state.returnViews.push view}
    | _ => throwErrorAt statement "unsupported Noctium entry return"
  pure state

private def readCompositeField (field : TSyntax `nlcompositefield) :
    CommandElabM (String × Ty) := do
  let `(nlcompositefield| $fieldName:ident : $fieldType:nltype) := field
    | throwErrorAt field "unsupported composite record field"
  pure (fieldName.getId.toString, ← readTy fieldType)

private def elaborateNamedRecord (contractName : Name) (record : TSyntax `ident)
    (recordFields : Array (TSyntax `nlcompositefield)) (owner : Syntax) :
    CommandElabM (Types.CompositeEnv × Types.CompositeType × TSyntax `term × TSyntax `term) := do
  let typeId := contractName.toString ++ "." ++ record.getId.toString
  let mut fieldTerms : Array (TSyntax `term) := #[]
  let mut fieldValues : List Noctium.Types.Field := []
  for field in recordFields do
    let (fieldName, fieldTy) ← readCompositeField field
    fieldValues := fieldValues ++ [{name := fieldName, type := .scalar fieldTy}]
    let fieldTypeTerm ← `(Noctium.Types.CompositeType.scalar $(← tyTerm fieldTy))
    let fieldSpan ← spanTerm field
    fieldTerms := fieldTerms.push (← `({ name := $(stringTerm fieldName), type := $fieldTypeTerm, span := $fieldSpan : Noctium.Types.Field }))
  let structSpan ← spanTerm owner
  let structureTerm ← `({ id := $(stringTerm typeId), fields := [$fieldTerms,*], span := $structSpan : Noctium.Types.StructDecl })
  let environmentTerm ← `({ structures := [$structureTerm] : Noctium.Types.CompositeEnv })
  let compositeType := Types.CompositeType.structure typeId
  let compositeTypeTerm ← `(Noctium.Types.CompositeType.structure $(stringTerm typeId))
  let environment : Types.CompositeEnv := {structures := [{id := typeId, fields := fieldValues}]}
  pure (environment, compositeType, environmentTerm, compositeTypeTerm)

private def elaborateScalarListDecl (keys : List (TSyntax `nltype)) (element : TSyntax `nltype) :
    CommandElabM (StateKind × TSyntax `term) := do
  let elementTy ← readTy element
  let mut valueSchema := LedgerValueType.«list» {} (.scalar elementTy)
  let mut valueTerm ← `(Noctium.LedgerValueType.«list» {}
    (Noctium.Types.CompositeType.scalar $(← tyTerm elementTy)))
  for key in keys.reverse do
    let keyTy ← readTy key
    valueSchema := .map keyTy valueSchema
    valueTerm ← `(Noctium.LedgerValueType.map $(← tyTerm keyTy) $valueTerm)
  pure (.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))

private def elaborateConstructor (source : TSyntax `nlstate)
    (schema : List (String × StateKind)) : CommandElabM (TSyntax `term) := do
  let `(nlstate| constructor($parameters:nlconstructorparam,*) where $initializers:nlconstructorinit* end) := source
    | throwErrorAt source "invalid Noctium constructor declaration"
  let mut parameterTerms : Array (TSyntax `term) := #[]
  let mut scalarBindings : Bindings := []
  let mut opaqueParameters : List String := []
  let mut parameterNames : List String := []
  for parameter in parameters.getElems.toList do
    let (name, parameterType, typeTerm) ← match parameter with
      | `(nlconstructorparam| $id:ident : OpaqueString) => do
        let name := id.getId.toString
        pure (name, ConstructorType.opaqueString, ← `(Noctium.ConstructorType.opaqueString))
      | `(nlconstructorparam| $id:ident : $sourceTy:nltype) => do
        let name := id.getId.toString
        let ty ← readTy sourceTy
        pure (name, ConstructorType.scalar ty,
          ← `(Noctium.ConstructorType.scalar $(← tyTerm ty)))
      | _ => throwErrorAt parameter "unsupported constructor parameter"
    if parameterNames.contains name then throwErrorAt parameter s!"duplicate constructor parameter '{name}'"
    parameterNames := name :: parameterNames
    if parameterType == .opaqueString then
      opaqueParameters := name :: opaqueParameters
    else
      let .scalar ty := parameterType | throwErrorAt parameter "invalid scalar constructor parameter"
      let reference ← `(@Noctium.Expr.ref $(← tyTerm ty) $(stringTerm name))
      scalarBindings := (name, ty, reference) :: scalarBindings
    parameterTerms := parameterTerms.push (← `(Noctium.ConstructorParameter.mk $(stringTerm name) $typeTerm))
  let mut initializerTerms : Array (TSyntax `term) := #[]
  let mut initializedNames : List String := []
  for initializer in initializers do
    let (destination, initializerType, initializerValue) ← match initializer with
      | `(nlconstructorinit| initialize $stateName:ident := $value:nlexpr) => do
        let destination := stateName.getId.toString
        match schema.find? (·.1 == destination) with
        | some (_, .opaqueString) =>
          match value with
          | `(nlexpr| $parameter:ident) =>
            let parameterName := parameter.getId.toString
            unless opaqueParameters.contains parameterName do
              throwErrorAt value "OpaqueString initializer must reference an OpaqueString parameter or literal"
            let typeTerm ← `(Noctium.ConstructorType.opaqueString)
            let valueTerm ← `(Noctium.ConstructorValue.opaqueStringParameter $(stringTerm parameterName))
            pure (destination, ConstructorType.opaqueString, (typeTerm, valueTerm))
          | _ => throwErrorAt value "OpaqueString initializer must reference an OpaqueString parameter or literal"
        | some (_, .cell ty) => do
          let expression ← checkedExpression scalarBindings value ty
          let typeTerm ← `(Noctium.ConstructorType.scalar $(← tyTerm ty))
          let valueTerm ← `(Noctium.ConstructorValue.scalar $expression)
          pure (destination, ConstructorType.scalar ty, (typeTerm, valueTerm))
        | some _ => throwErrorAt stateName "constructor initializers must target cells"
        | none => throwErrorAt stateName s!"constructor initializes unknown state '{destination}'"
      | `(nlconstructorinit| initialize $stateName:ident := $literal:str) => do
        let destination := stateName.getId.toString
        match schema.find? (·.1 == destination) with
        | some (_, .opaqueString) => do
          let typeTerm ← `(Noctium.ConstructorType.opaqueString)
          let valueTerm ← `(Noctium.ConstructorValue.opaqueStringLiteral $(stringTerm literal.getString))
          pure (destination, ConstructorType.opaqueString, (typeTerm, valueTerm))
        | some _ => throwErrorAt literal "string literals initialize only OpaqueString cells"
        | none => throwErrorAt stateName s!"constructor initializes unknown state '{destination}'"
      | _ => throwErrorAt initializer "unsupported constructor initializer"
    if initializedNames.contains destination then
      throwErrorAt initializer s!"duplicate constructor initializer for '{destination}'"
    initializedNames := destination :: initializedNames
    let (typeTerm, valueTerm) := initializerValue
    initializerTerms := initializerTerms.push
      (← `(Noctium.ConstructorInitializer.mk $(stringTerm destination) $typeTerm $valueTerm))
  let parameters := parameterTerms
  let initializers := initializerTerms
  `(some ({parameters := [$parameters,*], initializers := [$initializers,*] : Noctium.Constructor}))

private def checkMerkleLeafWidth (source : Syntax) (fields : List Ty) : CommandElabM Unit := do
  let widths ← fields.mapM fun ty =>
    match merkleLeafWidth ty with
    | some width => pure width
    | none => throwErrorAt source "MerkleTree leaves require Native, Bool, bounded UInt, fixed Bytes, JubjubPoint or a foreign curve value"
  unless widths.sum + 6 ≤ Noctium.maxBytesLength do
    throwErrorAt source s!"MerkleTree leaf exceeds the maximum preimage length of {Noctium.maxBytesLength}"

private def readMerkleSpec (spec : TSyntax `nlmerklespec) : CommandElabM (Nat × MerkleLeafType) := do
  let (depth, leaf) ← match spec with
    | `(nlmerklespec| $depth:num $[of $leaf:nltype]?) => do
      let ty ← match leaf with | none => pure Ty.native | some source => readTy source
      checkMerkleLeafWidth spec [ty]
      pure (depth.getNat, MerkleLeafType.scalar ty)
    | `(nlmerklespec| $depth:num of struct $name:ident { $fields:nlcompositefield* }) => do
      let fields ← fields.toList.mapM readCompositeField
      checkMerkleLeafWidth spec (fields.map Prod.snd)
      let id := name.getId.toString
      let layoutFields : List Types.Field := fields.map fun (field, ty) =>
        {name := field, type := match ty with | .bytes length => .bytes length | _ => .scalar ty}
      let environment : Types.CompositeEnv := {structures := [{id, fields := layoutFields}]}
      match Types.checkedLayout Types.defaultLimits environment (.structure id) with
      | .ok _ => pure (depth.getNat, MerkleLeafType.record fields)
      | .error diagnostic => throwErrorAt spec diagnostic.message
    | _ => throwErrorAt spec "expected a MerkleTree depth and optional leaf type"
  unless 2 ≤ depth && depth ≤ 32 do
    throwErrorAt spec "MerkleTree depth must be between 2 and 32"
  pure (depth, leaf)

private def merkleDeclaration? (state : TSyntax `nlstate) :
    Option (TSyntax `ident × List (TSyntax `nltype) × TSyntax `nlmerklespec × _root_.Bool) :=
  match state with
  | `(nlstate| merkleTree $id:ident : $spec:nlmerklespec) => some (id, [], spec, Bool.false)
  | `(nlstate| historicMerkleTree $id:ident : $spec:nlmerklespec) => some (id, [], spec, Bool.true)
  | `(nlstate| tree $id:ident : $key:nltype => MerkleTree $spec:nlmerklespec) =>
    some (id, [key], spec, Bool.false)
  | `(nlstate| tree $id:ident : $key:nltype => HistoricMerkleTree $spec:nlmerklespec) =>
    some (id, [key], spec, Bool.true)
  | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => MerkleTree $spec:nlmerklespec) =>
    some (id, [outer, inner], spec, Bool.false)
  | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => HistoricMerkleTree $spec:nlmerklespec) =>
    some (id, [outer, inner], spec, Bool.true)
  | _ => none

private def elaborateMerkleState (keys : List (TSyntax `nltype)) (depth : Nat)
    (historic : _root_.Bool) : CommandElabM (StateKind × TSyntax `term) := do
  if keys.isEmpty then
    if historic then
      return (.historicMerkleTree depth, ← `(Noctium.StateKind.historicMerkleTree $(natTerm depth)))
    return (.merkleTree depth, ← `(Noctium.StateKind.merkleTree $(natTerm depth)))
  let historyTerm ← if historic then `(Bool.true) else `(Bool.false)
  let mut schema := LedgerValueType.merkleTree depth historic
  let mut term ← `(Noctium.LedgerValueType.merkleTree $(natTerm depth) $historyTerm)
  for key in keys.reverse do
    let keyTy ← readTy key
    schema := .map keyTy schema
    term ← `(Noctium.LedgerValueType.map $(← tyTerm keyTy) $term)
  pure (.tree schema, ← `(Noctium.StateKind.tree $term))

@[command_elab contractCommand] unsafe def elabContract : CommandElab := fun stx => do
  match stx with
  | `(noctium_contract $name:ident where $states:nlstate* $entries:nlentry* end) =>
    let mut stateTerms : Array (TSyntax `term) := #[]
    let mut schema : List (String × StateKind) := []
    let mut merkleLeafTypes : List (String × MerkleLeafType) := []
    let mut concreteSchema : List StateDecl := []
    let mut stateDeclarations : Array (TSyntax `nlstate) := #[]
    let mut constructorSyntax? : Option (TSyntax `nlstate) := none
    for state in states do
      match state with
      | `(nlstate| constructor($_:nlconstructorparam,*) where $_:nlconstructorinit* end) =>
        if constructorSyntax?.isSome then throwErrorAt state "duplicate constructor declaration"
        constructorSyntax? := some state
      | _ => stateDeclarations := stateDeclarations.push state
    for state in stateDeclarations do
      let merkle ← (merkleDeclaration? state).mapM fun (id, keys, spec, historic) => do
        let (depth, ty) ← readMerkleSpec spec
        let (kind, term) ← elaborateMerkleState keys depth historic
        pure (id, kind, term, ty)
      if let some (id, _, _, ty) := merkle then
        merkleLeafTypes := (id.getId.toString, ty) :: merkleLeafTypes
      let (id, kind, term) ← if let some (id, kind, term, _) := merkle then pure (id, kind, term) else match state with
        | `(nlstate| set $id:ident : struct $record:ident { $recordFields:nlcompositefield* }) => do
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          match LedgerValueType.shieldedCoinRecordFields environment compositeType with
          | .ok _ => pure ()
          | .error message => throwErrorAt state message
          let valueSchema := LedgerValueType.shieldedCoinSet environment compositeType
          let valueTerm ← `(Noctium.LedgerValueType.shieldedCoinSet $environmentTerm $compositeTypeTerm)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| cell $id:ident : struct $record:ident { $recordFields:nlcompositefield* }) => do
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          match LedgerValueType.shieldedCoinRecordFields environment compositeType with
          | .ok _ => pure ()
          | .error message => throwErrorAt state message
          let valueSchema := LedgerValueType.composite environment compositeType
          let valueTerm ← `(Noctium.LedgerValueType.composite $environmentTerm $compositeTypeTerm)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| sealed cell $id:ident : OpaqueString) =>
          pure (id, StateKind.opaqueString, ← `(Noctium.StateKind.opaqueString))
        | `(nlstate| sealed cell $id:ident : $ty:nltype) => do
          let t ← readTy ty
          pure (id, StateKind.cell t, ← `(Noctium.StateKind.cell $(← tyTerm t)))
        | `(nlstate| cell $id:ident : $ty:nltype) => do
          let t ← readTy ty
          pure (id, StateKind.cell t, ← `(Noctium.StateKind.cell $(← tyTerm t)))
        | `(nlstate| map $id:ident : $key:nltype => $value:nltype) => do
          let k ← readTy key
          let v ← readTy value
          pure (id, StateKind.map k v, ← `(Noctium.StateKind.map $(← tyTerm k) $(← tyTerm v)))
        | `(nlstate| set $id:ident : $key:nltype) => do
          let keyTy ← readTy key
          pure (id, StateKind.tree (.set keyTy), ← `(Noctium.StateKind.tree
            (Noctium.LedgerValueType.set $(← tyTerm keyTy))))
        | `(nlstate| tree $id:ident : $key:nltype => Set $memberType:nltype) => do
          let mapKeyTy ← readTy key
          let memberTy ← readTy memberType
          let mapKeyTerm ← tyTerm mapKeyTy
          let memberTerm ← tyTerm memberTy
          let valueSchema := LedgerValueType.map mapKeyTy (.set memberTy)
          let valueTerm ← `(Noctium.LedgerValueType.map $mapKeyTerm
            (Noctium.LedgerValueType.set $memberTerm))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => Set $memberType:nltype) => do
          let outerTy ← readTy outer
          let innerTy ← readTy inner
          let memberTy ← readTy memberType
          let outerTerm ← tyTerm outerTy
          let innerTerm ← tyTerm innerTy
          let memberTerm ← tyTerm memberTy
          let valueSchema := LedgerValueType.map outerTy (.map innerTy (.set memberTy))
          let valueTerm ← `(Noctium.LedgerValueType.map $outerTerm
            (Noctium.LedgerValueType.map $innerTerm
              (Noctium.LedgerValueType.set $memberTerm)))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| counter $id:ident) =>
          pure (id, StateKind.tree .counter, ← `(Noctium.StateKind.tree Noctium.LedgerValueType.counter))
        | `(nlstate| tree $id:ident : $key:nltype => Counter) => do
          let keyTy ← readTy key
          let keyTerm ← tyTerm keyTy
          let valueSchema := LedgerValueType.map keyTy .counter
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree
            (Noctium.LedgerValueType.map $keyTerm Noctium.LedgerValueType.counter)))
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => Counter) => do
          let outerTy ← readTy outer
          let innerTy ← readTy inner
          let outerTerm ← tyTerm outerTy
          let innerTerm ← tyTerm innerTy
          let valueSchema := LedgerValueType.map outerTy (.map innerTy .counter)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree
            (Noctium.LedgerValueType.map $outerTerm
              (Noctium.LedgerValueType.map $innerTerm Noctium.LedgerValueType.counter))))
        | `(nlstate| tree $id:ident : $key:nltype => struct $record:ident { $recordFields:nlcompositefield* }) => do
          let keyTy ← readTy key
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          let valueSchema := LedgerValueType.map keyTy (.composite environment compositeType)
          let valueTerm ← `(Noctium.LedgerValueType.map $(← tyTerm keyTy)
            (Noctium.LedgerValueType.composite $environmentTerm $compositeTypeTerm))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $key:nltype => $value:nltype) => do
          let keyTy ← readTy key
          let valueTy ← readTy value
          unless keyTy == .bytes 32 && valueTy == .opaqueBytes do
            throwErrorAt state "single-key scalar trees currently support only Bytes32 => OpaqueBytes"
          let valueSchema := LedgerValueType.map keyTy (.scalar valueTy)
          let valueTerm ← `(Noctium.LedgerValueType.map $(← tyTerm keyTy)
            (Noctium.LedgerValueType.scalar $(← tyTerm valueTy)))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => struct $record:ident { $recordFields:nlcompositefield* }) => do
          let outerTy ← readTy outer
          let innerTy ← readTy inner
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          let valueSchema := LedgerValueType.map outerTy
            (.map innerTy (.composite environment compositeType))
          let outerTerm ← tyTerm outerTy
          let innerTerm ← tyTerm innerTy
          let valueTerm ← `(Noctium.LedgerValueType.map $outerTerm
            (Noctium.LedgerValueType.map $innerTerm
              (Noctium.LedgerValueType.composite $environmentTerm $compositeTypeTerm)))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| $listKind:ident $id:ident : struct $record:ident { $recordFields:nlcompositefield* }) => do
          unless listKind.getId.toString == "list" do
            throwErrorAt listKind "unsupported recursive List state declaration"
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          let valueSchema := LedgerValueType.«list» environment compositeType
          let valueTerm ← `(Noctium.LedgerValueType.«list» $environmentTerm $compositeTypeTerm)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $key:nltype => $listKind:ident struct $record:ident { $recordFields:nlcompositefield* }) => do
          unless listKind.getId.toString == "List" do
            throwErrorAt listKind "unsupported recursive tree value declaration"
          let keyTy ← readTy key
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          let valueSchema := LedgerValueType.map keyTy (.«list» environment compositeType)
          let valueTerm ← `(Noctium.LedgerValueType.map $(← tyTerm keyTy)
            (Noctium.LedgerValueType.«list» $environmentTerm $compositeTypeTerm))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => $listKind:ident struct $record:ident { $recordFields:nlcompositefield* }) => do
          unless listKind.getId.toString == "List" do
            throwErrorAt listKind "unsupported recursive tree value declaration"
          let outerTy ← readTy outer
          let innerTy ← readTy inner
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          let valueSchema := LedgerValueType.map outerTy
            (.map innerTy (.«list» environment compositeType))
          let outerTerm ← tyTerm outerTy
          let innerTerm ← tyTerm innerTy
          let valueTerm ← `(Noctium.LedgerValueType.map $outerTerm
            (Noctium.LedgerValueType.map $innerTerm
              (Noctium.LedgerValueType.«list» $environmentTerm $compositeTypeTerm)))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| $listKind:ident $id:ident : $element:nltype) => do
          unless listKind.getId.toString == "list" do
            throwErrorAt listKind "expected a scalar List declaration"
          let (kind, term) ← elaborateScalarListDecl [] element
          pure (id, kind, term)
        | `(nlstate| tree $id:ident : $key:nltype => $listKind:ident $element:nltype) => do
          unless listKind.getId.toString == "List" do
            throwErrorAt listKind "expected a List value in the recursive tree"
          let (kind, term) ← elaborateScalarListDecl [key] element
          pure (id, kind, term)
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => $listKind:ident $element:nltype) => do
          unless listKind.getId.toString == "List" do
            throwErrorAt listKind "expected a List value in the recursive tree"
          let (kind, term) ← elaborateScalarListDecl [outer, inner] element
          pure (id, kind, term)
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => $value:nltype) => do
          let outerTy ← readTy outer
          let innerTy ← readTy inner
          let valueTy ← readTy value
          let valueSchema := LedgerValueType.map outerTy
            (.map innerTy (.scalar valueTy))
          let outerTerm ← tyTerm outerTy
          let innerTerm ← tyTerm innerTy
          let valueTerm ← tyTerm valueTy
          pure (id, StateKind.tree valueSchema, ←
            `(Noctium.StateKind.tree
              (Noctium.LedgerValueType.map $outerTerm
                (Noctium.LedgerValueType.map $innerTerm
                  (Noctium.LedgerValueType.scalar $valueTerm)))))
        | _ => throwErrorAt state "unsupported Noctium state declaration"
      if schema.any (fun p => p.1 == id.getId.toString) then throwErrorAt id "duplicate Noctium state"
      schema := schema ++ [(id.getId.toString, kind)]
      concreteSchema := concreteSchema ++ [{name := id.getId.toString, kind := kind, «sealed» := state.raw[0].getAtomVal == "sealed"}]
      if state.raw[0].getAtomVal == "sealed" then
        stateTerms := stateTerms.push (← `(Noctium.StateDecl.mk $(stringTerm id.getId.toString)
          $term Bool.true $(← spanTerm state)))
      else
        stateTerms := stateTerms.push (← `(Noctium.StateDecl.mk $(stringTerm id.getId.toString)
          $term Bool.false $(← spanTerm state)))
    let constructorTerm ← match constructorSyntax? with
      | none => `(none)
      | some ctor => elaborateConstructor ctor schema
    let mut entryTerms : Array (TSyntax `term) := #[]
    let mut entryNames : List Name := []
    for entryStx in entries do
      match entryStx with
      | `(nlentry| entry $id:ident uses $circuit:ident $argumentKeyword:ident [$args,*] where $statements:nlstatement* $returns:nlreturn* end) =>
        unless argumentKeyword.getId == `arguments do
          throwErrorAt argumentKeyword "expected 'arguments' before the call input list"
        if entryNames.contains id.getId then throwErrorAt id "duplicate Noctium entrypoint"
        entryNames := id.getId :: entryNames
        let registry := circuitRegistry.getState (← getEnv)
        let fullName := (← getCurrNamespace) ++ circuit.getId
        let some info := registry.find? (fun i => i.declName == fullName || i.declName == circuit.getId)
          | throwErrorAt circuit "entrypoint requires a registered Noctium circuit"
        unless args.getElems.size ≤ 256 && uniqueNames (args.getElems.toList.map (·.getId.toString)) do
          throwErrorAt id "invalid logical call argument list"
        let mut callInputTerms : Array (TSyntax `term) := #[]
        let mut callInputViews : Array (TSyntax `term) := #[]
        for argument in args.getElems do
          let labelName := argument.getId.toString
          if let some view := info.aggregateInputs.find? (·.name == labelName) then
            let fields ← view.fields.mapM fun (field, ty) => do
              let typeTerm ← tyTerm ty
              `(($(stringTerm field), $typeTerm))
            let fields := fields.toArray
            callInputTerms := callInputTerms ++ (view.fields.map (stringTerm ∘ Prod.fst)).toArray
            callInputViews := callInputViews.push (← `(Noctium.CallInputView.mk $(stringTerm labelName) [$fields,*]))
          else
            if let some allowed := info.witnessCallArguments? then
              unless allowed.contains labelName do
                throwErrorAt argument "hosted call argument must name a scalar or private aggregate source parameter"
            callInputTerms := callInputTerms.push (stringTerm labelName)
        let env ← addReferences [] (info.inputs ++ info.outputs)
        let env ← addLogicalReferences env info.logicalOutputs
        let reserved := statements.toList.flatMap (fun statement => syntaxIdentifiers statement.raw) ++
          returns.toList.flatMap (fun statement => syntaxIdentifiers statement.raw)
        let initial : EntryEffects := {env, merkleLeafTypes, usedLocalNames := reserved}
        let lowered ← elaborateStatements schema none 0 statements initial
        let lowered ← elaborateReturns ((← getCurrNamespace) ++ name.getId).toString returns info lowered
        let circuitTerm := mkIdent info.declName
        let entryName := stringTerm id.getId.toString
        let entrySpan ← spanTerm entryStx
        entryTerms := entryTerms.push (← `(Noctium.Entrypoint.mk $entryName $circuitTerm
          [$callInputTerms,*] [$callInputViews,*] [$lowered.terms,*] [$lowered.returns,*] [$lowered.returnViews,*] $entrySpan
          [$lowered.spans,*] [$lowered.guards,*]))
      | `(nlentry| entry $id:ident uses $circuit:ident where $statements:nlstatement* $returns:nlreturn* end) =>
        if entryNames.contains id.getId then throwErrorAt id "duplicate Noctium entrypoint"
        entryNames := id.getId :: entryNames
        let registry := circuitRegistry.getState (← getEnv)
        let fullName := (← getCurrNamespace) ++ circuit.getId
        let some info := registry.find? (fun i => i.declName == fullName || i.declName == circuit.getId)
          | throwErrorAt circuit "entrypoint requires a registered Noctium circuit"
        let env ← addReferences [] (info.inputs ++ info.outputs)
        let env ← addLogicalReferences env info.logicalOutputs
        let reserved := statements.toList.flatMap (fun statement => syntaxIdentifiers statement.raw) ++
          returns.toList.flatMap (fun statement => syntaxIdentifiers statement.raw)
        let initial : EntryEffects := {env, merkleLeafTypes, usedLocalNames := reserved}
        let lowered ← elaborateStatements schema none 0 statements initial
        let lowered ← elaborateReturns ((← getCurrNamespace) ++ name.getId).toString returns info lowered
        let circuitTerm := mkIdent info.declName
        entryTerms := entryTerms.push (← `({ name := $(stringTerm id.getId.toString), circuit := $circuitTerm, effects := [$lowered.terms,*], returns := [$lowered.returns,*], returnViews := [$lowered.returnViews,*], span := $(← spanTerm entryStx), effectSpans := [$lowered.spans,*], effectGuards := [$lowered.guards,*] : Noctium.Entrypoint }))
      | `(nlentry| entry $id:ident from $source:ident entry $exportName:str end) =>
        if entryNames.contains id.getId then throwErrorAt id "duplicate Noctium entrypoint"
        entryNames := id.getId :: entryNames
        let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
        let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
        let value ← match Witness.compileStateEntrypoint program exportName.getString concreteSchema with
          | .ok value => pure value
          | .error diagnostic => failDisclosure diagnostic *> throwError "structured ledger compilation failed"
        let localCircuitName := name.getId ++ id.getId ++ `circuit
        let fullCircuitName := (← getCurrNamespace) ++ localCircuitName
        let circuitId := mkIdent localCircuitName
        let circuitName := stringTerm fullCircuitName.toString
        let sourceTerm := mkIdent sourceName
        elabCommand (← `(def $circuitId : Noctium.Circuit :=
          match Noctium.Witness.compileStateEntrypoint $sourceTerm $exportName [$stateTerms,*] with
          | .ok compiledEntry => {compiledEntry.circuit with name := $circuitName}
          | .error _ => {name := $circuitName}))
        unsafe checkGeneratedCircuit fullCircuitName
        modifyEnv fun env => circuitRegistry.addEntry env {
          declName := fullCircuitName
          inputs := value.circuit.inputs.map fun input => (input.name, input.ty)
          publicInputs := (value.circuit.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty)
          outputs := []
          stateProgram? := some (sourceName, exportName.getString)}
        let circuitTerm := mkIdent fullCircuitName
        entryTerms := entryTerms.push (← `(
          match Noctium.Witness.compileStateEntrypoint $sourceTerm $exportName [$stateTerms,*] with
          | .ok compiledEntry => {compiledEntry with name := $(stringTerm id.getId.toString), circuit := $circuitTerm}
          | .error _ => {name := $(stringTerm id.getId.toString), circuit := $circuitTerm}))
      | _ => throwErrorAt entryStx "unsupported Noctium entrypoint"
    let span ← spanTerm stx
    let fullName := (← getCurrNamespace) ++ name.getId
    elabCommand (← `(def $name : Noctium.Contract := Noctium.Contract.mk
      $(stringTerm fullName.toString) [$stateTerms,*] $constructorTerm [$entryTerms,*] $span))
    unsafe checkGeneratedContract fullName
    modifyEnv fun e => contractRegistry.addEntry e fullName
  | _ => throwUnsupportedSyntax

@[command_elab interfaceCommand] def elabContractInterface : CommandElab := fun stx => do
  match stx with
  | `(noctium_interface $name:ident where $entries:nlinterfaceentry* end) => do
    let interfaceName := (← getCurrNamespace) ++ name.getId
    unless (← interfaceMethods interfaceName).isEmpty do
      throwErrorAt name s!"contract interface '{interfaceName}' is already declared"
    unless entries.size > 0 do
      throwErrorAt name "contract interfaces require at least one entry"
    let mut methods : Array CallInterface := #[]
    for methodDecl in entries do
      let `(nlinterfaceentry| entry $operation:ident accepts [$arguments,*]
          yields [$results,*]) := methodDecl
        | throwErrorAt methodDecl "invalid contract interface entry"
      let operationName := operation.getId.toString
      if methods.any (·.operation == operationName) then
        throwErrorAt operation s!"duplicate contract interface entry '{operationName}'"
      let (argumentFields, argumentViews) ← elaborateInterfaceValues arguments
      let (resultFields, resultViews) ← elaborateInterfaceValues results
      let argumentCount := (argumentFields.map (Ty.nativeCallFieldCount ∘ Prod.snd)).sum
      let resultCount := (resultFields.map (Ty.nativeCallFieldCount ∘ Prod.snd)).sum
      unless argumentCount ≤ 256 && resultCount ≤ maxEntrypointReturnFields do
        throwErrorAt methodDecl "contract interface ABI exceeds 256 fields"
      methods := methods.push {
        contract := interfaceName
        operation := operationName
        argumentFields
        argumentViews
        resultFields
        resultViews
      }
    elabCommand (← `(def $name : Noctium.ContractInterface := Noctium.ContractInterface.declared))
    modifyEnv fun env => methods.foldl callInterfaceRegistry.addEntry env
  | _ => throwUnsupportedSyntax

@[command_elab implementsCommand] def elabContractImplementation : CommandElab := fun stx => do
  match stx with
  | `(noctium_implements $contract:ident implements $interface:ident) => do
    let contractName ← liftCoreM <| resolveGlobalConstNoOverload contract
    unless (contractRegistry.getState (← getEnv)).contains contractName do
      throwErrorAt contract s!"'{contractName}' is not a declared Noctium contract"
    let interfaceName ← liftCoreM <| resolveGlobalConstNoOverload interface
    let some interfaceDeclaration := (← getEnv).find? interfaceName
      | throwErrorAt interface s!"'{interfaceName}' is not a declared Noctium contract interface"
    unless interfaceDeclaration.type == mkConst ``Noctium.ContractInterface do
      throwErrorAt interface s!"'{interfaceName}' is not a declared Noctium contract interface"
    let declarations ← interfaceMethods interfaceName
    if declarations.isEmpty then
      throwErrorAt interface s!"'{interfaceName}' is not a declared Noctium contract interface"
    let implementations := interfaceImplementationRegistry.getState (← getEnv)
    if implementations.any (fun item =>
        item.contract == contractName && item.interface == interfaceName) then
      throwErrorAt interface s!"contract '{contractName}' already implements '{interfaceName}'"
    let contractEntries := callInterfaceRegistry.getState (← getEnv)
    for expected in declarations do
      let some actual := contractEntries.find? (fun item =>
          item.contract == contractName && item.operation == expected.operation)
        | throwErrorAt contract s!"contract '{contractName}' has no entry '{expected.operation}' required by '{interfaceName}'"
      unless sameCallInterfaceShape expected actual do
        throwErrorAt contract s!"entry '{expected.operation}' does not match interface '{interfaceName}'"
    modifyEnv fun env => interfaceImplementationRegistry.addEntry env {
      contract := contractName
      interface := interfaceName
    }
  | _ => throwUnsupportedSyntax

/-- Structured source declarations support forward references and lexical IDs.
The generated value enters exactly the same circuit registry and compiler. -/
scoped syntax (name := helperCircuitCommand) "noctium_helper_circuit" ident
  "from" ident "entry" str : command

open scoped Noctium

@[command_elab helperCircuitCommand] unsafe def elabHelperCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_helper_circuit $name:ident from $source:ident entry $exportName:str) =>
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
    match ComponentDisclosure.checkProgram program exportName.getString with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let value ← match Helpers.compile program exportName.getString with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "helper compilation failed"
    let fullName := (← getCurrNamespace) ++ name.getId
    let sourceTerm := mkIdent sourceName
    elabCommand (← `(def $name : Noctium.Circuit :=
      match Noctium.Helpers.compile $sourceTerm $exportName with
      | .ok value => {value with name := $(stringTerm fullName.toString)}
      | .error _ => {name := $(stringTerm fullName.toString)}))
    checkGeneratedCircuit fullName
    modifyEnv fun env => circuitRegistry.addEntry env {
      declName := fullName
      inputs := value.inputs.map fun input => (input.name, input.ty)
      publicInputs := (value.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty)
      outputs := value.outputs.map fun item => (item.name, item.ty)
      sourceProgram? := some (sourceName, exportName.getString)
    }
  | _ => throwUnsupportedSyntax

/-- Compile a generic source export into one registered monomorphic helper program.
The compiler later checks this generated concrete program again. -/
scoped syntax (name := genericHelperCircuitCommand) "noctium_generic_circuit" ident
  "from" ident "entry" str : command

open scoped Noctium

@[command_elab genericHelperCircuitCommand] unsafe def elabGenericHelperCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_generic_circuit $name:ident from $source:ident entry $exportName:str) => do
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    let sourceProgram ← evalConstCheck Helpers.Specialization.Program
      ``Helpers.Specialization.Program sourceName
    let specialized ← match Helpers.Specialization.specialize sourceProgram exportName.getString with
      | .ok result => pure result
      | .error diagnostic => failDisclosure diagnostic *> throwError "generic helper specialization failed"
    match ComponentDisclosure.checkProgram specialized.program specialized.exportName with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let value ← match Helpers.compile specialized.program specialized.exportName with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "generic helper compilation failed"
    let fullName := (← getCurrNamespace) ++ name.getId.eraseMacroScopes
    let programName := fullName ++ `specializedProgram
    if (← getEnv).contains programName then
      throwErrorAt name "generated specialized program name collides with an existing declaration"
    let sourceTerm := mkIdent sourceName
    let programIdent := mkIdent programName
    elabCommand (← `(def $programIdent : Noctium.Helpers.Program :=
      match Noctium.Helpers.Specialization.specialize $sourceTerm $exportName with
      | .ok result => result.program
      | .error _ => {}))
    let programTerm := mkIdent programName
    elabCommand (← `(def $name : Noctium.Circuit :=
      match Noctium.Helpers.compile $programTerm $exportName with
      | .ok value => {value with name := $(stringTerm fullName.toString)}
      | .error _ => {name := $(stringTerm fullName.toString)}))
    checkGeneratedCircuit fullName
    let signatureText := (Lean.toJson specialized.signatureArtifact).pretty
    modifyEnv fun env => circuitRegistry.addEntry env {
      declName := fullName
      inputs := value.inputs.map fun input => (input.name, input.ty)
      publicInputs := (value.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty)
      outputs := value.outputs.map fun item => (item.name, item.ty)
      sourceProgram? := some (programName, specialized.exportName)
      specializationArtifact? := some signatureText
    }
  | _ => throwUnsupportedSyntax

/-- Explicit source spelling for component-aware helper circuits. It compiles
through the same checked helper IR and mandatory origin pass. -/
scoped syntax (name := componentCircuitCommand) "noctium_component_circuit" ident
  "from" ident "entry" str : command

@[command_elab componentCircuitCommand] unsafe def elabComponentCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_component_circuit $name:ident from $source:ident entry $exportName:str) =>
    elabHelperCircuit (← `(command| noctium_helper_circuit $name from $source entry $exportName))
  | _ => throwUnsupportedSyntax

/-- Portable host-only execution plans never enter the native circuit registry. -/
scoped syntax (name := controlPlanCommand) "noctium_control" ident
  "from" ident "entry" str : command

open scoped Noctium

@[command_elab controlPlanCommand] unsafe def elabControlPlan : CommandElab := fun stx => do
  match stx with
  | `(noctium_control $name:ident from $source:ident entry $exportName:str) =>
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
    match Control.compile program exportName.getString with
    | .error diagnostic => throwErrorAt stx diagnostic.message
    | .ok _ => pure ()
    let sourceTerm := mkIdent sourceName
    elabCommand (← `(def $name : Lean.Json :=
      match Noctium.Control.compile $sourceTerm $exportName with
      | .ok value => value
      | .error _ => Lean.Json.null))
    let fullName := (← getCurrNamespace) ++ name.getId
    modifyEnv fun env => controlRegistry.addEntry env fullName
  | _ => throwUnsupportedSyntax

scoped syntax (name := witnessCircuitCommand) "noctium_witness_circuit" ident
  "from" ident "entry" str : command

/-- Share checked registration between generated authoring programs and explicit IR sources. -/
unsafe def registerWitnessCircuit (name : Syntax) (sourceName : Name) (exportName : String)
    (outputName : String := "") (observationArtifact? : Option String := none)
    (describeOutputs : Helpers.Program → Witness.Compiled →
      CommandElabM (List (String × Ty × Name) × List (String × Name × List String)) :=
      fun _ _ => pure ([], [])) : CommandElabM Unit := do
    let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
    let fullName := (← getCurrNamespace) ++ name.getId
    let compiled ← match Witness.compile program exportName fullName.toString outputName with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "typed witness compilation failed"
    let (logicalOutputs, aggregateOutputs) ← describeOutputs program compiled
    let sourceTerm := mkIdent sourceName
    let fullNameTerm := stringTerm fullName.toString
    let exportNameTerm := stringTerm exportName
    let outputNameTerm := stringTerm outputName
    let name : TSyntax `ident := ⟨name⟩
    elabCommand (← `(def $name : Noctium.Circuit :=
      match Noctium.Witness.compile $sourceTerm $exportNameTerm $fullNameTerm $outputNameTerm with
      | .ok value => value.circuit
      | .error _ => {name := $fullNameTerm, inputs := [], outputs := [], constraints := []}))
    match Disclosure.circuit compiled.circuit with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let some exported := program.exports.find? (·.name == exportName)
      | throwErrorAt name "unknown witness entrypoint"
    let aggregateInputs ← (exported.compositeInputs.filter (·.visibility == .private)).mapM fun input => do
      let checked ← match Types.checkedLayout {} program.composites input.type input.span with
        | .ok checked => pure checked
        | .error diagnostic => throwError diagnostic.message
      let fields := (Helpers.sourceLeafPaths checked.value input.name).zip (callViewLeafTypes checked.value)
      pure (CallInputView.mk input.name fields)
    modifyEnv fun env => circuitRegistry.addEntry env {
      declName := fullName,
      inputs := compiled.circuit.inputs.map fun input => (input.name, input.ty),
      publicInputs := (compiled.circuit.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty),
      outputs := compiled.circuit.outputs.map fun value => (value.name, value.ty),
      logicalOutputs,
      aggregateOutputs,
      witnessCallArguments? := some (exported.inputs.map (·.name)),
      aggregateInputs,
      sourceProgram? := some (sourceName, exportName)}
    modifyEnv fun env => witnessRegistry.addEntry env {
      circuitName := fullName, sourceName, exportName, outputName, observationArtifact?}
    modifyEnv fun env => checkedWitnesses.modifyState env (·.insert fullName compiled)

@[command_elab witnessCircuitCommand] unsafe def elabWitnessCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_witness_circuit $name:ident from $source:ident entry $exportName:str) =>
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    registerWitnessCircuit name sourceName exportName.getString
  | _ => throwUnsupportedSyntax

private def moduleProgramDeclName (contractName : Name) (ordinal : Nat) : Name :=
  contractName ++ Name.str .anonymous ("__moduleProgram_" ++ toString ordinal)

private def moduleCircuitDeclName (contractName : Name) (outputName : String) : Name :=
  contractName ++ Name.str .anonymous "__moduleCircuit" ++ Name.str .anonymous outputName

private def moduleCapabilities : Capabilities := {
  typedBoolean := Bool.true
  poseidon2 := Bool.true
  persistentHash32 := Bool.true
  persistentHashVector32 := Bool.true
  persistentHashNative := Bool.true
  sha512 := Bool.true
  keccak256 := Bool.true
  bytes32Conversions := Bool.true
  hashToCurve := Bool.true
  jubjub := Bool.true
  foreignValues := Bool.true
  foreignArithmetic := Bool.true
  foreignByteConversions := Bool.true
  stateCells := Bool.true
  stateMaps := Bool.true}

/-- Re-read every registered module definition constant before expansion. -/
unsafe def moduleRegistryForBuild : CommandElabM Modules.Registry := do
  let mut registry : Modules.Registry := {}
  for info in moduleSourceRegistry.getState (← getEnv) do
    let definition ← evalConstCheck Modules.Definition ``Modules.Definition info.definitionName
    registry ← match registry.register info.sourceName definition with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "module registration failed"
  pure registry

/-- Re-expand a registered module root from exact source constants. This is
called by both elaboration and the compiler's mandatory source checks. -/
unsafe def rebuildModuleBuild (buildInfo : ModuleBuildInfo) : CommandElabM ModuleBuildOutput := do
  let registry ← moduleRegistryForBuild
  let request ← evalConstCheck Modules.Request ``Modules.Request buildInfo.requestName
  let expansion ← match Modules.expand registry request.sourceName request.arguments with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module expansion failed"
  let plan ← match expansion.contractPlan expansion.root with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module contract planning failed"
  let groups ← match plan.specializationGroups with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module specialization planning failed"
  let mut sources : List (Name × Helpers.Specialization.Program) := []
  for group in groups do
    let source ← evalConstCheck Helpers.Specialization.Program
      ``Helpers.Specialization.Program group.sourceProgram
    sources := sources ++ [(group.sourceProgram, source)]
  let specialized ← match plan.specializeWithSources {} sources with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module helper specialization failed"
  let mut programs : List (Name × Name × Helpers.Program) := []
  let mut ordinal := 0
  for (sourceName, batch) in specialized.batches do
    let programName := moduleProgramDeclName buildInfo.contractName ordinal
    programs := programs ++ [(sourceName, programName, batch.program)]
    ordinal := ordinal + 1
  let mut circuitInfos : List ModuleCircuitBuildInfo := []
  let mut circuitValues : List Circuit := []
  for source in plan.circuits do
    let some (_, programName, program) := programs.find? (·.1 == source.source.program)
      | throwError "module source program was not specialized"
    match ComponentDisclosure.checkProgram program source.outputName with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let circuit ← match source.kind with
      | .witness => do
        match Witness.compile program source.outputName source.outputName with
        | .ok compiled => pure compiled.circuit
        | .error diagnostic => failDisclosure diagnostic *> throwError "module witness compilation failed"
      | .circuit =>
        match Helpers.compile program source.outputName with
        | .ok compiled => pure compiled
        | .error diagnostic => failDisclosure diagnostic *> throwError "module circuit compilation failed"
      | _ => throwError "module circuit plan contains a non-circuit member"
    match Disclosure.circuit circuit with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let some (_, batch) := specialized.batches.find? (·.1 == source.source.program)
      | throwError "module specialization batch was not retained"
    let some signatureArtifact := batch.signatureArtifactFor source.outputName
      | throwError "module specialization signature is missing"
    let declarationName := moduleCircuitDeclName buildInfo.contractName source.outputName
    circuitInfos := circuitInfos ++ [{
      source
      declarationName
      programName
      program
      circuit
      signatureArtifact}]
    circuitValues := circuitValues ++ [circuit]
  let contract ← match plan.assembleContract buildInfo.contractName.toString circuitValues with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module contract assembly failed"
  match contract.validate moduleCapabilities with
  | .ok _ => pure ()
  | .error diagnostic => failDisclosure diagnostic
  match Disclosure.contract contract with
  | .ok _ => pure ()
  | .error diagnostic => failDisclosure diagnostic
  pure {specialized, contract, programs, circuits := circuitInfos}

private partial def nameTerm : Name → CommandElabM (TSyntax `term)
  | .anonymous => `(Lean.Name.anonymous)
  | .str parent component => do
    let parentTerm ← nameTerm parent
    `(Lean.Name.str $parentTerm $(stringTerm component))
  | .num parent value => do
    let parentTerm ← nameTerm parent
    `(Lean.Name.num $parentTerm $(natTerm value))

private def moduleRegistryTerm : CommandElabM (TSyntax `term) := do
  let infos := moduleSourceRegistry.getState (← getEnv)
  let entries ← infos.toList.toArray.mapM fun info => do
    let sourceName ← nameTerm info.sourceName
    let definition := mkIdent info.definitionName
    `( ({sourceName := $sourceName, definition := $definition : Noctium.Modules.Registered}) )
  let modules ← `(([$entries,*] : List Noctium.Modules.Registered))
  `({modules := $modules : Noctium.Modules.Registry})

private def moduleSourceProgramsTerm (specialized : Modules.SpecializedModule) :
    CommandElabM (TSyntax `term) := do
  let entries ← specialized.batches.toArray.mapM fun (sourceName, _) => do
    let sourceNameTerm ← nameTerm sourceName
    let source := mkIdent sourceName
    `(($sourceNameTerm, $source))
  `(([$entries,*] : List (Lean.Name × Noctium.Helpers.Specialization.Program)))

private def moduleSpecializeTerm (buildInfo : ModuleBuildInfo)
    (specialized : Modules.SpecializedModule) : CommandElabM (TSyntax `term) := do
  let registry ← moduleRegistryTerm
  let request := mkIdent buildInfo.requestName
  let sources ← moduleSourceProgramsTerm specialized
  `(Noctium.Modules.specializeRequestWithSources {} {} $registry $request $sources)

private def moduleProgramBodyTerm (specializeTerm : TSyntax `term) (sourceName : Name) :
    CommandElabM (TSyntax `term) := do
  let sourceNameTerm ← nameTerm sourceName
  `(match ($specializeTerm) with
    | .ok specialized =>
      match specialized.findBatch $sourceNameTerm with
      | some batch => batch.program
      | none => ({} : Noctium.Helpers.Program)
    | .error _ => ({} : Noctium.Helpers.Program))

private def moduleCircuitBodyTerm (source : Modules.ModuleCircuitSource)
    (programName : Name) : CommandElabM (TSyntax `term) := do
  let program := mkIdent programName
  let outputName := stringTerm source.outputName
  match source.kind with
  | .witness =>
    `(match Noctium.Witness.compile $program $outputName $outputName with
      | .ok value => value.circuit
      | .error _ => {name := $outputName, inputs := [], outputs := [], constraints := []})
  | .circuit =>
    `(match Noctium.Helpers.compile $program $outputName with
      | .ok value => value
      | .error _ => {name := $outputName, inputs := [], outputs := [], constraints := []})
  | _ => throwError "module circuit source has an invalid member kind"

scoped syntax (name := moduleSourceCommand) "noctium_module" "from" ident : command

open scoped Noctium

@[command_elab moduleSourceCommand] unsafe def elabModuleSource : CommandElab := fun stx => do
  match stx with
  | `(noctium_module from $source:ident) => do
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    if moduleSourceRegistry.getState (← getEnv) |>.any (·.sourceName == sourceName) then
      throwErrorAt source "Noctium module source identity is already registered"
    let definition ← evalConstCheck Modules.Definition ``Modules.Definition sourceName
    match Modules.registerDefinition sourceName definition with
    | .error diagnostic => failDisclosure diagnostic
    | .ok _ => pure ()
    modifyEnv fun env => moduleSourceRegistry.addEntry env {
      sourceName
      definitionName := sourceName}
  | _ => throwUnsupportedSyntax

scoped syntax (name := moduleContractCommand) "noctium_module_contract" ident
  "from" ident : command

@[command_elab moduleContractCommand] unsafe def elabModuleContract : CommandElab := fun stx => do
  match stx with
  | `(noctium_module_contract $name:ident from $requestSource:ident) => do
    let requestName ← liftCoreM <| resolveGlobalConstNoOverload requestSource
    let fullName := (← getCurrNamespace) ++ name.getId.eraseMacroScopes
    if (← getEnv).contains fullName then
      throwErrorAt name "generated module contract name collides with an existing declaration"
    let buildInfo : ModuleBuildInfo := {contractName := fullName, requestName}
    let builtModule ← rebuildModuleBuild buildInfo
    let specializeTerm ← moduleSpecializeTerm buildInfo builtModule.specialized
    for (sourceName, programName, _) in builtModule.programs do
      let programIdent := mkIdent programName
      if (← getEnv).contains programName then
        throwErrorAt name "generated module program name collides with an existing declaration"
      let body ← moduleProgramBodyTerm specializeTerm sourceName
      elabCommand (← `(def $programIdent : Noctium.Helpers.Program := $body))
    for circuitInfo in builtModule.circuits do
      let circuitIdent := mkIdent circuitInfo.declarationName
      if (← getEnv).contains circuitInfo.declarationName then
        throwErrorAt name "generated module circuit name collides with an existing declaration"
      let body ← moduleCircuitBodyTerm circuitInfo.source circuitInfo.programName
      elabCommand (← `(def $circuitIdent : Noctium.Circuit := $body))
      unsafe checkGeneratedCircuit circuitInfo.declarationName
      let signatureText := (Lean.toJson circuitInfo.signatureArtifact).pretty
      modifyEnv fun env => circuitRegistry.addEntry env {
        declName := circuitInfo.declarationName
        inputs := circuitInfo.circuit.inputs.map fun input => (input.name, input.ty)
        publicInputs := (circuitInfo.circuit.inputs.filter (·.visibility == .public)).map
          fun input => (input.name, input.ty)
        outputs := circuitInfo.circuit.outputs.map fun item => (item.name, item.ty)
        sourceProgram? := some (circuitInfo.programName, circuitInfo.source.outputName)
        specializationArtifact? := some signatureText}
      if circuitInfo.source.kind == .witness then
        modifyEnv fun env => witnessRegistry.addEntry env {
          circuitName := Name.str .anonymous circuitInfo.source.outputName
          sourceName := circuitInfo.programName
          exportName := circuitInfo.source.outputName}
    let circuitTerms := builtModule.circuits.toArray.map fun circuitInfo => mkIdent circuitInfo.declarationName
    let contractNameText := stringTerm fullName.toString
    let contractIdent := mkIdent fullName
    let contractBody ← `(match ($specializeTerm) with
      | .ok specialized =>
        match specialized.plan.assembleContract $contractNameText [$circuitTerms,*] with
        | .ok contract => contract
        | .error _ => {name := $contractNameText : Noctium.Contract}
      | .error _ => {name := $contractNameText : Noctium.Contract})
    elabCommand (← `(def $contractIdent : Noctium.Contract := $contractBody))
    unsafe checkGeneratedContract fullName
    modifyEnv fun env => contractRegistry.addEntry env fullName
    modifyEnv fun env => moduleBuildRegistry.addEntry env buildInfo
  | _ => throwUnsupportedSyntax

end Noctium
