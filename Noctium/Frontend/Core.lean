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
import Noctium.Types.Either
import Noctium.EntryPointHash
import Noctium.Authoring.QuoteCircuit
import Noctium.Wire
import Noctium.ShieldedBurn
import Lean

namespace Noctium
open Lean Elab Command

initialize noctiumNominalUIntTypeRegistry : SimplePersistentEnvExtension
    (String × Noctium.NominalUIntType) (Array (String × Noctium.NominalUIntType)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

/-- Source-only labels for ordinary Field values represented by Native. -/
structure NominalFieldType where
  name : String
  deriving Repr, BEq, DecidableEq

initialize noctiumNominalFieldTypeRegistry : SimplePersistentEnvExtension
    (String × NominalFieldType) (Array (String × NominalFieldType)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

/-- Source-only labels for Midnight address and key values represented by
Bytes32 expressions at circuit and native boundaries. -/
inductive NominalBytes32 where
  | contractAddress
  | userAddress
  | zswapCoinPublicKey
  deriving Repr, BEq, DecidableEq, Inhabited

def NominalBytes32.displayName : NominalBytes32 → String
  | .contractAddress => "ContractAddress"
  | .userAddress => "UserAddress"
  | .zswapCoinPublicKey => "ZswapCoinPublicKey"

def NominalBytes32.declarationId : NominalBytes32 → String
  | .contractAddress => "Noctium.Midnight.ContractAddress"
  | .userAddress => "Noctium.Midnight.UserAddress"
  | .zswapCoinPublicKey => "Noctium.Midnight.ZswapCoinPublicKey"

/-- Declarations registered through the supported Noctium circuit surface. -/
structure CircuitInfo where
  declName : Name
  inputs : List (String × Ty)
  publicInputs : List (String × Ty)
  outputs : List (String × Ty)
  /-- Source-only nominal UInt identities for circuit inputs and outputs. -/
  nominalUIntInputs : List (String × NominalUIntType) := []
  nominalUIntOutputs : List (String × NominalUIntType) := []
  /-- Source-only nominal Field identities on ordinary circuit parameters/results. -/
  nominalFieldInputs : List (String × NominalFieldType) := []
  nominalFieldOutputs : List (String × NominalFieldType) := []
  /-- Interface identities on byte-encoded contract addresses. -/
  contractRefBindings : List (String × Name) := []
  /-- Logical witness-circuit results retained when a grouped helper result is
  expanded into native leaves. The names point to typed Expr constants. -/
  logicalOutputs : List (String × Ty × Name) := []
  /-- Compile-time nominal tags retained alongside byte-string output aliases.
  These tags never enter Expr or the native plan. -/
  nominalBytes32Outputs : List (String × NominalBytes32) := []
  /-- The declared aggregate label and its checked return schema. -/
  aggregateOutputs : List (String × Name × List String) := []
  /-- Hosted call arguments are selected from source parameters, never callback slots. -/
  witnessCallArguments? : Option (List String) := none
  aggregateInputs : List CallInputView := []
  sourceProgram? : Option (Name × String) := none
  /-- Structured ledger bodies are rebuilt from their typed source at export. -/
  stateProgram? : Option (Name × String) := none
  /-- Source nominal identities for scalar cells in the owning structured
  contract. These tags are reapplied when the helper source is rebuilt. -/
  stateNominalUIntCells : List (String × NominalUIntType) := []
  /-- Source nominal Field identities for scalar Cells in the owning
  structured contract. -/
  stateNominalFieldCells : List (String × NominalFieldType) := []
  /-- Source nominal identities for direct Map keys and values in the owning
  structured contract. These tags are reapplied when the helper source is rebuilt. -/
  stateNominalUIntMaps : List (String × NominalUIntMap) := []
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
  argumentContractRefs : List (String × Name) := []
  argumentNominalUInts : List (String × NominalUIntType) := []
  argumentNominalFields : List (String × NominalFieldType) := []
  argumentViews : List (String × List (String × Ty))
  resultFields : List (String × Ty)
  resultContractRefs : List (String × Name) := []
  resultNominalUInts : List (String × NominalUIntType) := []
  resultNominalFields : List (String × NominalFieldType) := []
  resultViews : List (String × List (String × Ty))
  deriving Inhabited

private structure CallInterfaceSourceRefs where
  contract : Name
  operation : String
  argumentContractRefs : List (String × Name) := []
  resultContractRefs : List (String × Name) := []
  argumentNominalUInts : List (String × NominalUIntType) := []
  resultNominalUInts : List (String × NominalUIntType) := []
  argumentNominalFields : List (String × NominalFieldType) := []
  resultNominalFields : List (String × NominalFieldType) := []
  deriving Inhabited

/-- A named Lean declaration whose source metadata defines a checked contract ABI. -/
inductive ContractInterface where
  | declared

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
    callAbiShape actual.resultFields actual.resultViews &&
  expected.argumentFields.map (fun (name, _) => expected.argumentContractRefs.lookup name) ==
    actual.argumentFields.map (fun (name, _) => actual.argumentContractRefs.lookup name) &&
  expected.resultFields.map (fun (name, _) => expected.resultContractRefs.lookup name) ==
    actual.resultFields.map (fun (name, _) => actual.resultContractRefs.lookup name) &&
  expected.argumentFields.map (fun (name, _) => expected.argumentNominalUInts.lookup name) ==
    actual.argumentFields.map (fun (name, _) => actual.argumentNominalUInts.lookup name) &&
  expected.resultFields.map (fun (name, _) => expected.resultNominalUInts.lookup name) ==
    actual.resultFields.map (fun (name, _) => actual.resultNominalUInts.lookup name) &&
  expected.argumentFields.map (fun (name, _) => expected.argumentNominalFields.lookup name) ==
    actual.argumentFields.map (fun (name, _) => actual.argumentNominalFields.lookup name) &&
  expected.resultFields.map (fun (name, _) => expected.resultNominalFields.lookup name) ==
    actual.resultFields.map (fun (name, _) => actual.resultNominalFields.lookup name)

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
scoped syntax (name := nominalUIntTypeName) (priority := low) ident : nltype
scoped syntax "Native" : nltype
scoped syntax "Bool" : nltype
scoped syntax "UInt" num : nltype
scoped syntax "UIntRange" num : nltype
scoped syntax "Bytes32" : nltype
scoped syntax "ContractRef" ident : nltype
scoped syntax "Bytes" num : nltype
scoped syntax "OpaqueBytes" : nltype
scoped syntax "OpaqueString" : nltype
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
scoped syntax (name := noctiumUIntTypeCommand) "noctium_uint_type" ident ":="
  "UInt" num : command

declare_syntax_cat nlexpr
scoped syntax ident : nlexpr
scoped syntax num : nlexpr
scoped syntax "true" : nlexpr
scoped syntax "false" : nlexpr
scoped syntax "let" ident ":=" nlexpr "in" nlexpr : nlexpr
scoped syntax "assertThen(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "assertUnit(" nlexpr ")" : nlexpr
scoped syntax "assertUnit(" nlexpr "," str ")" : nlexpr
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
scoped syntax "boolNot(" nlexpr ")" : nlexpr
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
scoped syntax "nativeToken()" : nlexpr
scoped syntax "tokenType(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "publicAddressContract(" nlexpr ")" : nlexpr
scoped syntax "publicAddressUser(" nlexpr ")" : nlexpr
scoped syntax "persistentHashVector32(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "persistentHashNative(" nlexpr ")" : nlexpr
scoped syntax "persistentHashNativeVector(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "persistentHashFab(" ident "," ident "," "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "transientHashFab(" ident "," ident "," "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "hashToCurveFab(" ident "," ident "," "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "sha512Fab(" ident "," ident "," "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "keccak256Fab(" ident "," ident "," "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "persistentCommitFab(" ident "," ident "," nlexpr "," "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "transientCommitFab(" ident "," ident "," nlexpr "," "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "transientHashNativeVector(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "transientHashValue(" nlexpr ")" : nlexpr
scoped syntax "shieldedOutputNonce(" nlexpr ")" : nlexpr
scoped syntax "shieldedBurnKey(" ")" : nlexpr
scoped syntax "shieldedIndexedNonce(" nlexpr "," nlexpr ")" : nlexpr
declare_syntax_cat nlcallvalue
scoped syntax nlexpr : nlcallvalue
scoped syntax ident ":=" "fields(" nlexpr,* ")" : nlcallvalue
scoped syntax "callCommitment(" ident "," str "," nlexpr ","
  "[" nlcallvalue,* "]" "," "[" nlcallvalue,* "]" ")" : nlexpr
scoped syntax "callCommitment(" str "," nlexpr ","
  "[" nlcallvalue,* "]" "," "[" nlcallvalue,* "]" ")" : nlexpr
scoped syntax "callCommitment(" ident "," ident "," str "," nlexpr ","
  "[" nlcallvalue,* "]" "," "[" nlcallvalue,* "]" ")" : nlexpr
scoped syntax "persistentHashPoint(" nlexpr ")" : nlexpr
scoped syntax "hashToCurve(" "[" nlexpr,* "]" ")" : nlexpr
scoped syntax "toBytes32(" nlexpr ")" : nlexpr
scoped syntax "fromBytes32(" nltype "," nlexpr ")" : nlexpr
scoped syntax "fromBytes(" nltype "," nlexpr ")" : nlexpr
scoped syntax "fromBytesChecked(" nltype "," nlexpr ")" : nlexpr
scoped syntax "serialize(" nlexpr "," num ")" : nlexpr
scoped syntax "toBytes(" nlexpr "," num ")" : nlexpr
scoped syntax "deserialize(" nltype "," nlexpr ")" : nlexpr
scoped syntax "byteAt(" nlexpr "," num ")" : nlexpr
scoped syntax "degradeToNative(" nlexpr ")" : nlexpr
scoped syntax "upgradeFromNative(" nlexpr ")" : nlexpr
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

/-- Expand token-color helpers through the ordinary Bytes32 literal and hash
surface so every frontend path shares the same padding and hashing rules. -/
def expandTokenHelperSyntax (stx : TSyntax `nlexpr) : CommandElabM (Option (TSyntax `nlexpr)) := do
  match stx with
  | `(nlexpr| nativeToken()) =>
    return some (← `(nlexpr| bytes32("")))
  | `(nlexpr| tokenType($domain, $contractAddress)) =>
    return some (← `(nlexpr| persistentHashVector32([bytes32("midnight:derive_token"), $domain, $contractAddress])))
  | _ => return none

declare_syntax_cat nlcstmt
scoped syntax "public" ident ":" nltype : nlcstmt
scoped syntax "private" ident ":" nltype : nlcstmt
scoped syntax "let" ident ":" nltype ":=" nlexpr : nlcstmt
scoped syntax "assert" nlexpr : nlcstmt
scoped syntax "output" ident ":" nltype ":=" nlexpr : nlcstmt
scoped syntax (name := circuitCommand) "noctium_circuit" ident "where" nlcstmt* "end" : command

declare_syntax_cat nlstate
scoped syntax "cell" ident ":" nltype : nlstate
scoped syntax "cell" ident ":" nltype "alignedBytes" : nlstate
scoped syntax "sealed" "cell" ident ":" nltype : nlstate
scoped syntax "sealed" "map" ident ":" nltype "=>" nltype : nlstate
scoped syntax "sealed" "set" ident ":" nltype : nlstate
declare_syntax_cat nlconstructorparam
scoped syntax ident ":" nltype : nlconstructorparam
scoped syntax ident ":" nltype "as" "[" (ident <|> "_"),* "]" : nlconstructorparam
declare_syntax_cat nlconstructorinit
scoped syntax "initialize" ident ":=" nlexpr : nlconstructorinit
scoped syntax "initialize" ident ":=" str : nlconstructorinit
scoped syntax "initializeCounter" ident "from" ident : nlconstructorinit
scoped syntax "insert" ident "[" nlexpr "]" ":=" nlexpr : nlconstructorinit
scoped syntax "when" nlexpr "insert" ident "[" nlexpr "]" ":=" nlexpr : nlconstructorinit
scoped syntax "when" nlexpr "insert" ident "[" nlexpr "]" : nlconstructorinit
scoped syntax "initializeMember" ident "from" ident "[" nlexpr "]" : nlconstructorinit
scoped syntax "insert" ident "[" nlexpr "]" : nlconstructorinit
scoped syntax "increment" ident "by" nlexpr : nlconstructorinit
scoped syntax "when" nlexpr "increment" ident "by" nlexpr : nlconstructorinit
scoped syntax "pushFront" ident ":=" nlexpr : nlconstructorinit
scoped syntax "when" nlexpr "pushFront" ident ":=" nlexpr : nlconstructorinit
scoped syntax "constructor" "(" nlconstructorparam,* ")" "where" nlconstructorinit* "end" : nlstate
scoped syntax "map" ident ":" nltype "=>" nltype : nlstate
scoped syntax "map" ident ":" "Vector(" num "," nltype ")" "=>" nltype : nlstate
scoped syntax "counter" ident : nlstate
scoped syntax "sealed" "counter" ident : nlstate
scoped syntax "sealed" ident ident ":" nltype : nlstate
declare_syntax_cat nlcompositefield
scoped syntax ident ":" nltype : nlcompositefield
scoped syntax ident ":" "struct" ident "{" nlcompositefield* "}" : nlcompositefield
declare_syntax_cat nlmerkleafield
scoped syntax ident ":" nltype : nlmerkleafield
scoped syntax ident ":" "struct" ident "{" nlmerkleafield* "}" : nlmerkleafield
declare_syntax_cat nlmaprecordtail
scoped syntax "struct" ident "{" nlcompositefield* "}" : nlmaprecordtail
scoped syntax ident "struct" ident "{" nlcompositefield* "}" : nlmaprecordtail
scoped syntax nltype "=>" nlmaprecordtail : nlmaprecordtail
scoped syntax "map" ident ":" "Vector(" num "," nltype ")" "=>"
  "struct" ident "{" nlcompositefield* "}" : nlstate
declare_syntax_cat nlmapsettail
scoped syntax "Set" "struct" ident "{" nlcompositefield* "}" : nlmapsettail
scoped syntax nltype "=>" nlmapsettail : nlmapsettail
scoped syntax "cell" ident ":" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "set" ident ":" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "sealed" "set" ident ":" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "set" ident ":" "Vector(" num "," nltype ")" : nlstate
declare_syntax_cat nlmerklespec
scoped syntax num ("of" nltype)? : nlmerklespec
scoped syntax num "of" "struct" ident "{" nlmerkleafield* "}" : nlmerklespec
scoped syntax "merkleTree" ident ":" nlmerklespec : nlstate
scoped syntax "historicMerkleTree" ident ":" nlmerklespec : nlstate
scoped syntax "tree" ident ":" nltype "=>" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" nltype "=>" "struct" ident "{" nlcompositefield* "}" "=>" nltype : nlstate
scoped syntax "tree" ident ":" nltype "=>" "struct" ident "{" nlcompositefield* "}" "=>" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" nltype "=>" "Set" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" "struct" ident "{" nlcompositefield* "}" "=>" nltype : nlstate
scoped syntax "tree" ident ":" "struct" ident "{" nlcompositefield* "}" "=>" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" "struct" ident "{" nlcompositefield* "}" : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" nltype "=>" nlmaprecordtail : nlstate
scoped syntax "tree" ident ":" nltype "=>" nltype "=>" nlmapsettail : nlstate
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
scoped syntax "initialize" ident ":=" nlleaves : nlconstructorinit
scoped syntax "insert" ident "[" nlexpr "]" ":=" nlleaves : nlconstructorinit
scoped syntax "when" nlexpr "insert" ident "[" nlexpr "]" ":=" nlleaves : nlconstructorinit
scoped syntax "insert" ident "[" nlleaves "]" ":=" nlexpr : nlconstructorinit
scoped syntax "when" nlexpr "insert" ident "[" nlleaves "]" ":=" nlexpr : nlconstructorinit
scoped syntax "insert" ident "[" nlleaves "]" ":=" nlleaves : nlconstructorinit
scoped syntax "when" nlexpr "insert" ident "[" nlleaves "]" ":=" nlleaves : nlconstructorinit
scoped syntax "insert" ident "[" nlleaves "]" : nlconstructorinit
scoped syntax "when" nlexpr "insert" ident "[" nlleaves "]" : nlconstructorinit
scoped syntax "pushFront" ident ":=" nlleaves : nlconstructorinit
scoped syntax "when" nlexpr "pushFront" ident ":=" nlleaves : nlconstructorinit

declare_syntax_cat nlledgervalue
scoped syntax nlexpr : nlledgervalue
scoped syntax nlleaves : nlledgervalue

declare_syntax_cat nlpath
scoped syntax ident : nlpath
scoped syntax nlpath "[" nlexpr "]" : nlpath

declare_syntax_cat nlupdate
scoped syntax "claimContractCall" "(" nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "claimContractCall" "(" nlexpr "," nlexpr ")" : nlupdate
scoped syntax "claimShielded" "(" ident "," nlexpr ")" : nlupdate
scoped syntax "mintShielded" "(" nlexpr "," nlexpr ")" : nlupdate
scoped syntax "receiveShieldedToMap" "(" ident "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "insertShieldedCoinSet" "(" nlpath "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "insertShieldedCoinSet" "(" nlpath "," nlexpr "," nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "insertShieldedCoinMap" "(" nlpath "," nlexpr "," nlexpr "," nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "writeShieldedCoinCell" "(" ident "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "writeShieldedCoinCell" "(" ident "," nlexpr "," nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "pushFrontCoin" "(" nlpath "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "pushFrontCoin" "(" nlpath "," nlexpr "," nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "spendShieldedFromMap" "(" ident "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "mergeShieldedFromMap" "(" ident "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "mergeShieldedImmediateFromMap" "(" ident "," nlexpr "," nlexpr "," nlexpr
  "," nlexpr ")" : nlupdate
scoped syntax "sendShieldedFromMap" "(" ident "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "relayShieldedImmediate" "(" nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "mintUnshielded" "(" nlexpr "," nlexpr ")" : nlupdate
scoped syntax "receiveUnshielded" "(" nlexpr "," nlexpr ")" : nlupdate
scoped syntax "incUnshieldedInputs" "(" nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "incUnshieldedOutputs" "(" nlexpr "," nlexpr "," nlexpr ")" : nlupdate
scoped syntax "claimUnshieldedCoinSpendTo" "(" nlexpr "," nlexpr "," nlexpr "," nlexpr ")" : nlupdate
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
scoped syntax "member" ident "[" nlleaves "]" "as" ident : nleffect
scoped syntax "member" ident "[" nlexpr "]" "[" nlleaves "]" "as" ident : nleffect
scoped syntax "read" ident "[" nlleaves "]" "as" ident : nleffect
scoped syntax "read" ident "[" nlexpr "]" "[" nlleaves "]" "as" ident : nleffect
scoped syntax "checkRoot" nlpath "against" nlexpr "as" ident : nleffect
scoped syntax "tokenBalance(" nlexpr "," nlexpr ")" "as" ident : nleffect
scoped syntax "tokenBalanceLt(" nlexpr "," nlexpr "," nlexpr ")" "as" ident : nleffect
scoped syntax "tokenBalanceGt(" nlexpr "," nlexpr "," nlexpr ")" "as" ident : nleffect
scoped syntax "headOrDefault" nlpath "as" "(" ident "," ident ")" : nleffect
scoped syntax "when" nlexpr "headOrDefault" nlpath "as" "(" ident "," ident ")" : nleffect
scoped syntax ident nlpath "as" ident : nleffect
scoped syntax "readCaller" "as" "(" ident "," ident "," ident "," ident ")" : nleffect
scoped syntax "when" nlexpr "readCaller" "as" "(" ident "," ident "," ident "," ident ")" : nleffect
scoped syntax "mintUnshieldedTo(" nlexpr "," nlexpr "," nlexpr "," nlexpr ")" "as" ident : nleffect
scoped syntax "when" nlexpr "mintUnshieldedTo(" nlexpr "," nlexpr "," nlexpr "," nlexpr ")" "as" ident : nleffect
scoped syntax "increment" nlpath "by" nlexpr : nleffect
scoped syntax "decrement" nlpath "by" nlexpr : nleffect
scoped syntax "reset" nlpath : nleffect
scoped syntax "insertDefault" nlpath : nleffect
scoped syntax "insertDefault" ident "[" nlleaves "]" : nleffect
scoped syntax "insertDefault" ident "[" nlexpr "]" "[" nlleaves "]" : nleffect
scoped syntax "resetHistory" nlpath : nleffect
scoped syntax "insertHash" nlpath ":=" nlexpr : nleffect
scoped syntax "insertField" nlpath ":=" nlexpr : nleffect
scoped syntax "require" nlexpr : nleffect
scoped syntax "absent" ident "[" nlexpr "]" : nleffect
scoped syntax "write" ident ":=" nlexpr : nleffect
scoped syntax "write" ident ":=" nlleaves : nleffect
scoped syntax "insert" ident "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "insert" ident "[" nlexpr "]" "[" nlleaves "]" ":=" nlexpr : nleffect
scoped syntax "insert" ident "[" nlexpr "]" "[" nlleaves "]" ":=" nlleaves : nleffect
scoped syntax "insert" ident "[" nlleaves "]" ":=" nlexpr : nleffect
scoped syntax "insert" ident "[" nlleaves "]" ":=" nlleaves : nleffect
scoped syntax "when" nlexpr "insert" ident "[" nlleaves "]" ":=" nlleaves : nleffect
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
scoped syntax "remove" ident "[" nlleaves "]" : nleffect
scoped syntax "remove" ident "[" nlexpr "]" "[" nlleaves "]" : nleffect
scoped syntax "when" nlexpr "remove" ident "[" nlleaves "]" : nleffect
scoped syntax "when" nlexpr "remove" ident "[" nlexpr "]" "[" nlleaves "]" : nleffect
scoped syntax "blockTimeBefore(" nlexpr ")" "as" ident : nleffect
scoped syntax "blockTimeAfter(" nlexpr ")" "as" ident : nleffect
scoped syntax "blockTimeAtOrAfter(" nlexpr ")" "as" ident : nleffect
scoped syntax "blockTimeAtOrBefore(" nlexpr ")" "as" ident : nleffect
scoped syntax "counterLessThan" nlpath "against" nlexpr "as" ident : nleffect
scoped syntax "insert" nlpath : nleffect
scoped syntax "insert" ident "[" nlleaves "]" : nleffect
scoped syntax "insert" ident "[" nlexpr "]" "[" nlleaves "]" : nleffect
scoped syntax "when" nlexpr "write" ident ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "insert" ident "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "insert" ident "[" nlexpr "]" "[" nlleaves "]" ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "insert" ident "[" nlexpr "]" "[" nlleaves "]" ":=" nlleaves : nleffect
scoped syntax "when" nlexpr "insert" ident "[" nlleaves "]" ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "require" nlexpr : nleffect
scoped syntax "when" nlexpr "read" nlpath "as" ident : nleffect
scoped syntax "when" nlexpr "readSelf" "as" ident : nleffect
scoped syntax "when" nlexpr "member" nlpath "as" ident : nleffect
scoped syntax "when" nlexpr "member" ident "[" nlleaves "]" "as" ident : nleffect
scoped syntax "when" nlexpr "member" ident "[" nlexpr "]" "[" nlleaves "]" "as" ident : nleffect
scoped syntax "when" nlexpr "read" ident "[" nlleaves "]" "as" ident : nleffect
scoped syntax "when" nlexpr "read" ident "[" nlexpr "]" "[" nlleaves "]" "as" ident : nleffect
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
scoped syntax "when" nlexpr "insertDefault" ident "[" nlleaves "]" : nleffect
scoped syntax "when" nlexpr "insertDefault" ident "[" nlexpr "]" "[" nlleaves "]" : nleffect
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
scoped syntax "when" nlexpr "remove" ident "[" nlleaves "]" : nleffect
scoped syntax "when" nlexpr "blockTimeBefore(" nlexpr ")" "as" ident : nleffect
scoped syntax "when" nlexpr "blockTimeAfter(" nlexpr ")" "as" ident : nleffect
scoped syntax "when" nlexpr "blockTimeAtOrAfter(" nlexpr ")" "as" ident : nleffect
scoped syntax "when" nlexpr "blockTimeAtOrBefore(" nlexpr ")" "as" ident : nleffect
scoped syntax "when" nlexpr "insert" nlpath : nleffect
scoped syntax "when" nlexpr "insert" ident "[" nlleaves "]" : nleffect
scoped syntax "when" nlexpr "insert" ident "[" nlexpr "]" "[" nlleaves "]" : nleffect

declare_syntax_cat nlstatement
scoped syntax nleffect : nlstatement
scoped syntax "if" nlexpr "then" "{" nlstatement* "}" "else" "{" nlstatement* "}" : nlstatement

declare_syntax_cat nlreturn
scoped syntax "return" ident ":" nltype ":=" nlexpr : nlreturn
scoped syntax "returnMaybe" ident "as" "(" ident "," ident ")" : nlreturn
scoped syntax "returnEither" ident "as" "(" ident "," ident "," ident ")" : nlreturn
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

private def nominalUIntTypeIdentifier (stx : TSyntax `nltype) : Option Syntax := do
  let `(nltype| $name:ident) := stx | none
  pure name.raw

def resolveNominalUIntType (name : Name) (site : Syntax) : CommandElabM NominalUIntType := do
  let registry := noctiumNominalUIntTypeRegistry.getState (← getEnv)
  let current := ((← getCurrNamespace) ++ name).toString
  match registry.find? (·.1 == current) <|> registry.find? (·.1 == name.toString) with
  | some (_, declaration) => pure declaration
  | none => throwErrorAt site s!"unknown nominal UInt type '{name}'"

@[command_elab noctiumUIntTypeCommand] unsafe def elabNoctiumUIntType : CommandElab := fun stx => do
  match stx with
  | `(noctium_uint_type $name:ident := UInt $bits:num) => do
    let fullName := ((← getCurrNamespace) ++ name.getId).toString
    unless Helpers.validWitnessIdentifier fullName do
      throwErrorAt name s!"nominal UInt identity is invalid or too long: {fullName}"
    let registry := noctiumNominalUIntTypeRegistry.getState (← getEnv)
    if registry.any (·.1 == fullName) then
      throwErrorAt name s!"duplicate nominal UInt type '{name.getId}'"
    let maximum ← match ScalarPolicy.sized bits.getNat with
      | .ok (.uint maximum) => pure maximum
      | .error message => throwErrorAt bits message
      | _ => throwErrorAt bits "invalid nominal UInt width"
    let declaration : NominalUIntType := {name := fullName, maximum}
    let typeIdent := mkIdent (name.getId ++ `nominalType)
    let bound : TSyntax `term := ⟨Syntax.mkNumLit (toString maximum)⟩
    elabCommand (← `(def $typeIdent : Noctium.NominalUIntType :=
      {name := $(⟨Syntax.mkStrLit fullName⟩), maximum := $bound}))
    modifyEnv fun env => noctiumNominalUIntTypeRegistry.addEntry env (fullName, declaration)
  | _ => throwUnsupportedSyntax

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
  | `(nltype| OpaqueString) => pure .opaqueString
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

private structure CircuitSourceType where
  type : Ty
  nominalUInt : Option NominalUIntType := none
  nominalField : Option NominalFieldType := none
  contractRef : Option Name := none

private def readCircuitSourceType (stx : TSyntax `nltype)
    (allowNominalField : _root_.Bool := _root_.Bool.false) : CommandElabM CircuitSourceType := do
  if let `(nltype| ContractRef $interface:ident) := stx then
    let name ← liftCoreM <| resolveGlobalConstNoOverload interface
    let declaration ← getConstInfo name
    unless declaration.type.isConstOf ``ContractInterface do
      throwErrorAt interface s!"'{name}' is not a declared contract interface"
    if (← interfaceMethods name).isEmpty then
      throwErrorAt interface s!"'{name}' is not a declared contract interface"
    return {type := .bytes 32, contractRef := some name}
  if let `(nltype| $name:ident) := stx then
    let registry := noctiumNominalFieldTypeRegistry.getState (← getEnv)
    let current := ((← getCurrNamespace) ++ name.getId).toString
    if let some (_, declaration) := registry.find? (·.1 == current) <|>
        registry.find? (·.1 == name.getId.toString) then
      if allowNominalField then
        return {type := .native, nominalField := some declaration}
      throwErrorAt name "nominal Field aliases are only supported in ordinary circuit declarations"
  if let some name := nominalUIntTypeIdentifier stx then
    let declaration ← resolveNominalUIntType name.getId name
    return {type := .uint declaration.maximum, nominalUInt := some declaration}
  return {type := ← readTy stx}

private def tyTerm : Ty → CommandElabM (TSyntax `term)
  | .native => `(Noctium.Ty.native)
  | .bool => `(Noctium.Ty.bool)
  | .uint maximum => `(Noctium.Ty.uint $(⟨Syntax.mkNumLit (toString maximum)⟩))
  | .bytes len => `(Noctium.Ty.bytes $(⟨Syntax.mkNumLit (toString len)⟩))
  | .opaqueBytes => `(Noctium.Ty.opaqueBytes)
  | .opaqueString => `(Noctium.Ty.opaqueString)
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
    CommandElabM (List (String × Ty) × List (String × Name) ×
      List (String × NominalUIntType) ×
      List (String × List (String × Ty))) := do
  let mut fields : List (String × Ty) := []
  let mut contractRefs : List (String × Name) := []
  let mut nominalUInts : List (String × NominalUIntType) := []
  let mut views : List (String × List (String × Ty)) := []
  let mut labels : List String := []
  for value in values do
    let (label, members, refs, memberNominals, isView) ← match value with
      | `(nlinterfacevalue| $field:nlinterfacefield) =>
        match field with
        | `(nlinterfacefield| $name:ident : $type:nltype) => do
          let sourceType ← readCircuitSourceType type
          let refs := (sourceType.contractRef.map fun interface =>
            (name.getId.toString, interface)).toList
          let memberNominals := (sourceType.nominalUInt.map fun nominalUInt =>
            (name.getId.toString, nominalUInt)).toList
          pure (name.getId.toString, [(name.getId.toString, sourceType.type)], refs,
            memberNominals, Bool.false)
        | _ => throwErrorAt field "invalid contract interface field"
      | `(nlinterfacevalue| $label:ident := fields($items:nlinterfacefield,*)) => do
        unless items.getElems.size > 0 do
          throwErrorAt value "contract interface views must contain at least one field"
        let memberValues ← items.getElems.toList.mapM fun
            (item : TSyntax `nlinterfacefield) => do
          let `(nlinterfacefield| $name:ident : $type:nltype) := item
            | throwErrorAt item "invalid contract interface view field"
          let sourceType ← readCircuitSourceType type
          let ref := sourceType.contractRef.map fun interface =>
            (name.getId.toString, interface)
          pure ((name.getId.toString, sourceType.type), ref,
            sourceType.nominalUInt.map fun nominalUInt => (name.getId.toString, nominalUInt))
        pure (label.getId.toString, memberValues.map fun (field, _, _) => field,
          memberValues.flatMap fun (_, ref, _) => ref.toList,
          memberValues.flatMap fun (_, _, nominalUInt) => nominalUInt.toList, Bool.true)
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
    contractRefs := contractRefs ++ refs
    nominalUInts := nominalUInts ++ memberNominals
    if isView then views := views ++ [(label, members)]
  pure (fields, contractRefs, nominalUInts, views)

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

private partial def sigmaExprListTerm : List (TSyntax `term) → CommandElabM (TSyntax `term)
  | [] => `(([] : List (Sigma Noctium.Expr)))
  | value :: rest => do
    let tail ← sigmaExprListTerm rest
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
    CommandElabM (List (String × TSyntax `nlexpr × Ty)) := do
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
    let some (value, ty) := supplied.lookup name
      | throwErrorAt site "missing committed {role} field '{name}'"
    pure (name, value, ty)

private def commitmentHashWith (env : Bindings)
    (expected : TSyntax `nlexpr → Ty → Option Name → Option NominalUIntType →
      CommandElabM (TSyntax `term))
    (interface : CallInterface) (opening : TSyntax `nlexpr)
    (inputs outputs : Array (TSyntax `nlcallvalue)) (stx : TSyntax `nlexpr) :
    CommandElabM (Ty × TSyntax `term) := do
  unless interface.argumentNominalFields.isEmpty && interface.resultNominalFields.isEmpty do
    throwErrorAt stx "nominal Field interface values are unsupported in callCommitment"
  let arguments ← callExpressions "argument" interface.argumentFields interface.argumentViews inputs stx
  let results ← callExpressions "result" interface.resultFields interface.resultViews outputs stx
  let argumentPayload := arguments.map fun (name, value, ty) =>
    (value, ty, interface.argumentContractRefs.lookup name,
      interface.argumentNominalUInts.lookup name)
  let resultPayload := results.map fun (name, value, ty) =>
    (value, ty, interface.resultContractRefs.lookup name,
      interface.resultNominalUInts.lookup name)
  let payload := [(opening, Ty.native, none, none)] ++ argumentPayload ++ resultPayload
  let mut bindings := []
  let mut fields : Array (TSyntax `term) := #[]
  for ((part, ty, contractRef, nominalUInt), index) in payload.zipIdx do
    let value ← expected part ty contractRef nominalUInt
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
  | `(nlexpr| fromBytesChecked($_:nltype, $_:nlexpr)) => Bool.true
  | `(nlexpr| serialize($value, $_:num)) => hasPartialScalar value
  | `(nlexpr| toBytes($value, $width:num)) => width.getNat < 32 || hasPartialScalar value
  | `(nlexpr| fromBytes($_:nltype, $value:nlexpr)) => hasPartialScalar value
  | `(nlexpr| assertThen($_:nlexpr, $_:nlexpr)) => Bool.true
  | `(nlexpr| let $_:ident := $value:nlexpr in $body:nlexpr) =>
    hasPartialScalar value || hasPartialScalar body
  | `(nlexpr| disclose($value)) => hasPartialScalar value
  | `(nlexpr| boolNot($value)) => hasPartialScalar value
  | `(nlexpr| add($a, $b)) | `(nlexpr| mul($a, $b))
  | `(nlexpr| eq($a, $b)) | `(nlexpr| boolAnd($a, $b))
  | `(nlexpr| boolOr($a, $b)) | `(nlexpr| andThen($a, $b))
  | `(nlexpr| orElse($a, $b)) | `(nlexpr| boolXor($a, $b))
  | `(nlexpr| poseidon2($_:num, $a, $b)) =>
    hasPartialScalar a || hasPartialScalar b
  | `(nlexpr| persistentHash32($value)) => hasPartialScalar value
  | `(nlexpr| shieldedOutputNonce($value)) => hasPartialScalar value
  | `(nlexpr| shieldedIndexedNonce($index, $nonce)) =>
    hasPartialScalar index || hasPartialScalar nonce
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
  | `(nlexpr| tokenType($domain, $contractAddress)) =>
    hasPartialScalar domain || hasPartialScalar contractAddress
  | `(nlexpr| persistentHashNative($value)) => hasPartialScalar value
  | `(nlexpr| persistentHashFab($_:ident, $_:ident, [$values,*]))
  | `(nlexpr| transientHashFab($_:ident, $_:ident, [$values,*])) =>
    values.getElems.toList.any hasPartialScalar
  | `(nlexpr| hashToCurveFab($_:ident, $_:ident, [$values,*])) =>
    values.getElems.toList.any hasPartialScalar
  | `(nlexpr| keccak256Fab($_:ident, $_:ident, [$values,*]))
  | `(nlexpr| sha512Fab($_:ident, $_:ident, [$values,*])) =>
    values.getElems.toList.any hasPartialScalar
  | `(nlexpr| persistentCommitFab($_:ident, $_:ident, $opening, [$values,*])) =>
    hasPartialScalar opening || values.getElems.toList.any hasPartialScalar
  | `(nlexpr| transientCommitFab($_:ident, $_:ident, $opening, [$values,*])) =>
    hasPartialScalar opening || values.getElems.toList.any hasPartialScalar
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
  | `(nlexpr| transientHashValue($value)) => hasPartialScalar value
  | `(nlexpr| persistentHashPoint($point)) => hasPartialScalar point
  | `(nlexpr| hashToCurve([$values,*])) => Bool.true
  | `(nlexpr| toBytes32($value)) => hasPartialScalar value
  | `(nlexpr| byteAt($value, $_:num)) => hasPartialScalar value
  | `(nlexpr| degradeToNative($value)) => hasPartialScalar value
  | `(nlexpr| upgradeFromNative($value)) => hasPartialScalar value
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
    if target.isOpaqueString || source.isOpaqueString then
      throwErrorAt stx "OpaqueString does not support scalar casts"
    if target.isJubjub || source.isJubjub || target.isForeign || source.isForeign then
      throwErrorAt stx "curve values require explicit typed conversions"
    if target.isBytes || source.isBytes then
      throwErrorAt stx "byte strings do not support scalar casts"
    pure (target, ← `(Noctium.Expr.cast $(← tyTerm target) $value))
  | `(nlexpr| default($target:nltype)) =>
    let target ← readTy target
    pure (target, ← `(Noctium.GuardedExpression.zeroValue $(← tyTerm target)))
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
  | `(nlexpr| fromBytesChecked($target:nltype, $value)) => do
    let target ← readTy target
    let (valueTy, value) ← expression env value
    let .bytes length := valueTy
      | throwErrorAt stx "fromBytesChecked requires a Bytes expression"
    unless 0 < length do
      throwErrorAt stx "fromBytesChecked requires at least one byte"
    if length > maxBytesLength then
      throwErrorAt stx s!"byte string length exceeds the maximum of {maxBytesLength}"
    match target with
    | .native =>
      pure (.native, ← `(Noctium.Wire.checkedNativeFromBytes $value))
    | .uint maximum =>
      match ScalarPolicy.validate (.uint maximum) with
      | .error message => throwErrorAt stx "{message}"
      | .ok _ =>
        pure (target, ← `(Noctium.Wire.checkedUIntFromBytes $(natTerm maximum) $value))
    | _ => throwErrorAt stx "fromBytesChecked supports only Native and UInt"
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
  | `(nlexpr| toBytes($value, $size:num)) => do
    let (source, value) ← expression env value
    let length := size.getNat
    let target ← match Wire.numericBytesTarget source length with
      | .ok target => pure target
      | .error message => throwErrorAt stx message
    let value ← if target == source then pure value
      else `(Noctium.Expr.cast $(← tyTerm target) $value)
    let codec ← wireCodecTerm target
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
  | `(nlexpr| boolNot($value)) => do
    let value ← expected env value .bool
    pure (.bool, ← `(Noctium.Expr.boolXor $value (Noctium.Expr.bool Bool.true)))
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
  | `(nlexpr| sha512Fab($environment:ident, $type:ident, [$values,*])) => do
    let environmentName ← liftCoreM <| resolveGlobalConstNoOverload environment
    let typeName ← liftCoreM <| resolveGlobalConstNoOverload type
    let environmentTerm : TSyntax `term := ⟨mkIdent environmentName⟩
    let typeTerm : TSyntax `term := ⟨mkIdent typeName⟩
    let sourceValues := values.getElems.toList
    unless !sourceValues.isEmpty && sourceValues.length ≤ Types.defaultLimits.maxExpandedNodes do
      throwErrorAt stx s!"sha512Fab requires 1 to {Types.defaultLimits.maxExpandedNodes} values"
    let encodedValues ← sourceValues.mapM fun sourceValue => do
      let (actualType, value) ← expression env sourceValue
      let actualType ← tyTerm actualType
      `(Sigma.mk $actualType $value)
    let valueList ← sigmaExprListTerm encodedValues
    pure (.bytes 64, ← `(Noctium.Expr.sha512Fab $environmentTerm $typeTerm $valueList))
  | `(nlexpr| keccak256Fab($environment:ident, $type:ident, [$values,*])) => do
    let environmentName ← liftCoreM <| resolveGlobalConstNoOverload environment
    let typeName ← liftCoreM <| resolveGlobalConstNoOverload type
    let environmentTerm : TSyntax `term := ⟨mkIdent environmentName⟩
    let typeTerm : TSyntax `term := ⟨mkIdent typeName⟩
    let sourceValues := values.getElems.toList
    unless !sourceValues.isEmpty && sourceValues.length ≤ Types.defaultLimits.maxExpandedNodes do
      throwErrorAt stx s!"keccak256Fab requires 1 to {Types.defaultLimits.maxExpandedNodes} values"
    let encodedValues ← sourceValues.mapM fun sourceValue => do
      let (actualType, value) ← expression env sourceValue
      let actualType ← tyTerm actualType
      `(Sigma.mk $actualType $value)
    let valueList ← sigmaExprListTerm encodedValues
    pure (.bytes 32, ← `(Noctium.Expr.keccak256Fab $environmentTerm $typeTerm $valueList))
  | `(nlexpr| keccak256($value)) => do
    let (valueTy, value) ← expression env value
    match valueTy with
    | .bytes _ => pure (.bytes 32, ← `(Noctium.Expr.keccak256 $value))
    | .native => do
      let environment ← `(({} : Noctium.Types.CompositeEnv))
      let nativeType ← tyTerm .native
      let payloadType ← `(Noctium.Types.CompositeType.tuple
        [Noctium.Types.CompositeType.scalar $nativeType])
      let payloadValue ← `(Sigma.mk $nativeType $value)
      let payloadValues ← sigmaExprListTerm [payloadValue]
      pure (.bytes 32, ← `(Noctium.Expr.keccak256Fab $environment $payloadType $payloadValues))
    | .foreign (.point .secp256k1) =>
      pure (.bytes 32, ← `(Noctium.Expr.keccak256Secp256k1Point $value))
    | .foreign (.point _) => throwErrorAt stx "keccak256 point overload supports Secp256k1Point"
    | _ => throwErrorAt stx "keccak256 requires a Bytes, Native, or Secp256k1Point expression"
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
  | `(nlexpr| upgradeFromNative($value)) => do
    let value ← expected env value .native
    pure (.bytes 32, ← `(Noctium.Wire.upgradeFromNative $value))
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
  | `(nlexpr| shieldedBurnKey()) =>
    pure (.bytes 32, ← `(Noctium.shieldedBurnAddress.recipient))
  | `(nlexpr| shieldedIndexedNonce($index, $nonce)) => do
    let index ← expected env index (.uint (2 ^ 128 - 1))
    let nonce ← expected env nonce (.bytes 32)
    pure (.bytes 32, ← `(Noctium.Wire.shieldedIndexedNonce $index $nonce))
  | `(nlexpr| bytes32($literal:str)) => do
    let bytes := literal.getString.toUTF8.data.toList.map UInt8.toNat
    if bytes.length > 32 then throwErrorAt stx "Bytes32 string literal exceeds 32 UTF-8 bytes"
    let padded := bytes ++ List.replicate (32 - bytes.length) 0
    let values ← natListTerm padded
    pure (.bytes 32, ← `(Noctium.Expr.bytes32Literal $values))
  | `(nlexpr| nativeToken()) | `(nlexpr| tokenType($_:nlexpr, $_:nlexpr)) => do
    let some expanded ← expandTokenHelperSyntax stx
      | throwErrorAt stx "token helper expansion failed"
    expression env expanded
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
  | `(nlexpr| persistentHashFab($environment:ident, $type:ident, [$values,*])) => do
    let environmentName ← liftCoreM <| resolveGlobalConstNoOverload environment
    let typeName ← liftCoreM <| resolveGlobalConstNoOverload type
    let environmentTerm : TSyntax `term := ⟨mkIdent environmentName⟩
    let typeTerm : TSyntax `term := ⟨mkIdent typeName⟩
    let sourceValues := values.getElems.toList
    unless sourceValues.length ≤ Types.defaultLimits.maxExpandedNodes do
      throwErrorAt stx s!"persistentHashFab accepts at most {Types.defaultLimits.maxExpandedNodes} values"
    let encodedValues ← sourceValues.mapM fun sourceValue => do
      let (actualType, value) ← expression env sourceValue
      let actualType ← tyTerm actualType
      `(Sigma.mk $actualType $value)
    let valueList ← sigmaExprListTerm encodedValues
    pure (.bytes 32, ← `(Noctium.Expr.persistentHashFab $environmentTerm $typeTerm $valueList))
  | `(nlexpr| transientHashFab($environment:ident, $type:ident, [$values,*])) => do
    let environmentName ← liftCoreM <| resolveGlobalConstNoOverload environment
    let typeName ← liftCoreM <| resolveGlobalConstNoOverload type
    let environmentTerm : TSyntax `term := ⟨mkIdent environmentName⟩
    let typeTerm : TSyntax `term := ⟨mkIdent typeName⟩
    let sourceValues := values.getElems.toList
    unless sourceValues.length ≤ Types.defaultLimits.maxVectorLength do
      throwErrorAt stx "transientHashFab accepts at most 1024 logical leaf values"
    let encodedValues ← sourceValues.mapM fun sourceValue => do
      let (actualType, value) ← expression env sourceValue
      let actualType ← tyTerm actualType
      `(Sigma.mk $actualType $value)
    let valueList ← sigmaExprListTerm encodedValues
    pure (.native, ← `(Noctium.Expr.transientHashFab $environmentTerm $typeTerm $valueList))
  | `(nlexpr| persistentCommitFab($environment:ident, $type:ident, $opening, [$values,*])) => do
    let environmentName ← liftCoreM <| resolveGlobalConstNoOverload environment
    let typeName ← liftCoreM <| resolveGlobalConstNoOverload type
    let environmentTerm : TSyntax `term := ⟨mkIdent environmentName⟩
    let typeTerm : TSyntax `term := ⟨mkIdent typeName⟩
    let opening ← expected env opening (.bytes 32)
    let sourceValues := values.getElems.toList
    unless !sourceValues.isEmpty && sourceValues.length ≤ Types.defaultLimits.maxExpandedNodes do
      throwErrorAt stx s!"persistentCommitFab requires 1 to {Types.defaultLimits.maxExpandedNodes} values"
    let encodedValues ← sourceValues.mapM fun sourceValue => do
      let (actualType, value) ← expression env sourceValue
      let actualType ← tyTerm actualType
      `(Sigma.mk $actualType $value)
    let valueList ← sigmaExprListTerm encodedValues
    pure (.bytes 32, ← `(Noctium.Expr.persistentCommitFab $environmentTerm $typeTerm $opening $valueList))
  | `(nlexpr| transientCommitFab($environment:ident, $type:ident, $opening, [$values,*])) => do
    let environmentName ← liftCoreM <| resolveGlobalConstNoOverload environment
    let typeName ← liftCoreM <| resolveGlobalConstNoOverload type
    let environmentTerm : TSyntax `term := ⟨mkIdent environmentName⟩
    let typeTerm : TSyntax `term := ⟨mkIdent typeName⟩
    let opening ← expected env opening .native
    let sourceValues := values.getElems.toList
    unless !sourceValues.isEmpty && sourceValues.length ≤ Types.defaultLimits.maxExpandedNodes do
      throwErrorAt stx s!"transientCommitFab requires 1 to {Types.defaultLimits.maxExpandedNodes} values"
    let encodedValues ← sourceValues.mapM fun sourceValue => do
      let (actualType, value) ← expression env sourceValue
      let actualType ← tyTerm actualType
      `(Sigma.mk $actualType $value)
    let valueList ← sigmaExprListTerm encodedValues
    pure (.native, ← `(Noctium.Expr.transientCommitFab $environmentTerm $typeTerm $opening $valueList))
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
  | `(nlexpr| transientHashValue($source)) => do
    let (ty, value) ← expression env source
    unless (ScalarPolicy.validate ty.scalarKind).isOk do
      throwErrorAt source "transientHashValue requires Native, Bool or UInt"
    let value ← if ty == .native then pure value else `(Noctium.Expr.cast Noctium.Ty.native $value)
    pure (.native, ← `(Noctium.Expr.transientHash [$value]))
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
  | `(nlexpr| hashToCurveFab($environment:ident, $type:ident, [$values,*])) => do
    let environmentName ← liftCoreM <| resolveGlobalConstNoOverload environment
    let typeName ← liftCoreM <| resolveGlobalConstNoOverload type
    let environmentTerm : TSyntax `term := ⟨mkIdent environmentName⟩
    let typeTerm : TSyntax `term := ⟨mkIdent typeName⟩
    let sourceValues := values.getElems.toList
    unless !sourceValues.isEmpty && sourceValues.length ≤ Types.defaultLimits.maxExpandedNodes do
      throwErrorAt stx s!"hashToCurveFab requires 1 to {Types.defaultLimits.maxExpandedNodes} values"
    let encodedValues ← sourceValues.mapM fun sourceValue => do
      let (actualType, value) ← expression env sourceValue
      let actualType ← tyTerm actualType
      `(Sigma.mk $actualType $value)
    let valueList ← sigmaExprListTerm encodedValues
    pure (.jubjubPoint, ← `(Noctium.Expr.hashToCurveFab $environmentTerm $typeTerm $valueList))
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
      (stx : TSyntax `nlexpr) : CommandElabM (Ty × TSyntax `term) :=
    if !interface.argumentContractRefs.isEmpty || !interface.resultContractRefs.isEmpty then
      throwErrorAt stx
        "typed contract reference values require an interface-based claimContractCall"
    else if !interface.argumentNominalUInts.isEmpty || !interface.resultNominalUInts.isEmpty then
      throwErrorAt stx "nominal UInt interface values require a typed contract reference"
    else
      commitmentHashWith env (fun value ty _ _ => expected env value ty)
        interface opening inputs outputs stx
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

private abbrev CircuitNominalEnv := List (String × Option NominalUIntType)

private def circuitNominalEnvironment (info : CircuitInfo) : CircuitNominalEnv :=
  (info.nominalUIntInputs.map fun (name, nominalUInt) => (name, some nominalUInt)) ++
    (info.nominalUIntOutputs.map fun (name, nominalUInt) => (name, some nominalUInt))

private def bindCircuitNominal (env : CircuitNominalEnv) (name : String)
    (nominalUInt : Option NominalUIntType) : CircuitNominalEnv :=
  (name, nominalUInt) :: env.filter (·.1 != name)

private partial def hasCircuitNominalReference (env : CircuitNominalEnv) (stx : Syntax) : _root_.Bool :=
  match stx with
  | .ident _ _ name _ => env.any fun (binding, nominalUInt) =>
      binding == name.toString && nominalUInt.isSome
  | .node _ kind children =>
    kind == ``nominalUIntTypeName || children.toList.any (hasCircuitNominalReference env)
  | _ => _root_.Bool.false

/-- Keep nominal identities while checking low-level circuits. Expr erases source
identity, so every conversion through this boundary must be explicit. -/
private partial def circuitSourceExpression (env : Bindings) (nominalEnv : CircuitNominalEnv)
    (stx : TSyntax `nlexpr) : CommandElabM (Ty × TSyntax `term × Option NominalUIntType) := do
  match stx with
  | `(nlexpr| cast($target:nltype, $value:nlexpr)) => do
    let target ← readCircuitSourceType target
    let (source, value, _) ← circuitSourceExpression env nominalEnv value
    if target.type.isOpaqueBytes || source.isOpaqueBytes then
      throwErrorAt stx "OpaqueBytes do not support scalar casts"
    if target.type.isOpaqueString || source.isOpaqueString then
      throwErrorAt stx "OpaqueString do not support scalar casts"
    if target.type.isJubjub || source.isJubjub || target.type.isForeign || source.isForeign then
      throwErrorAt stx "curve values require explicit typed conversions"
    if target.type.isBytes || source.isBytes then
      throwErrorAt stx "byte strings do not support scalar casts"
    pure (target.type,
      ← `(Noctium.Expr.cast $(← tyTerm target.type) $value), target.nominalUInt)
  | _ =>
    if !hasCircuitNominalReference nominalEnv stx.raw then
      let (type, value) ← expression env stx
      return (type, value, none)
    match stx with
    | `(nlexpr| $id:ident) => do
      let some (_, type, value) := env.find? (fun binding => binding.1 == id.getId.toString)
        | throwErrorAt id s!"unknown Noctium value '{id.getId}'"
      let nominalUInt := (nominalEnv.lookup id.getId.toString).join
      return (type, value, nominalUInt)
    | `(nlexpr| let $id:ident := $value:nlexpr in $body:nlexpr) => do
      let (valueType, valueTerm, valueNominal) ← circuitSourceExpression env nominalEnv value
      let valueTypeTerm ← tyTerm valueType
      let valueRef ← `(Noctium.Expr.ref (ty := $valueTypeTerm) $(stringTerm id.getId.toString))
      let bodyEnv := (id.getId.toString, valueType, valueRef) :: env.filter
        (fun binding => binding.1 != id.getId.toString)
      let bodyNominals := bindCircuitNominal nominalEnv id.getId.toString valueNominal
      let (bodyType, bodyTerm, bodyNominal) ← circuitSourceExpression bodyEnv bodyNominals body
      pure (bodyType,
        ← `(Noctium.Expr.letE $(stringTerm id.getId.toString) $valueTerm $bodyTerm), bodyNominal)
    | `(nlexpr| disclose($value)) => do
      let (type, value, nominalUInt) ← circuitSourceExpression env nominalEnv value
      pure (type, ← `(Noctium.Expr.disclose $(← spanTerm stx) $value), nominalUInt)
    | `(nlexpr| copyValue($value)) => do
      let (type, value, nominalUInt) ← circuitSourceExpression env nominalEnv value
      pure (type, ← `(Noctium.Expr.copyValue $value), nominalUInt)
    | `(nlexpr| assertThen($condition, $body)) => do
      let (conditionType, conditionTerm, conditionNominal) ←
        circuitSourceExpression env nominalEnv condition
      unless conditionType == .bool && conditionNominal.isNone do
        throwErrorAt condition "assertThen condition requires Bool"
      let (bodyType, bodyTerm, bodyNominal) ← circuitSourceExpression env nominalEnv body
      pure (bodyType, ← `(Noctium.Expr.assertE $conditionTerm $bodyTerm), bodyNominal)
    | `(nlexpr| add($left, $right)) =>
      circuitSourceArithmetic env nominalEnv stx .add left right
    | `(nlexpr| sub($left, $right)) =>
      circuitSourceArithmetic env nominalEnv stx .sub left right
    | `(nlexpr| mul($left, $right)) =>
      circuitSourceArithmetic env nominalEnv stx .mul left right
    | `(nlexpr| eq($left, $right)) => do
      let (leftType, leftTerm, leftNominal) ← circuitSourceExpression env nominalEnv left
      let (rightType, rightTerm, rightNominal) ← circuitSourceExpression env nominalEnv right
      unless leftNominal == rightNominal do
        throwErrorAt stx "nominal UInt equality requires matching nominal operands"
      if leftNominal.isSome then
        unless leftType == rightType do
          throwErrorAt stx "nominal UInt equality operands do not match their declared bound"
        pure (.bool, ← `(Noctium.Expr.eq $leftTerm $rightTerm), none)
      else
        let type ← commonType stx leftType rightType
        let leftTerm ← coerceExpression stx leftType type leftTerm
        let rightTerm ← coerceExpression stx rightType type rightTerm
        pure (.bool, ← `(Noctium.Expr.eq $leftTerm $rightTerm), none)
    | `(nlexpr| select($condition, $yes, $no)) => do
      let (conditionType, conditionTerm, conditionNominal) ←
        circuitSourceExpression env nominalEnv condition
      unless conditionType == .bool && conditionNominal.isNone do
        throwErrorAt condition "select condition requires Bool"
      let (yesType, yesTerm, yesNominal) ← circuitSourceExpression env nominalEnv yes
      let (noType, noTerm, noNominal) ← circuitSourceExpression env nominalEnv no
      unless yesNominal == noNominal do
        throwErrorAt stx "select branches require the same nominal UInt type"
      let type ← commonType stx yesType noType
      let yesTerm ← coerceExpression stx yesType type yesTerm
      let noTerm ← coerceExpression stx noType type noTerm
      pure (type, ← `(Noctium.Expr.select $conditionTerm $yesTerm $noTerm), yesNominal)
    | _ => throwErrorAt stx "nominal UInt values require an explicit cast before this operation"
where
  circuitSourceArithmetic (env : Bindings) (nominalEnv : CircuitNominalEnv) (stx : TSyntax `nlexpr)
      (operation : ScalarPolicy.Binary) (left right : TSyntax `nlexpr) :
      CommandElabM (Ty × TSyntax `term × Option NominalUIntType) := do
    let (leftType, leftTerm, leftNominal) ← circuitSourceExpression env nominalEnv left
    let (rightType, rightTerm, rightNominal) ← circuitSourceExpression env nominalEnv right
    unless leftNominal == rightNominal do
      throwErrorAt stx "nominal UInt arithmetic requires matching nominal operands"
    match leftNominal with
    | none =>
      let (type, term) ← expression env stx
      pure (type, term, none)
    | some nominalUInt => do
      unless leftType == .uint nominalUInt.maximum && rightType == .uint nominalUInt.maximum do
        throwErrorAt stx "nominal UInt arithmetic operands do not match their declared bound"
      let result ← match ScalarPolicy.infer operation leftType.scalarKind rightType.scalarKind with
        | .ok result => pure result
        | .error message => throwErrorAt stx message
      let .uint _ := result
        | throwErrorAt stx "nominal UInt arithmetic requires unsigned operands"
      let term ← match operation with
        | .add => `(Noctium.Expr.uadd $leftTerm $rightTerm)
        | .sub => `(Noctium.Expr.usub $leftTerm $rightTerm)
        | .mul => `(Noctium.Expr.umul $leftTerm $rightTerm)
      let bounded ← `(Noctium.Expr.cast $(← tyTerm (.uint nominalUInt.maximum)) $term)
      pure (.uint nominalUInt.maximum, bounded, some nominalUInt)

private def checkedCircuitSourceExpression (env : Bindings) (nominalEnv : CircuitNominalEnv)
    (stx : TSyntax `nlexpr) (target : CircuitSourceType) : CommandElabM (TSyntax `term) := do
  if target.nominalUInt.isNone && !hasCircuitNominalReference nominalEnv stx.raw then
    return ← checkedExpression env stx target.type
  let (found, value, nominalUInt) ← circuitSourceExpression env nominalEnv stx
  unless nominalUInt == target.nominalUInt do
    throwErrorAt stx "nominal UInt values require an explicit cast and must match the target type"
  coerceExpression stx found target.type value

private partial def hasCircuitNominalFieldReference (env : List (String × Option NominalFieldType))
    (stx : Syntax) : _root_.Bool :=
  match stx with
  | .ident _ _ name _ => env.any fun (binding, nominal) =>
      binding == name.toString && nominal.isSome
  | .node _ _ children => children.toList.any (hasCircuitNominalFieldReference env)
  | _ => _root_.Bool.false

/-- Ordinary circuits keep nominal Field aliases in this source-only side channel.
The generated expression and ABI both remain Native. -/
private partial def circuitFieldExpression (env : Bindings) (nominalEnv : CircuitNominalEnv)
    (fieldEnv : List (String × Option NominalFieldType)) (stx : TSyntax `nlexpr) :
    CommandElabM (Ty × TSyntax `term × Option NominalFieldType) := do
  match stx with
  | `(nlexpr| cast($target:nltype, $value:nlexpr)) => do
    let target ← readCircuitSourceType target _root_.Bool.true
    let (source, value, _) ← circuitFieldExpression env nominalEnv fieldEnv value
    unless source == .native && target.type == .native do
      throwErrorAt stx "nominal Field casts require Native representation"
    pure (.native, ← `(Noctium.Expr.cast Noctium.Ty.native $value), target.nominalField)
  | `(nlexpr| let $id:ident := $value:nlexpr in $body:nlexpr) => do
    let (valueType, valueTerm, valueField) ← circuitFieldExpression env nominalEnv fieldEnv value
    let valueTypeTerm ← tyTerm valueType
    let valueRef ← `(Noctium.Expr.ref (ty := $valueTypeTerm) $(stringTerm id.getId.toString))
    let bodyEnv := (id.getId.toString, valueType, valueRef) :: env.filter
      (fun binding => binding.1 != id.getId.toString)
    let bodyFields := (id.getId.toString, valueField) :: fieldEnv.filter
      (fun binding => binding.1 != id.getId.toString)
    let (bodyType, bodyTerm, bodyField) ← circuitFieldExpression bodyEnv nominalEnv bodyFields body
    pure (bodyType, ← `(Noctium.Expr.letE $(stringTerm id.getId.toString) $valueTerm $bodyTerm), bodyField)
  | `(nlexpr| disclose($value)) => do
    let (type, term, nominalField) ← circuitFieldExpression env nominalEnv fieldEnv value
    pure (type, ← `(Noctium.Expr.disclose $(← spanTerm stx) $term), nominalField)
  | `(nlexpr| copyValue($value)) => do
    let (type, term, nominalField) ← circuitFieldExpression env nominalEnv fieldEnv value
    pure (type, ← `(Noctium.Expr.copyValue $term), nominalField)
  | `(nlexpr| $id:ident) => do
    let some (_, type, value) := env.find? (fun binding => binding.1 == id.getId.toString)
      | throwErrorAt id s!"unknown Noctium value '{id.getId}'"
    pure (type, value, (fieldEnv.lookup id.getId.toString).join)
  | `(nlexpr| add($left, $right)) | `(nlexpr| sub($left, $right)) | `(nlexpr| mul($left, $right)) => do
    let (leftType, leftTerm, leftField) ← circuitFieldExpression env nominalEnv fieldEnv left
    let (rightType, rightTerm, rightField) ← circuitFieldExpression env nominalEnv fieldEnv right
    if leftField.isSome || rightField.isSome then
      unless leftField == rightField && leftType == .native && rightType == .native do
        throwErrorAt stx "nominal Field arithmetic requires matching nominal operands"
      let operation ← match stx with
        | `(nlexpr| add($_, $_)) => pure ScalarPolicy.Binary.add
        | `(nlexpr| sub($_, $_)) => pure ScalarPolicy.Binary.sub
        | _ => pure ScalarPolicy.Binary.mul
      let type ← match ScalarPolicy.infer operation leftType.scalarKind rightType.scalarKind with
        | .ok .native => pure .native
        | .ok _ => throwErrorAt stx "nominal Field arithmetic requires Native operands"
        | .error message => throwErrorAt stx message
      let term ← match operation with
        | .add => `(Noctium.Expr.add $leftTerm $rightTerm)
        | .sub => `(Noctium.Expr.sub $leftTerm $rightTerm)
        | .mul => `(Noctium.Expr.mul $leftTerm $rightTerm)
      pure (type, term, leftField)
    else
      let (type, term, _) ← circuitSourceExpression env nominalEnv stx
      pure (type, term, none)
  | `(nlexpr| eq($left, $right)) => do
    let (leftType, leftTerm, leftField) ← circuitFieldExpression env nominalEnv fieldEnv left
    let (rightType, rightTerm, rightField) ← circuitFieldExpression env nominalEnv fieldEnv right
    if leftField.isSome || rightField.isSome then
      unless leftField == rightField && leftType == .native && rightType == .native do
        throwErrorAt stx "nominal Field equality requires matching nominal operands"
      pure (.bool, ← `(Noctium.Expr.eq $leftTerm $rightTerm), none)
    else
      let (type, term, _) ← circuitSourceExpression env nominalEnv stx
      pure (type, term, none)
  | `(nlexpr| select($condition, $yes, $no)) => do
    let (conditionType, conditionTerm, conditionField) ← circuitFieldExpression env nominalEnv fieldEnv condition
    unless conditionType == .bool && conditionField.isNone do throwErrorAt condition "select condition requires Bool"
    let (yesType, yesTerm, yesField) ← circuitFieldExpression env nominalEnv fieldEnv yes
    let (noType, noTerm, noField) ← circuitFieldExpression env nominalEnv fieldEnv no
    if yesField.isSome || noField.isSome then
      unless yesField == noField && yesType == .native && noType == .native do
        throwErrorAt stx "select branches require the same nominal Field type"
    if yesField.isSome || noField.isSome then
      let type ← commonType stx yesType noType
      let yesTerm ← coerceExpression stx yesType type yesTerm
      let noTerm ← coerceExpression stx noType type noTerm
      pure (type, ← `(Noctium.Expr.select $conditionTerm $yesTerm $noTerm), yesField)
    else
      let (type, term, _) ← circuitSourceExpression env nominalEnv stx
      pure (type, term, none)
  | _ =>
    if !hasCircuitNominalFieldReference fieldEnv stx.raw then
      let (type, value, _) ← circuitSourceExpression env nominalEnv stx
      return (type, value, none)
    throwErrorAt stx "nominal Field values require an explicit cast before this operation"

private def checkedCircuitFieldExpression (env : Bindings)
    (nominalEnv : CircuitNominalEnv) (fieldEnv : List (String × Option NominalFieldType))
    (stx : TSyntax `nlexpr)
    (target : CircuitSourceType) : CommandElabM (TSyntax `term) := do
  if target.nominalField.isNone && !hasCircuitNominalFieldReference fieldEnv stx.raw then
    return ← checkedExpression env stx target.type
  let (found, value, nominalField) ← circuitFieldExpression env nominalEnv fieldEnv stx
  unless nominalField == target.nominalField do
    throwErrorAt stx "nominal Field values require an explicit cast and must match the target type"
  coerceExpression stx found target.type value

private def bindContractRef (bindings : List (String × Name)) (name : String)
    (interface : Option Name) : List (String × Name) :=
  let rest := bindings.filter (·.1 != name)
  match interface with
  | none => rest
  | some interface => (name, interface) :: rest

private partial def checkedContractRef (bindings : List (String × Name))
    (expression : TSyntax `nlexpr) : CommandElabM (Option Name) := do
  if bindings.isEmpty then return none
  match expression with
  | `(nlexpr| $name:ident) => pure (bindings.lookup name.getId.toString)
  | `(nlexpr| disclose($value)) | `(nlexpr| copyValue($value)) =>
    checkedContractRef bindings value
  | `(nlexpr| select($condition, $yes, $no)) => do
    if (← checkedContractRef bindings condition).isSome then
      throwErrorAt condition "a contract reference cannot be a selection condition"
    let yesInterface ← checkedContractRef bindings yes
    let noInterface ← checkedContractRef bindings no
    unless yesInterface == noInterface do
      throwErrorAt expression "selected contract references must use the same interface"
    pure yesInterface
  | `(nlexpr| let $name:ident := $value:nlexpr in $body:nlexpr) => do
    let interface ← checkedContractRef bindings value
    checkedContractRef (bindContractRef bindings name.getId.toString interface) body
  | _ =>
    if (syntaxIdentifiers expression.raw).any (fun name => (bindings.lookup name).isSome) then
      throwErrorAt expression "unsupported operation on a typed contract reference"
    pure none

private def checkedSourceValue (env : Bindings) (nominalEnv : CircuitNominalEnv)
    (contractRefs : List (String × Name)) (value : TSyntax `nlexpr)
    (target : CircuitSourceType)
    (nominalFields : List (String × Option NominalFieldType) := []) : CommandElabM (TSyntax `term) := do
  unless (← checkedContractRef contractRefs value) == target.contractRef do
    throwErrorAt value "contract reference must match the declared interface"
  if target.nominalField.isSome || hasCircuitNominalFieldReference nominalFields value.raw then
    checkedCircuitFieldExpression env nominalEnv nominalFields value target
  else
    checkedCircuitSourceExpression env nominalEnv value target

private def checkedLedgerFieldValues (env : Bindings) (payload : TSyntax `nlleaves)
    (fields : List (String × Ty)) (fieldTypes : List (String × CircuitSourceType) := [])
    (nominals : CircuitNominalEnv := []) (contractRefs : List (String × Name) := [])
    (nominalFields : List (String × Option NominalFieldType) := []) :
    CommandElabM (List (Ty × TSyntax `term)) := do
  let `(nlleaves| fields($items:nlexpr,*)) := payload
    | throwErrorAt payload "ledger record payload expects fields(...)"
  let items := items.getElems.toList
  unless items.length == fields.length do
    throwErrorAt payload "ledger record field count does not match its checked layout"
  (items.zip fields).mapM fun (item, field, ty) => do
    let sourceType := (fieldTypes.lookup field).getD {type := ty}
    let value ← checkedSourceValue env nominals contractRefs item sourceType nominalFields
    pure (ty, value)

private partial def lowerTreePath (env : Bindings) (schema : LedgerValueType)
    (keys : List (TSyntax `nlexpr)) (nominals : CircuitNominalEnv := [])
    (keyNominals : List (Option NominalUIntType) := [])
    (keyFieldNominals : List (Option NominalFieldType) := [])
    (fieldBindings : List (String × Option NominalFieldType) := []) :
    CommandElabM (List (TSyntax `term) × LedgerValueType) := do
  match schema, keys with
  | value, [] => pure ([], value)
  | .scalar _, _ :: _ => throwError "nested map path continues through a scalar value"
  | .set _, _ :: _ => throwError "set members have no readable value"
  | .recordSet .., _ :: _ => throwError "record Set members have no readable value"
  | .recordMapKey .., _ :: _ => throwError "record Map values are scalar and have no nested path"
  | .recordMapComposite .., _ :: _ => throwError "record Map values are composite and have no nested path"
  | .shieldedCoinSet .., _ :: _ => throwError "qualified shielded coin Set members have no readable value"
  | .counter, _ :: _ => throwError "nested map path continues through a Counter value"
  | .composite .., _ :: _ => throwError "nested map path continues through a composite value"
  | .«list» .., _ :: _ => throwError "nested map path continues through a list value"
  | .merkleTree .., _ :: _ => throwError "nested map path continues through a MerkleTree value"
  | .map keyTy child, key :: rest => do
    let target : CircuitSourceType := {
      type := keyTy
      nominalUInt := keyNominals.head?.join
      nominalField := keyFieldNominals.head?.join
    }
    let lowered ← if target.nominalField.isSome ||
        hasCircuitNominalFieldReference fieldBindings key.raw then
      checkedCircuitFieldExpression env nominals fieldBindings key target
    else
      checkedCircuitSourceExpression env nominals key target
    let (tail, result) ← lowerTreePath env child rest nominals (keyNominals.drop 1)
      (keyFieldNominals.drop 1) fieldBindings
    pure ((← `(Noctium.PathKey.mk $(← tyTerm keyTy) $lowered)) :: tail, result)

private def pathKeysTerm (keys : List (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let list ← pathKeyListTerm keys
  `(($list : List Noctium.PathKey))

private def lowerCollectionEntryPath (env : Bindings) (schema : LedgerValueType)
    (keys : List (TSyntax `nlexpr)) (nominals : CircuitNominalEnv := [])
    (keyNominals : List (Option NominalUIntType) := [])
    (keyFieldNominals : List (Option NominalFieldType) := [])
    (fieldBindings : List (String × Option NominalFieldType) := []) :
    CommandElabM (TSyntax `term × LedgerValueType) := do
  let some finalKey := keys.getLast? | throwError "map or set operation requires a key"
  let index := keys.length - 1
  let (parents, parent) ← lowerTreePath env schema (keys.take index) nominals keyNominals
    keyFieldNominals fieldBindings
  let some keyTy := parent.collectionKey?
    | throwErrorAt finalKey "entry path must select a map or set"
  let target : CircuitSourceType := {
    type := keyTy
    nominalUInt := (keyNominals[index]?).join
    nominalField := (keyFieldNominals[index]?).join
  }
  let value ← if target.nominalField.isSome ||
      hasCircuitNominalFieldReference fieldBindings finalKey.raw then
    checkedCircuitFieldExpression env nominals fieldBindings finalKey target
  else
    checkedCircuitSourceExpression env nominals finalKey target
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
    CommandElabM (TSyntax `ident × TSyntax `term × Types.CompositeEnv ×
      Types.CompositeType × List (String × Ty)) := do
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
  pure (storage, ← pathKeysTerm keys, environment, type, fields)

private partial def bytes32ParentMaps (schema : LedgerValueType)
    (keys : List (TSyntax `nlexpr)) : _root_.Bool :=
  match keys with
  | [] => _root_.Bool.true
  | _ :: rest =>
    match schema with
    | .map (.bytes 32) value => bytes32ParentMaps value rest
    | _ => _root_.Bool.false

private def lowerQualifiedCoinSetPath (schema : List (String × StateKind))
    (env : Bindings) (path : TSyntax `nlpath) :
    CommandElabM (TSyntax `ident × TSyntax `term) := do
  let (storage, sourceKeys) ← sourcePathParts path
  unless sourceKeys.length ≤ 14 do
    throwErrorAt path "insertShieldedCoinSet supports at most fourteen Bytes32 Map parents"
  let treeSchema ← treeStateSchema schema storage
  unless bytes32ParentMaps treeSchema sourceKeys do
    throwErrorAt path
      "insertShieldedCoinSet requires a qualified coin Set under Bytes32-keyed Map parents"
  let (keys, selected) ← lowerTreePath env treeSchema sourceKeys
  let (environment, recordType) ← match selected with
    | .shieldedCoinSet environment recordType => pure (environment, recordType)
    | .recordSet environment recordType =>
      if sourceKeys.isEmpty then
        throwErrorAt path "insertShieldedCoinSet root path must select a qualified coin Set"
      pure (environment, recordType)
    | _ => throwErrorAt path "insertShieldedCoinSet path must select a qualified coin Set"
  match LedgerValueType.shieldedCoinRecordFields environment recordType with
  | .ok _ => pure ()
  | .error message => throwErrorAt path message
  pure (storage, ← pathKeysTerm keys)

private def lowerQualifiedCoinMapPath (schema : List (String × StateKind))
    (env : Bindings) (path : TSyntax `nlpath) :
    CommandElabM (TSyntax `ident × TSyntax `term) := do
  let (storage, sourceKeys) ← sourcePathParts path
  let treeSchema ← treeStateSchema schema storage
  let (keys, selected) ← lowerTreePath env treeSchema sourceKeys
  unless bytes32ParentMaps treeSchema sourceKeys do
    throwErrorAt path "insertShieldedCoinMap requires Bytes32-keyed parent Maps"
  let .map (.bytes 32) (.composite environment recordType) := selected
    | throwErrorAt path
        "insertShieldedCoinMap requires a Bytes32-keyed Map with the fixed qualified coin record value"
  match LedgerValueType.shieldedCoinRecordFields environment recordType with
  | .ok _ => pure ()
  | .error message => throwErrorAt path message
  pure (storage, ← pathKeysTerm keys)

private def lowerQualifiedCoinListPath (schema : List (String × StateKind))
    (env : Bindings) (path : TSyntax `nlpath) :
    CommandElabM (TSyntax `ident × TSyntax `term) := do
  let (storage, sourceKeys) ← sourcePathParts path
  let treeSchema ← treeStateSchema schema storage
  let supportedShape := sourceKeys.length ≤ 13 && bytes32ParentMaps treeSchema sourceKeys
  unless supportedShape do
    throwErrorAt path
      "pushFrontCoin supports a qualified coin List under at most 13 Bytes32-keyed Maps"
  let (keys, selected) ← lowerTreePath env treeSchema sourceKeys
  let .«list» environment recordType := selected
    | throwErrorAt path "pushFrontCoin path must select a qualified coin List"
  match LedgerValueType.shieldedCoinRecordFields environment recordType with
  | .ok _ => pure ()
  | .error message => throwErrorAt path message
  pure (storage, ← pathKeysTerm keys)

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

private unsafe def checkGeneratedContract (name : Name)
    (sourceRefs : List CallInterfaceSourceRefs := []) : CommandElabM Unit := do
  let value ← evalConstCheck Contract ``Contract name
  match value.validate Capabilities.source with
  | .error diagnostic => failDisclosure diagnostic
  | .ok _ =>
    match Disclosure.contract value with
    | .error diagnostic => failDisclosure diagnostic
    | .ok _ =>
      for entrypoint in value.entrypoints do
        let interfaceRefs := sourceRefs.find? fun refs =>
          refs.contract == name && refs.operation == entrypoint.name
        let resultViews ← entrypoint.returnViews.mapM fun view => do
          let checked ← match Types.checkedLayout {} view.environment view.type entrypoint.span with
            | .ok checked => pure checked
            | .error diagnostic => throwError diagnostic.message
          pure (view.name, view.fields.zip (Helpers.callViewLeafTypes checked.value))
        modifyEnv fun env => callInterfaceRegistry.addEntry env {
          contract := name, operation := entrypoint.name
          argumentFields := entrypoint.callArguments.map fun input => (input.name, input.ty)
          argumentContractRefs := (interfaceRefs.map (·.argumentContractRefs)).getD [] |>.filterMap
            fun (field, interface) =>
              if entrypoint.callArguments.any (·.name == field) then some (field, interface) else none
          argumentNominalUInts := (interfaceRefs.map (·.argumentNominalUInts)).getD [] |>.filterMap
            fun (field, nominalUInt) =>
              if entrypoint.callArguments.any (·.name == field) then some (field, nominalUInt) else none
          argumentNominalFields := (interfaceRefs.map (·.argumentNominalFields)).getD [] |>.filterMap
            fun (field, nominalField) =>
              if entrypoint.callArguments.any (·.name == field) then some (field, nominalField) else none
          argumentViews := entrypoint.callInputViews.map fun view => (view.name, view.fields)
          resultFields := entrypoint.returns.map fun result => (result.name, result.ty)
          resultContractRefs := (interfaceRefs.map (·.resultContractRefs)).getD []
          resultNominalUInts := (interfaceRefs.map (·.resultNominalUInts)).getD []
          resultNominalFields := (interfaceRefs.map (·.resultNominalFields)).getD []
          resultViews
        }

@[command_elab circuitCommand] def elabCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_circuit $name:ident where $stmts:nlcstmt* end) =>
    let mut env : Bindings := []
    let mut nominalEnv : CircuitNominalEnv := []
    let mut inputs : Array (TSyntax `term) := #[]
    let mut inputInfo := []
    let mut publicInputInfo := []
    let mut nominalUIntInputInfo := []
    let mut nominalFieldEnv : List (String × Option NominalFieldType) := []
    let mut nominalFieldInputInfo := []
    let mut contractRefEnv : List (String × Name) := []
    let mut contractRefInfo : List (String × Name) := []
    let mut outputs : Array (TSyntax `term) := #[]
    let mut outputInfo : List (String × Ty) := []
    let mut nominalUIntOutputInfo := []
    let mut nominalFieldOutputInfo := []
    let mut constraints : Array (TSyntax `term) := #[]
    for stmt in stmts do
      match stmt with
      | `(nlcstmt| public $id:ident : $ty:nltype)
      | `(nlcstmt| private $id:ident : $ty:nltype) =>
        ensureFresh env id
        let sourceType ← readCircuitSourceType ty _root_.Bool.true
        let t := sourceType.type
        let tt ← tyTerm t
        let isPublic := stmt.raw[0].getAtomVal == "public"
        let visibility ← if isPublic then `(Noctium.Visibility.public) else `(Noctium.Visibility.private)
        let span ← spanTerm stmt
        inputs := inputs.push (← `({ name := $(stringTerm id.getId.toString), ty := $tt, visibility := $visibility, span := $span : Noctium.Input }))
        env := (id.getId.toString, t, ← `(@Noctium.Expr.ref $tt $(stringTerm id.getId.toString))) :: env
        nominalEnv := bindCircuitNominal nominalEnv id.getId.toString sourceType.nominalUInt
        nominalFieldEnv := (id.getId.toString, sourceType.nominalField) ::
          nominalFieldEnv.filter (·.1 != id.getId.toString)
        contractRefEnv := bindContractRef contractRefEnv id.getId.toString sourceType.contractRef
        if let some interface := sourceType.contractRef then
          contractRefInfo := (id.getId.toString, interface) :: contractRefInfo
        inputInfo := inputInfo ++ [(id.getId.toString, t)]
        if let some nominalUInt := sourceType.nominalUInt then
          nominalUIntInputInfo := nominalUIntInputInfo ++ [(id.getId.toString, nominalUInt)]
        if let some nominalField := sourceType.nominalField then
          nominalFieldInputInfo := nominalFieldInputInfo ++ [(id.getId.toString, nominalField)]
        if isPublic then publicInputInfo := publicInputInfo ++ [(id.getId.toString, t)]
      | `(nlcstmt| let $id:ident : $ty:nltype := $value:nlexpr) =>
        ensureFresh env id
        let sourceType ← readCircuitSourceType ty _root_.Bool.true
        let t := sourceType.type
        let retain := (match t with | .uint _ => Bool.true | _ => Bool.false) || hasPartialScalar value
        let value ← if sourceType.nominalField.isSome ||
            hasCircuitNominalFieldReference nominalFieldEnv value.raw then
          checkedCircuitFieldExpression env nominalEnv nominalFieldEnv value sourceType
        else checkedSourceValue env nominalEnv contractRefEnv value sourceType
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
        nominalEnv := bindCircuitNominal nominalEnv id.getId.toString sourceType.nominalUInt
        nominalFieldEnv := (id.getId.toString, sourceType.nominalField) ::
          nominalFieldEnv.filter (·.1 != id.getId.toString)
        contractRefEnv := bindContractRef contractRefEnv id.getId.toString sourceType.contractRef
      | `(nlcstmt| assert $value:nlexpr) =>
        constraints := constraints.push (← if hasCircuitNominalFieldReference nominalFieldEnv value.raw then
          checkedCircuitFieldExpression env nominalEnv nominalFieldEnv value {type := .bool}
          else checkedSourceValue env nominalEnv contractRefEnv value {type := .bool})
      | `(nlcstmt| output $id:ident : $ty:nltype := $value:nlexpr) =>
        if outputInfo.any (fun p => p.1 == id.getId.toString) || inputInfo.any (fun p => p.1 == id.getId.toString) then
          throwErrorAt id "duplicate Noctium output '{id.getId}'"
        let sourceType ← readCircuitSourceType ty _root_.Bool.true
        let t := sourceType.type
        let tt ← tyTerm t
        let value ← if sourceType.nominalField.isSome ||
            hasCircuitNominalFieldReference nominalFieldEnv value.raw then
          checkedCircuitFieldExpression env nominalEnv nominalFieldEnv value sourceType
        else checkedSourceValue env nominalEnv contractRefEnv value sourceType
        let span ← spanTerm stmt
        outputs := outputs.push (← `({ name := $(stringTerm id.getId.toString), ty := $tt, value := $value, span := $span : Noctium.Output }))
        outputInfo := outputInfo ++ [(id.getId.toString, t)]
        if let some nominalUInt := sourceType.nominalUInt then
          nominalUIntOutputInfo := nominalUIntOutputInfo ++ [(id.getId.toString, nominalUInt)]
        if let some nominalField := sourceType.nominalField then
          nominalFieldOutputInfo := nominalFieldOutputInfo ++ [(id.getId.toString, nominalField)]
        if let some interface := sourceType.contractRef then
          contractRefInfo := (id.getId.toString, interface) :: contractRefInfo
      | _ => throwErrorAt stmt "unsupported Noctium circuit statement"
    let span ← spanTerm stx
    let fullName := (← getCurrNamespace) ++ name.getId
    elabCommand (← `(def $name : Noctium.Circuit := { name := $(stringTerm fullName.toString), inputs := [$inputs,*], outputs := [$outputs,*], constraints := [$constraints,*], span := $span }))
    unsafe checkGeneratedCircuit fullName
    modifyEnv fun e => circuitRegistry.addEntry e {
      declName := fullName
      inputs := inputInfo
      publicInputs := publicInputInfo
      outputs := outputInfo
      nominalUIntInputs := nominalUIntInputInfo
      nominalUIntOutputs := nominalUIntOutputInfo
      nominalFieldInputs := nominalFieldInputInfo
      nominalFieldOutputs := nominalFieldOutputInfo
      contractRefBindings := contractRefInfo
    }
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

private structure OptionalRecordHead where
  presentName : String
  recordName : String
  environment : Types.CompositeEnv
  type : Types.CompositeType
  fields : List (String × Ty)
  fieldPaths : List (List String × String × Ty) := []
  nominalUIntFields : List (String × NominalUIntType) := []

private structure CollectionNominals where
  /-- Nominal identities for each Map key, followed by the member key for a leaf Set. -/
  pathKeys : List (Option NominalUIntType) := []
  /-- Nominal Field identities for the same keys, currently used by root scalar Sets. -/
  pathFieldKeys : List (Option NominalFieldType) := []
  scalarValue : Option NominalUIntType := none

private def CollectionNominals.isEmpty (nominals : CollectionNominals) : _root_.Bool :=
  nominals.scalarValue.isNone && nominals.pathKeys.all Option.isNone &&
    nominals.pathFieldKeys.all Option.isNone

private def directNominalUIntMaps (schema : List (String × StateKind))
    (nominals : List (String × CollectionNominals)) : List (String × NominalUIntMap) :=
  schema.filterMap fun (name, kind) => do
    let .map .. := kind | none
    let some metadata := nominals.lookup name | none
    let [key] := metadata.pathKeys | none
    if metadata.isEmpty then none
    else some (name, {key := key, value := metadata.scalarValue})

private structure EntryEffects where
  env : Bindings
  nominalUIntBindings : CircuitNominalEnv := []
  nominalFieldBindings : List (String × Option NominalFieldType) := []
  nominalUIntCells : List (String × NominalUIntType) := []
  nominalFieldCells : List (String × NominalFieldType) := []
  nominalUIntLists : List (String × NominalUIntType) := []
  nominalCollections : List (String × CollectionNominals) := []
  contractRefBindings : List (String × Name) := []
  contractRefState : List (String × Name) := []
  recordFieldTypes : List (String × List (String × CircuitSourceType)) := []
  recordKeyFieldTypes : List (String × List (String × CircuitSourceType)) := []
  nominalBytes32Bindings : List (String × NominalBytes32) := []
  merkleLeafTypes : List (String × MerkleLeafType) := []
  optionalRecordHeads : List OptionalRecordHead := []
  terms : Array (TSyntax `term) := #[]
  spans : Array (TSyntax `term) := #[]
  guards : Array (TSyntax `term) := #[]
  returns : Array (TSyntax `term) := #[]
  returnContractRefs : List (String × Name) := []
  returnNominalUInts : List (String × NominalUIntType) := []
  returnNominalFields : List (String × NominalFieldType) := []
  returnViews : Array (TSyntax `term) := #[]
  nextLocal : Nat := 0
  usedLocalNames : List String := []

private def elaborateLedgerFieldValues (state : EntryEffects) (payload : TSyntax `nlleaves)
    (fields : List (String × Ty)) (fieldTypes : List (String × CircuitSourceType) := []) :
    CommandElabM (TSyntax `term) := do
  let checked ← checkedLedgerFieldValues state.env payload fields fieldTypes
    state.nominalUIntBindings state.contractRefBindings state.nominalFieldBindings
  let values ← checked.mapM fun (ty, value) => do
    `(Noctium.LedgerFieldExpr.mk $(← tyTerm ty) $value)
  let values := values.toArray
  `(([$values,*] : List Noctium.LedgerFieldExpr))

private def elaborateConstructorRecordListPush (schema : List (String × StateKind))
    (bindings : EntryEffects) (initializer : TSyntax `nlconstructorinit)
    (stateName : TSyntax `ident) (payload : TSyntax `nlleaves) :
    CommandElabM (TSyntax `term) := do
  let destination := stateName.getId.toString
  let guard ← match initializer with
    | `(nlconstructorinit| when $condition:nlexpr pushFront $_:ident := $_:nlleaves) => do
      let conditionExpression ← checkedCircuitSourceExpression bindings.env
        bindings.nominalUIntBindings condition {type := .bool}
      `(some $conditionExpression)
    | `(nlconstructorinit| pushFront $_:ident := $_:nlleaves) => `(none)
    | _ => throwErrorAt initializer "invalid constructor record List pushFront"
  let some (.tree (.«list» environment (.structure recordType))) := schema.lookup destination
    | throwErrorAt stateName "constructor record pushFront requires a root record List"
  let fields ← match LedgerValueType.listElementFields environment (.structure recordType) with
    | .ok fields => pure fields
    | .error message => throwErrorAt stateName message
  let values ← elaborateLedgerFieldValues bindings payload fields
    ((bindings.recordFieldTypes.lookup destination).getD [])
  `(Noctium.ConstructorAction.pushRecordList $(stringTerm destination) $values $guard)

private def elaborateRecordMapKeyFields (state : EntryEffects) (storage : TSyntax `ident)
    (payload : TSyntax `nlleaves) (fields : List (String × Ty)) : CommandElabM (TSyntax `term) :=
  elaborateLedgerFieldValues state payload fields
    ((state.recordKeyFieldTypes.lookup storage.getId.toString).getD [])

private def EntryEffects.collectionNominals (state : EntryEffects) (storage : TSyntax `ident) : CollectionNominals :=
  (state.nominalCollections.lookup storage.getId.toString).getD {}

private def lowerMapPath (state : EntryEffects) (storage : TSyntax `ident) (schema : LedgerValueType)
    (keys : List (TSyntax `nlexpr)) : CommandElabM (List (TSyntax `term) × LedgerValueType) :=
  lowerTreePath state.env schema keys state.nominalUIntBindings
    (state.collectionNominals storage).pathKeys (state.collectionNominals storage).pathFieldKeys
    state.nominalFieldBindings

private def lowerMapEntryPath (state : EntryEffects) (storage : TSyntax `ident) (schema : LedgerValueType)
    (keys : List (TSyntax `nlexpr)) : CommandElabM (TSyntax `term × LedgerValueType) :=
  lowerCollectionEntryPath state.env schema keys state.nominalUIntBindings
    (state.collectionNominals storage).pathKeys (state.collectionNominals storage).pathFieldKeys
    state.nominalFieldBindings

private def checkedRootMapKey (state : EntryEffects) (storage : TSyntax `ident)
    (key : TSyntax `nlexpr) (ty : Ty) : CommandElabM (TSyntax `term) :=
  checkedSourceValue state.env state.nominalUIntBindings state.contractRefBindings key
    {type := ty, nominalUInt := (state.collectionNominals storage).pathKeys.head?.join}

private def checkedMapValue (state : EntryEffects) (storage : TSyntax `ident)
    (value : TSyntax `nlexpr) (ty : Ty) : CommandElabM (TSyntax `term) :=
  checkedSourceValue state.env state.nominalUIntBindings state.contractRefBindings value
    {type := ty, nominalUInt := (state.collectionNominals storage).scalarValue}

private partial def nominalBytes32OfExpression (state : EntryEffects)
    (expression : TSyntax `nlexpr) : Option NominalBytes32 :=
  match expression with
  | `(nlexpr| disclose($value)) => nominalBytes32OfExpression state value
  | `(nlexpr| shieldedBurnKey()) => some .zswapCoinPublicKey
  | `(nlexpr| $name:ident) => state.nominalBytes32Bindings.lookup name.getId.toString
  | _ => none

private def checkNominalBytes32Argument (state : EntryEffects)
    (expression : TSyntax `nlexpr) (expected : NominalBytes32) (operation : String) :
    CommandElabM Unit := do
  if let some actual := nominalBytes32OfExpression state expression then
    unless actual == expected do
      throwErrorAt expression
        s!"{operation} expects {expected.displayName}, got {actual.displayName}"

private def requireNominalBytes32Argument (state : EntryEffects)
    (expression : TSyntax `nlexpr) (expected : NominalBytes32) (branch : String) :
    CommandElabM Unit := do
  let some actual := nominalBytes32OfExpression state expression
    | throwErrorAt expression
        s!"PublicAddress.{branch} requires a nominal {expected.displayName} value"
  unless actual == expected do
    throwErrorAt expression
      s!"PublicAddress.{branch} expects {expected.displayName}, got {actual.displayName}"

private partial def boolLiteralValue? (expression : TSyntax `nlexpr) : Option _root_.Bool :=
  match expression with
  | `(nlexpr| true) => some _root_.Bool.true
  | `(nlexpr| false) => some _root_.Bool.false
  | `(nlexpr| disclose($value)) => boolLiteralValue? value
  | _ => none

private def checkUnshieldedRecipientTag (state : EntryEffects)
    (isContract recipient : TSyntax `nlexpr) : CommandElabM Unit := do
  match nominalBytes32OfExpression state recipient with
  | none => pure ()
  | some .zswapCoinPublicKey =>
    throwErrorAt recipient
      "claimUnshieldedCoinSpend cannot use a ZswapCoinPublicKey recipient"
  | some nominal =>
    let expectedContract := nominal == .contractAddress
    let some actualContract := boolLiteralValue? isContract
      | throwErrorAt isContract
          "claimUnshieldedCoinSpend needs a literal tag for a nominal recipient; use claimUnshieldedCoinSpendTo"
    unless actualContract == expectedContract do
      let expectedBranch := if expectedContract then "true for ContractAddress" else "false for UserAddress"
      throwErrorAt isContract
        s!"claimUnshieldedCoinSpend tag must be {expectedBranch}"

private def addNominalBytes32Binding (state : EntryEffects) (name : String)
    (type : NominalBytes32) : EntryEffects :=
  {state with nominalBytes32Bindings :=
    (name, type) :: state.nominalBytes32Bindings.filter (·.1 != name)}

private def explicitEffectGuard (effect : TSyntax `nleffect) : Option (TSyntax `nlexpr) :=
  match effect with
  | `(nleffect| when $condition:nlexpr $update:nlupdate) => some condition
  | `(nleffect| when $condition:nlexpr write $_state:ident := $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr insert $_state:ident [ $_key:nlexpr ] := $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr insert $_state:ident [ $_payload:nlleaves ] := $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr insert $_state:ident [ $_owner:nlexpr ] [ $_payload:nlleaves ] := $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr insert $_state:ident [ $_owner:nlexpr ] [ $_payload:nlleaves ] := $_valuePayload:nlleaves) => some condition
  | `(nleffect| when $condition:nlexpr insert $_state:ident [ $_payload:nlleaves ] := $_valuePayload:nlleaves) => some condition
  | `(nleffect| when $condition:nlexpr require $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr read $_path:nlpath as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr read $_state:ident [$_payload:nlleaves] as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr read $_state:ident [$_owner:nlexpr] [$_payload:nlleaves] as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr readSelf as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr mintUnshieldedTo($_:nlexpr, $_:nlexpr, $_:nlexpr, $_:nlexpr) as $_:ident) =>
    some condition
  | `(nleffect| when $condition:nlexpr member $_path:nlpath as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr member $_state:ident [$_owner:nlexpr] [$_payload:nlleaves] as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr member $_state:ident [$_payload:nlleaves] as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr insert $_state:ident [$_owner:nlexpr] [$_payload:nlleaves]) => some condition
  | `(nleffect| when $condition:nlexpr insert $_state:ident [$_payload:nlleaves]) => some condition
  | `(nleffect| when $condition:nlexpr remove $_state:ident [$_owner:nlexpr] [$_payload:nlleaves]) => some condition
  | `(nleffect| when $condition:nlexpr remove $_state:ident [$_payload:nlleaves]) => some condition
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
  | `(nleffect| when $condition:nlexpr insertDefault $_state:ident [$_owner:nlexpr] [$_payload:nlleaves]) => some condition
  | `(nleffect| when $condition:nlexpr insertDefault $_state:ident [$_payload:nlleaves]) => some condition
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
  | `(nleffect| when $condition:nlexpr blockTimeAfter($_deadline:nlexpr) as $_dest:ident)
  | `(nleffect| when $condition:nlexpr blockTimeAtOrAfter($_deadline:nlexpr) as $_dest:ident)
  | `(nleffect| when $condition:nlexpr blockTimeAtOrBefore($_deadline:nlexpr) as $_dest:ident) =>
    some condition
  | `(nleffect| when $condition:nlexpr counterLessThan $_path:nlpath against $_threshold:nlexpr as $_destination:ident) =>
    some condition
  | `(nleffect| when $condition:nlexpr readCaller as ($_present:ident, $_isContract:ident, $_contract:ident, $_user:ident)) => some condition
  | _ => none

private def effectGuardTerm (state : EntryEffects) (parent : Option (TSyntax `term))
    (effect : TSyntax `nleffect) : CommandElabM (TSyntax `term) := do
  let explicit ← match explicitEffectGuard effect with
    | none => pure none
    | some condition => pure (some (← checkedSourceValue state.env state.nominalUIntBindings
        state.contractRefBindings condition {type := .bool} state.nominalFieldBindings))
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
    (depth : Nat) (fields : List (String × Ty))
    (fieldTypes : List (String × CircuitSourceType) := []) :
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
    let sourceType := fieldTypes.lookup field
    let contractRefBindings := bindContractRef updated.contractRefBindings sourceName
      (sourceType.bind (·.contractRef))
    let nominalUIntBindings := bindCircuitNominal updated.nominalUIntBindings sourceName
      (sourceType.bind (·.nominalUInt))
    let nominalFieldBindings := (sourceName, sourceType.bind (·.nominalField)) ::
      updated.nominalFieldBindings.filter (·.1 != sourceName)
    updated := {updated with contractRefBindings, nominalUIntBindings, nominalFieldBindings}
    destinations := destinations.push (← `(($(stringTerm internalName), $(← tyTerm ty))))
  pure (updated, ← `(([$destinations,*] : List (String × Noctium.Ty))))

private def readShieldedCoinFields (baseName : String)
    : CommandElabM (TSyntax `nlexpr × TSyntax `nlexpr × TSyntax `nlexpr) := do
  let nonceName := mkIdent (Name.mkSimple (baseName ++ "_nonce"))
  let colorName := mkIdent (Name.mkSimple (baseName ++ "_color"))
  let amountName := mkIdent (Name.mkSimple (baseName ++ "_value"))
  let nonceSyntax ← `(nlexpr| $nonceName:ident)
  let colorSyntax ← `(nlexpr| $colorName:ident)
  let amountSyntax ← `(nlexpr| $amountName:ident)
  pure (nonceSyntax, colorSyntax, amountSyntax)

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
    (destination : TSyntax `ident) (before : _root_.Bool) (deadline : TSyntax `nlexpr)
    (complementGuard : Option (TSyntax `term) := none) :
    CommandElabM EntryEffects := do
  let value ← checkedExpression state.env deadline (.uint (2 ^ 64 - 1))
  let (name, updated) ← freshReadName depth state destination
  let direction ← if before then `(Bool.true) else `(Bool.false)
  let term ← `(Noctium.Effect.blockTimeCompare $(stringTerm name) $direction $value)
  let updated := {updated with terms := updated.terms.push term}
  let sourceName := destination.getId.toString
  let some guard := complementGuard | bindReadName updated sourceName name .bool
  let complemented ← `(Noctium.Expr.select (Noctium.Expr.ref $(stringTerm name))
    (Noctium.Expr.bool Bool.false) (Noctium.Expr.bool Bool.true))
  -- The inactive strict read produces false, so complement only an active observation.
  let result ← `(match ($guard : Option (Noctium.Expr Noctium.Ty.bool)) with
    | none => $complemented
    | some active => Noctium.Expr.select active $complemented (Noctium.Expr.bool Bool.false))
  pure {updated with env := (sourceName, .bool, result) :: updated.env}

private def elaborateUnshieldedMintTo (state : EntryEffects)
    (domain amount isContract recipient : TSyntax `nlexpr) (destination : TSyntax `ident)
    (guard span : TSyntax `term) : CommandElabM EntryEffects := do
  ensureFresh state.env destination
  checkUnshieldedRecipientTag state isContract recipient
  let destinationName := destination.getId.toString
  let (selfName, nextLocal) := chooseBranchLocalName state.env
    (destinationName :: state.usedLocalNames) state.nextLocal "noctium_mint_self_"
  let selfIdent := mkIdent (Name.mkSimple selfName)
  let selfRef ← `(Noctium.Expr.ref (ty := Noctium.Ty.bytes 32) $(stringTerm selfName))
  let addressEnv := (selfName, Ty.bytes 32, selfRef) :: state.env
  let colorSource ← `(nlexpr| tokenType($domain, $selfIdent:ident))
  let selfSource ← `(nlexpr| eq($recipient, $selfIdent:ident))
  let color ← checkedExpression addressEnv colorSource (.bytes 32)
  let isSelf ← checkedExpression addressEnv selfSource .bool
  let domain ← checkedExpression state.env domain (.bytes 32)
  let mintAmount ← checkedExpression state.env amount (.uint (2 ^ 64 - 1))
  let wideAmount ← `(Noctium.Expr.cast (Noctium.Ty.uint $(natTerm balanceMaximum)) $mintAmount)
  let isContract ← checkedExpression state.env isContract .bool
  let recipient ← checkedExpression state.env recipient (.bytes 32)
  let mint ← `(Noctium.Effect.mintUnshielded $domain $mintAmount)
  let addressRead ← `(Noctium.Effect.readContractAddress $(stringTerm selfName))
  let claim ← `(Noctium.Effect.claimUnshieldedCoinSpend
    $color $wideAmount (Noctium.Expr.bool Bool.true) $isContract $recipient)
  let credit ← `(Noctium.Effect.incUnshieldedInputs $color $wideAmount (Noctium.Expr.bool Bool.true))
  let creditSelf ← `(Noctium.Backend.Impact.activityGuardWithin
    $isContract $isSelf)
  let (creditGuard, result) ← match guard with
    | `(term| none) => pure (← `(some $creditSelf), color)
    | `(term| some $active) => do
      let creditGuard ← `(some (Noctium.Backend.Impact.activityGuardWithin $active $creditSelf))
      let result ← `(Noctium.Expr.select $active (Noctium.GuardedExpression.totalize $active $color)
        (Noctium.GuardedExpression.zeroValue (Noctium.Ty.bytes 32)))
      pure (creditGuard, result)
    | _ => throwError "invalid unshielded mint activity guard"
  pure {state with
    terms := state.terms.push mint |>.push addressRead |>.push claim |>.push credit
    spans := state.spans.push span |>.push span |>.push span
    guards := state.guards.push guard |>.push guard |>.push creditGuard
    env := (destinationName, .bytes 32, result) :: state.env
    nextLocal
    usedLocalNames := selfName :: state.usedLocalNames}

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

private def bindMapRead (state : EntryEffects) (storage destination : TSyntax `ident)
    (readName : String) (valueTy : Ty) : CommandElabM EntryEffects := do
  let updated ← bindReadName state destination.getId.toString readName valueTy
  let bindings := bindCircuitNominal updated.nominalUIntBindings destination.getId.toString
    (state.collectionNominals storage).scalarValue
  pure {updated with nominalUIntBindings := bindings}

private def elaborateTreeRead (storage destination : TSyntax `ident)
    (keys : List (TSyntax `nlexpr))
    (treeSchema : LedgerValueType) (depth : Nat) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (path, result) ← lowerMapPath state storage treeSchema keys
  let keys ← pathKeysTerm path
  match result with
  | .scalar valueTy => do
    let (readName, updated) ← freshReadName depth state destination
    let term ← `(Noctium.Effect.readPath $(stringTerm storage.getId.toString)
      $(stringTerm readName) $keys $(← tyTerm valueTy))
    let updated := {updated with terms := updated.terms.push term}
    bindMapRead updated storage destination readName valueTy
  | .composite environment (.structure typeId) => do
    let fields ← if path.isEmpty then
      match LedgerValueType.cellRecordFields environment (.structure typeId) with
      | .ok fields => pure fields
      | .error message => throwErrorAt destination message
    else if path.length == 1 then
      match LedgerValueType.rootMapRecordFields environment (.structure typeId) with
      | .ok fields => pure fields
      | .error message => throwErrorAt destination message
    else match LedgerValueType.ledgerRecordFields environment (.structure typeId) with
      | .ok fields => pure fields
      | .error message => throwErrorAt destination message
    let (readName, updated) ← freshReadName depth state destination
    let fieldTypes := (state.recordFieldTypes.lookup storage.getId.toString).getD []
    let (updated, destinations) ← bindLedgerRecordFields updated destination depth fields fieldTypes
    let typeTerm ← `(Noctium.Types.CompositeType.structure $(stringTerm typeId))
    let term ← `(Noctium.Effect.readCompositePath
      $(stringTerm storage.getId.toString) $(stringTerm readName) $keys $typeTerm $destinations)
    pure {updated with terms := updated.terms.push term}
  | .composite .. => throwErrorAt destination "native composite ledger reads require a named structure"
  | .map .. => throwErrorAt destination "nested map read must select a scalar or composite value"
  | .set _ => throwErrorAt destination "Set members do not have readable values"
  | .recordSet .. => throwErrorAt destination "Set members do not have readable values"
  | .recordMapKey .. => throwErrorAt destination "record Map values require a typed record key read"
  | .recordMapComposite .. => throwErrorAt destination "record Map values require a typed record key read"
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
  let (storage, keys, _, _, _) ← lowerListPath schema state.env path
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
  let (storage, keys, _, type, fields) ← lowerListPath schema state.env path
  let (readName, updated) ← freshReadName depth state destination
  let (updated, destinations) ← match type with
    | .scalar ty => do
      let updated ← bindReadName updated destination.getId.toString readName ty
      let nominalUInt := state.nominalUIntLists.lookup storage.getId.toString
      let nominalUIntBindings := bindCircuitNominal updated.nominalUIntBindings
        destination.getId.toString nominalUInt
      let interface := state.contractRefState.lookup storage.getId.toString
      let contractRefBindings := bindContractRef updated.contractRefBindings destination.getId.toString interface
      let updated := {updated with nominalUIntBindings, contractRefBindings}
      pure (updated, ← `([($(stringTerm readName), $(← tyTerm ty))]))
    | _ =>
      let fieldTypes := (state.recordFieldTypes.lookup storage.getId.toString).getD []
      bindLedgerRecordFields updated destination depth fields fieldTypes
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
  let (storage, keys, environment, type, fields) ← lowerListPath schema state.env path
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
  let headed ← elaborateListHead schema path record depth updated
  match type with
  | .structure _ =>
    let fieldTypes := (state.recordFieldTypes.lookup storage.getId.toString).getD []
    let nominalUIntFields := fieldTypes.filterMap fun (field, sourceType) =>
      sourceType.nominalUInt.map fun nominalUInt => (field, nominalUInt)
    pure {headed with optionalRecordHeads := {
      presentName
      recordName := record.getId.toString
      environment
      type
      fields
      fieldPaths := (LedgerValueType.listElementFieldPaths environment type).toOption.getD []
      nominalUIntFields
    } :: headed.optionalRecordHeads}
  | _ => pure headed

private def elaborateListPushFront (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (payload : TSyntax `nlledgervalue)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, _, type, fields) ← lowerListPath schema state.env path
  let valuesTerm ← match payload with
    | `(nlledgervalue| $item:nlexpr) => do
      let .scalar ty := type
        | throwErrorAt payload "record List pushFront expects fields(...)"
      let contractRef := state.contractRefState.lookup storage.getId.toString
      let nominalUInt := state.nominalUIntLists.lookup storage.getId.toString
      let value ← checkedSourceValue state.env state.nominalUIntBindings state.contractRefBindings item
        {type := ty, nominalUInt, contractRef}
      `([Noctium.LedgerFieldExpr.mk $(← tyTerm ty) $value])
    | `(nlledgervalue| $items:nlleaves) => do
      if let .scalar _ := type then
        throwErrorAt payload "scalar List pushFront expects one value expression"
      let fieldTypes := (state.recordFieldTypes.lookup storage.getId.toString).getD []
      elaborateLedgerFieldValues state items fields fieldTypes
    | _ => throwErrorAt payload "expected a List element"
  let typeTerm ← listElementTypeTerm path type
  let term ← `(Noctium.Effect.listPushFront
    $(stringTerm storage.getId.toString) $keys $typeTerm $valuesTerm)
  pure {state with terms := state.terms.push term}

private def elaborateListPopFront (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, keys, _, _, _) ← lowerListPath schema state.env path
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
  | .map .. | .set _ | .recordSet .. | .recordMapKey .. | .recordMapComposite .. =>
    `(Noctium.Effect.emptyMapPath $name $keys)
  | .shieldedCoinSet .. => do
    unless 1 ≤ keyCount && keyCount ≤ 14 do
      throwErrorAt path "qualified shielded coin Set reset supports one to fourteen Map keys"
    `(Noctium.Effect.emptyMapPath $name $keys)
  | .merkleTree depth historic =>
    unless 1 ≤ keyCount && keyCount ≤ 12 do
      throwErrorAt path "nested MerkleTree paths require one to twelve map keys"
    unless 2 ≤ depth && depth ≤ 32 do
      throwErrorAt path "MerkleTree depth must be between 2 and 32"
    let historyTerm ← if historic then `(Bool.true) else `(Bool.false)
    let emptyHistory ← if historic && mapDefault then `(Bool.true) else `(Bool.false)
    `(Noctium.Effect.merkleTreeResetAt $name $keys $(natTerm depth) $historyTerm $emptyHistory)
  | _ => throwErrorAt path "reset requires a Counter, List, Map, Set or MerkleTree value"

private def zeroLedgerFieldValues (fields : List (String × Ty)) :
    CommandElabM (Array (TSyntax `term)) := do
  fields.toArray.mapM fun (_, ty) => do
    let type ← tyTerm ty
    `(Noctium.LedgerFieldExpr.mk $type (Noctium.GuardedExpression.zeroValue $type))

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
  if let some (.tree (.composite environment type)) := schema.lookup storage.getId.toString then
    unless sourceKeys.isEmpty do throwErrorAt path "cell reset does not accept a key path"
    let fields ← match LedgerValueType.cellRecordFields environment type with
      | .ok fields => pure fields
      | .error message => throwErrorAt path message
    let values ← zeroLedgerFieldValues fields
    let typeTerm ← match type with
      | .structure id => `(Noctium.Types.CompositeType.structure $(stringTerm id))
      | _ => throwErrorAt path "reset requires a named ledger record"
    let keys ← pathKeysTerm []
    let term ← `(Noctium.Effect.writeCompositePath
      $(stringTerm storage.getId.toString) $keys $typeTerm [$values,*])
    return {state with terms := state.terms.push term}
  if let some (.cell ty) := schema.lookup storage.getId.toString then
    unless sourceKeys.isEmpty do throwErrorAt path "cell reset does not accept a key path"
    let type ← tyTerm ty
    let value ← `(Noctium.GuardedExpression.zeroValue $type)
    let term ← `(Noctium.Effect.writeCell $(stringTerm storage.getId.toString) $type $value)
    return {state with terms := state.terms.push term}
  let treeSchema ← statePathSchema schema storage
  let (keys, value) ← lowerMapPath state storage treeSchema sourceKeys
  let keys ← pathKeysTerm keys
  let term ← collectionResetTerm path storage keys sourceKeys.length value
  pure {state with terms := state.terms.push term}

private def elaborateMapDefault (schema : List (String × StateKind)) (path : TSyntax `nlpath)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, sourceKeys) ← sourcePathParts path
  let name := stringTerm storage.getId.toString
  let term ← if let some (.map keyTy valueTy) := schema.lookup storage.getId.toString then do
    let [key] := sourceKeys | throwErrorAt path "insertDefault on a direct Map requires one key"
    let key ← checkedRootMapKey state storage key keyTy
    let type ← tyTerm valueTy
    `(Noctium.Effect.writeMap $name $(← tyTerm keyTy) $type $key
      (Noctium.GuardedExpression.zeroValue $type))
  else do
    let stateSchema ← statePathSchema schema storage
    let (keys, parent) ← lowerMapEntryPath state storage stateSchema sourceKeys
    let .map _ value := parent | throwErrorAt path "insertDefault requires a Map entry"
    match value with
    | .scalar ty => do
      let type ← tyTerm ty
      `(Noctium.Effect.writePath $name $keys $type (Noctium.GuardedExpression.zeroValue $type))
    | .composite environment (.structure id) => do
      let fields ← match (if sourceKeys.length == 1 then
          LedgerValueType.rootMapRecordFields environment (.structure id)
        else LedgerValueType.ledgerRecordFields environment (.structure id)) with
        | .ok fields => pure fields
        | .error message => throwErrorAt path message
      let values ← zeroLedgerFieldValues fields
      `(Noctium.Effect.writeCompositePath $name $keys
        (Noctium.Types.CompositeType.structure $(stringTerm id)) [$values,*])
    | .composite .. => throwErrorAt path "insertDefault requires a named ledger record"
    | value => collectionResetTerm path storage keys sourceKeys.length value Bool.true
  pure {state with terms := state.terms.push term}

private def elaborateRecordMapDefault (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentPath : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (state : EntryEffects) :
    CommandElabM EntryEffects := do
  let name := stringTerm storage.getId.toString
  let treeSchema ← treeStateSchema schema storage
  let (parentKeys, valueSchema) ← lowerTreePath state.env treeSchema parentPath
  let parentKeys ← pathKeysTerm parentKeys
  let term ← match valueSchema with
    | .recordMapKey keyEnvironment keyType valueTy => do
      let keyFields ← match LedgerValueType.recordMapKeyFields keyEnvironment keyType with
        | .ok fields => pure fields
        | .error message => throwErrorAt storage message
      let keyValues ← elaborateRecordMapKeyFields state storage payload keyFields
      let type ← tyTerm valueTy
      let value ← `(Noctium.GuardedExpression.zeroValue $type)
      `(Noctium.Effect.writeRecordMap $name $keyValues $type $value $parentKeys)
    | .recordMapComposite keyEnvironment keyType valueEnvironment valueType => do
      let keyFields ← match LedgerValueType.ledgerRecordWriteFields keyEnvironment keyType with
        | .ok fields => pure fields
        | .error message => throwErrorAt storage message
      let keyValues ← elaborateRecordMapKeyFields state storage payload keyFields
      let valueFields ← match (if parentPath.isEmpty then
          LedgerValueType.rootMapRecordWriteFields valueEnvironment valueType
        else LedgerValueType.ledgerRecordWriteFields valueEnvironment valueType) with
        | .ok fields => pure fields
        | .error message => throwErrorAt storage message
      let values ← zeroLedgerFieldValues valueFields
      let .structure valueTypeId := valueType
        | throwErrorAt storage "record Map values require a named structure"
      let type ← `(Noctium.Types.CompositeType.structure $(stringTerm valueTypeId))
      `(Noctium.Effect.writeRecordMapComposite $name $type $keyValues [$values,*]
        $parentKeys)
    | _ =>
      if parentPath.isEmpty then
        throwErrorAt storage "insertDefault with fields(...) requires a root record-key Map"
      else
        throwErrorAt storage
          "insertDefault with fields(...) requires a nested scalar- or record-valued record-key Map"
  pure {state with terms := state.terms.push term}

private def elaborateCompositePathWrite (schema : List (String × StateKind))
    (storage : TSyntax `ident) (keys : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (state : EntryEffects) : CommandElabM EntryEffects := do
  let treeSchema ← treeStateSchema schema storage
  let (path, result) ← lowerTreePath state.env treeSchema keys
  let (.composite environment type) := result
    | throwErrorAt payload "composite write must select a composite record"
  let fields ← match (if path.isEmpty then
      LedgerValueType.cellWriteRecordFields environment type
    else if path.length == 1 then LedgerValueType.rootMapRecordWriteFields environment type
    else LedgerValueType.ledgerRecordWriteFields environment type) with
    | .ok fields => pure fields
    | .error message => throwErrorAt payload message
  let fieldTypes := (state.recordFieldTypes.lookup storage.getId.toString).getD []
  let valueList ← elaborateLedgerFieldValues state payload fields fieldTypes
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
  let (keys, _) ← lowerMapEntryPath state storage stateSchema sourceKeys
  let term ← `(Noctium.Effect.removePath $(stringTerm storage.getId.toString) $keys)
  pure {state with terms := state.terms.push term}

private def elaborateSetInsert (schema : List (String × StateKind))
    (path : TSyntax `nlpath) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (storage, sourceKeys) ← sourcePathParts path
  let stateSchema ← statePathSchema schema storage
  let (keys, parent) ← lowerMapEntryPath state storage stateSchema sourceKeys
  let .set _ := parent | throwErrorAt path "insert without a value requires a Set"
  let term ← `(Noctium.Effect.setInsert $(stringTerm storage.getId.toString) $keys)
  pure {state with terms := state.terms.push term}

private def recordSetKeyValuesAt (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (state : EntryEffects) :
    CommandElabM (TSyntax `term × List (String × Ty) × TSyntax `term) := do
  let treeSchema ← treeStateSchema schema storage
  let (keys, valueSchema) ← lowerTreePath state.env treeSchema parentKeys
  let .recordSet environment type := valueSchema
    | throwErrorAt storage "typed record key operation requires a record Set"
  let fields ← match LedgerValueType.recordSetKeyFields environment type with
    | .ok fields => pure fields
    | .error message => throwErrorAt storage message
  let fieldTypes := (state.recordKeyFieldTypes.lookup storage.getId.toString).getD []
  let values ← elaborateLedgerFieldValues state payload fields fieldTypes
  pure (← pathKeysTerm keys, fields, values)

private def recordSetKeyValues (schema : List (String × StateKind))
    (storage : TSyntax `ident) (payload : TSyntax `nlleaves) (state : EntryEffects) :
    CommandElabM (List (String × Ty) × TSyntax `term) := do
  let (_, fields, values) ← recordSetKeyValuesAt schema storage [] payload state
  pure (fields, values)

private def elaborateRecordSetMember (schema : List (String × StateKind))
    (storage : TSyntax `ident) (payload : TSyntax `nlleaves) (destination : TSyntax `ident)
    (depth : Nat) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (_, values) ← recordSetKeyValues schema storage payload state
  let (readName, updated) ← freshReadName depth state destination
  let term ← `(Noctium.Effect.memberRecordSet
    $(stringTerm storage.getId.toString) $(stringTerm readName) ([] : List Noctium.PathKey) $values)
  bindReadName {updated with terms := updated.terms.push term}
    destination.getId.toString readName .bool

private def elaborateRecordSetMutation (schema : List (String × StateKind))
    (storage : TSyntax `ident) (payload : TSyntax `nlleaves) (inserting : _root_.Bool)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (_, values) ← recordSetKeyValues schema storage payload state
  let term ← if inserting then
    `(Noctium.Effect.setInsertRecord $(stringTerm storage.getId.toString) ([] : List Noctium.PathKey) $values)
  else
    `(Noctium.Effect.removeRecordSet $(stringTerm storage.getId.toString) ([] : List Noctium.PathKey) $values)
  pure {state with terms := state.terms.push term}

private def elaborateNestedRecordSetMember (schema : List (String × StateKind))
    (storage : TSyntax `ident) (owner : TSyntax `nlexpr) (payload : TSyntax `nlleaves)
    (destination : TSyntax `ident) (depth : Nat) (state : EntryEffects) :
    CommandElabM EntryEffects := do
  let (keys, _, values) ← recordSetKeyValuesAt schema storage [owner] payload state
  let (readName, updated) ← freshReadName depth state destination
  let term ← `(Noctium.Effect.memberRecordSet
    $(stringTerm storage.getId.toString) $(stringTerm readName) $keys $values)
  bindReadName {updated with terms := updated.terms.push term}
    destination.getId.toString readName .bool

private def elaborateNestedRecordSetMutation (schema : List (String × StateKind))
    (storage : TSyntax `ident) (owner : TSyntax `nlexpr) (payload : TSyntax `nlleaves)
    (inserting : _root_.Bool) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (keys, _, values) ← recordSetKeyValuesAt schema storage [owner] payload state
  let term ← if inserting then
    `(Noctium.Effect.setInsertRecord $(stringTerm storage.getId.toString) $keys $values)
  else
    `(Noctium.Effect.removeRecordSet $(stringTerm storage.getId.toString) $keys $values)
  pure {state with terms := state.terms.push term}

private def recordMapFieldsAt (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (state : EntryEffects) :
    CommandElabM (TSyntax `term × LedgerValueType × List (String × Ty) × TSyntax `term) := do
  let treeSchema ← treeStateSchema schema storage
  let (keys, valueSchema) ← lowerTreePath state.env treeSchema parentKeys
  let (environment, type) ← match valueSchema with
    | .recordMapKey environment type _ | .recordMapComposite environment type _ _ =>
      pure (environment, type)
    | _ => throwErrorAt storage "typed record key operation requires a record-key Map"
  let fieldResult := match valueSchema with
    | .recordMapKey .. | .recordMapComposite .. =>
      LedgerValueType.recordMapKeyFieldsAtDepth environment type parentKeys.length
    | _ => LedgerValueType.ledgerRecordWriteFields environment type
  let fields ← match fieldResult with
    | .ok fields => pure fields
    | .error message => throwErrorAt storage message
  let values ← elaborateRecordMapKeyFields state storage payload fields
  pure (← pathKeysTerm keys, valueSchema, fields, values)

private def recordMapKeyValuesAt (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (state : EntryEffects) :
    CommandElabM (TSyntax `term × List (String × Ty) × Ty × TSyntax `term) := do
  let (keys, valueSchema, fields, values) ← recordMapFieldsAt schema storage parentKeys payload state
  let .recordMapKey _ _ valueTy := valueSchema
    | throwErrorAt storage "typed record key operation requires a scalar-valued record-key Map"
  pure (keys, fields, valueTy, values)

private def nestedRecordMapAt (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (state : EntryEffects) : CommandElabM _root_.Bool := do
  let treeSchema ← treeStateSchema schema storage
  let (_, selected) ← lowerTreePath state.env treeSchema parentKeys
  pure (match selected with
    | .recordMapKey .. | .recordMapComposite .. => _root_.Bool.true
    | _ => _root_.Bool.false)

private def nestedRecordMapCompositeAt (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (state : EntryEffects) : CommandElabM _root_.Bool := do
  let treeSchema ← treeStateSchema schema storage
  let (_, selected) ← lowerTreePath state.env treeSchema parentKeys
  pure (match selected with
    | .recordMapComposite .. => _root_.Bool.true
    | _ => _root_.Bool.false)

private def elaborateRecordMapMember (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (destination : TSyntax `ident)
    (depth : Nat) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (keys, _, _, values) ← recordMapFieldsAt schema storage parentKeys payload state
  let (readName, updated) ← freshReadName depth state destination
  let term ← `(Noctium.Effect.memberRecordMap
    $(stringTerm storage.getId.toString) $(stringTerm readName) $values $keys)
  bindReadName {updated with terms := updated.terms.push term}
    destination.getId.toString readName .bool

private def elaborateRecordMapRead (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (destination : TSyntax `ident)
    (depth : Nat) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (keys, _, valueTy, values) ← recordMapKeyValuesAt schema storage parentKeys payload state
  let (readName, updated) ← freshReadName depth state destination
  let term ← `(Noctium.Effect.readRecordMap
    $(stringTerm storage.getId.toString) $(stringTerm readName) $(← tyTerm valueTy) $values $keys)
  let destinationName := destination.getId.toString
  let updated ← bindReadName {updated with terms := updated.terms.push term}
    destinationName readName valueTy
  pure {updated with
    nominalUIntBindings := bindCircuitNominal updated.nominalUIntBindings destinationName
      (state.collectionNominals storage).scalarValue
    contractRefBindings := bindContractRef updated.contractRefBindings destinationName
      (state.contractRefState.lookup storage.getId.toString)}

private def recordMapCompositeFieldsAt (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (state : EntryEffects) :
    CommandElabM (TSyntax `term × Types.CompositeType × List (String × Ty) ×
      Types.CompositeType × List (String × Ty)) := do
  let treeSchema ← treeStateSchema schema storage
  let (keys, selected) ← lowerTreePath state.env treeSchema parentKeys
  let .recordMapComposite keyEnvironment keyType valueEnvironment valueType := selected
    | throwErrorAt storage "typed record Map value operation requires a composite-valued record-key Map"
  let keyFieldResult := LedgerValueType.recordMapKeyFieldsAtDepth keyEnvironment keyType
    parentKeys.length
  let keyFields ← match keyFieldResult with
    | .ok fields => pure fields
    | .error message => throwErrorAt storage message
  let valueFields ← match (if parentKeys.isEmpty then
      LedgerValueType.rootMapRecordWriteFields valueEnvironment valueType
    else LedgerValueType.ledgerRecordWriteFields valueEnvironment valueType) with
    | .ok fields => pure fields
    | .error message => throwErrorAt storage message
  pure (← pathKeysTerm keys, keyType, keyFields, valueType, valueFields)

private def elaborateRecordMapCompositeRead (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (destination : TSyntax `ident)
    (depth : Nat) (state : EntryEffects) : CommandElabM EntryEffects := do
  let (parentPathTerm, _, keyFields, valueType, valueFields) ←
    recordMapCompositeFieldsAt schema storage parentKeys state
  let keyValues ← elaborateRecordMapKeyFields state storage payload keyFields
  let (readName, updated) ← freshReadName depth state destination
  let fieldTypes := (state.recordFieldTypes.lookup storage.getId.toString).getD []
  let (updated, destinations) ← bindLedgerRecordFields updated destination depth valueFields fieldTypes
  let .structure valueTypeId := valueType
    | throwErrorAt storage "record Map values require a named structure"
  let typeTerm ← `(Noctium.Types.CompositeType.structure $(stringTerm valueTypeId))
  let term ← `(Noctium.Effect.readRecordMapComposite
    $(stringTerm storage.getId.toString) $(stringTerm readName) $typeTerm
    $keyValues $destinations $parentPathTerm)
  pure {updated with terms := updated.terms.push term}

private def elaborateRecordMapCompositeWrite (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (payload valuePayload : TSyntax `nlleaves)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (parentPathTerm, _, keyFields, valueType, valueFields) ←
    recordMapCompositeFieldsAt schema storage parentKeys state
  let keyValues ← elaborateRecordMapKeyFields state storage payload keyFields
  let fieldTypes := (state.recordFieldTypes.lookup storage.getId.toString).getD []
  let valueValues ← elaborateLedgerFieldValues state valuePayload valueFields fieldTypes
  let .structure valueTypeId := valueType
    | throwErrorAt storage "record Map values require a named structure"
  let typeTerm ← `(Noctium.Types.CompositeType.structure $(stringTerm valueTypeId))
  let term ← `(Noctium.Effect.writeRecordMapComposite
    $(stringTerm storage.getId.toString) $typeTerm $keyValues $valueValues $parentPathTerm)
  pure {state with terms := state.terms.push term}

private def elaborateRecordMapWrite (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (value : TSyntax `nlexpr)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let (keys, _, valueTy, values) ← recordMapKeyValuesAt schema storage parentKeys payload state
  let value ← checkedSourceValue state.env state.nominalUIntBindings state.contractRefBindings value
    {type := valueTy, nominalUInt := (state.collectionNominals storage).scalarValue,
      contractRef := state.contractRefState.lookup storage.getId.toString}
    state.nominalFieldBindings
  let term ← `(Noctium.Effect.writeRecordMap
    $(stringTerm storage.getId.toString) $values $(← tyTerm valueTy) $value $keys)
  pure {state with terms := state.terms.push term}

private def elaborateRecordMapRemove (schema : List (String × StateKind))
    (storage : TSyntax `ident) (parentKeys : List (TSyntax `nlexpr))
    (payload : TSyntax `nlleaves) (state : EntryEffects) :
    CommandElabM EntryEffects := do
  let (keys, _, _, values) ← recordMapFieldsAt schema storage parentKeys payload state
  let term ← `(Noctium.Effect.removeRecordMap $(stringTerm storage.getId.toString) $values $keys)
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
    let (keys, selected) ← lowerMapPath state storage valueType sourceKeys
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
    unless selected.isCollection do
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
    let (keys, selected) ← lowerMapPath state storage valueType sourceKeys
    unless selected.isCollection do
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
      let updated ← bindReadName updated destination.getId.toString readName ty
      let nominalUInt := state.nominalUIntCells.lookup storage.getId.toString
      let nominalField := state.nominalFieldCells.lookup storage.getId.toString
      let contractRef := state.contractRefState.lookup storage.getId.toString
      pure {updated with
        nominalUIntBindings := bindCircuitNominal updated.nominalUIntBindings destination.getId.toString nominalUInt
        nominalFieldBindings := match nominalField with
        | none => updated.nominalFieldBindings
        | some field => (destination.getId.toString, some field) :: updated.nominalFieldBindings
        contractRefBindings := bindContractRef updated.contractRefBindings destination.getId.toString contractRef}
    | some (.map keyTy valueTy) => do
      let [key] := sourceKeys | throwErrorAt path "map reads require exactly one key"
      let (readName, updated) ← freshReadName depth state destination
      let loweredKey ← checkedRootMapKey state storage key keyTy
      let term ← `(Noctium.Effect.readMap
        $(stringTerm storage.getId.toString) $(stringTerm readName)
        $(← tyTerm keyTy) $(← tyTerm valueTy) $loweredKey)
      let updated := {updated with terms := updated.terms.push term}
      bindMapRead updated storage destination readName valueTy
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
      let loweredKey ← checkedRootMapKey state storage key keyTy
      let term ← `(Noctium.Effect.readMember
        $(stringTerm storage.getId.toString) $(stringTerm readName)
        $(← tyTerm keyTy) $(← tyTerm valueTy) $loweredKey)
      let updated := {updated with terms := updated.terms.push term}
      bindReadName updated destination.getId.toString readName .bool
    | some (.tree treeSchema) => do
      unless sourceKeys.length > 0 do
        throwErrorAt path "tree membership requires at least one key"
      let (keys, _) ← lowerMapEntryPath state storage treeSchema sourceKeys
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

private partial def typedClaimCall (value : TSyntax `nlexpr) :
    Option (String × TSyntax `nlexpr × Array (TSyntax `nlcallvalue) ×
      Array (TSyntax `nlcallvalue) × TSyntax `nlexpr) :=
  match value with
  | `(nlexpr| callCommitment($operation:str, $opening, [$inputs,*], [$outputs,*])) =>
    some (operation.getString, opening, inputs.getElems, outputs.getElems, value)
  | `(nlexpr| disclose($inner)) => typedClaimCall inner
  | _ => none

private partial def wrapClaimDisclosures (source : TSyntax `nlexpr)
    (value : TSyntax `term) : CommandElabM (TSyntax `term) := do
  match source with
  | `(nlexpr| disclose($inner)) => do
    let value ← wrapClaimDisclosures inner value
    `(Noctium.Expr.disclose $(← spanTerm source) $value)
  | _ => pure value

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

private def elaborateShieldedMerge (schema : List (String × StateKind)) (depth : Nat)
    (state : EntryEffects) (update : TSyntax `nlupdate) (storage : TSyntax `ident)
    (nonceA nonceB : TSyntax `nlexpr) (incoming : Option (TSyntax `nlexpr × TSyntax `nlexpr))
    (guard span : TSyntax `term) : CommandElabM EntryEffects := do
  let mut state := state
  let priorTerms := state.terms.size
  unless depth == 0 do
    throwErrorAt update "mergeShieldedFromMap must be unguarded"
  match guard with
  | `(term| none) => pure ()
  | _ => throwErrorAt update "mergeShieldedFromMap must be unguarded"
  let treeSchema ← treeStateSchema schema storage
  let .map keyTy (.composite environment recordType) := treeSchema
    | throwErrorAt storage "mergeShieldedFromMap requires a root Bytes32-keyed tree Map"
  unless keyTy == .bytes 32 do
    throwErrorAt storage "mergeShieldedFromMap map key must be Bytes32"
  let fields ← match LedgerValueType.shieldedCoinRecordFields environment recordType with
    | .ok fields => pure fields
    | .error message => throwErrorAt storage message
  unless fields.map Prod.fst == ["nonce", "color", "value", "mtIndex"] do
    throwErrorAt storage "mergeShieldedFromMap requires the exact shielded coin field order"
  let coinAName := s!"noctium_merge_coin_{state.terms.size}"
  let coinA := mkIdent (Name.mkSimple coinAName)
  state ← elaborateTreeRead storage coinA [nonceA] treeSchema depth state
  let (nonceARecordSyntax, colorASyntax, amountASyntax) ←
    readShieldedCoinFields coinAName
  let nonceARecord ← checkedExpression state.env nonceARecordSyntax (.bytes 32)
  let colorA ← checkedExpression state.env colorASyntax (.bytes 32)
  let amountA ← checkedExpression state.env amountASyntax (.uint (2 ^ 128 - 1))
  let keyAEqualitySyntax ← `(nlexpr| eq($nonceARecordSyntax, $nonceA))
  let keyAEquality ← checkedExpression state.env keyAEqualitySyntax .bool
  let requireKeyA ← `(Noctium.Effect.require $keyAEquality)
  state := {state with terms := state.terms.push requireKeyA}

  let (nonceBRecordSyntax, colorBSyntax, amountBSyntax) ← match incoming with
  | some (color, amount) => pure (nonceB, color, amount)
  | none => do
    let coinBName := s!"noctium_merge_coin_{state.terms.size}"
    let coinB := mkIdent (Name.mkSimple coinBName)
    state ← elaborateTreeRead storage coinB [nonceB] treeSchema depth state
    let (nonceBRecordSyntax, colorBSyntax, amountBSyntax) ←
      readShieldedCoinFields coinBName
    let keyBEqualitySyntax ← `(nlexpr| eq($nonceBRecordSyntax, $nonceB))
    let keyBEquality ← checkedExpression state.env keyBEqualitySyntax .bool
    let requireKeyB ← `(Noctium.Effect.require $keyBEquality)
    state := {state with terms := state.terms.push requireKeyB}
    pure (nonceBRecordSyntax, colorBSyntax, amountBSyntax)
  let nonceBRecord ← checkedExpression state.env nonceBRecordSyntax (.bytes 32)
  let colorB ← checkedExpression state.env colorBSyntax (.bytes 32)
  let amountB ← checkedExpression state.env amountBSyntax (.uint (2 ^ 128 - 1))

  let matchingColorSyntax ← `(nlexpr| eq($colorASyntax, $colorBSyntax))
  let matchingColor ← checkedExpression state.env matchingColorSyntax .bool
  let requireColor ← `(Noctium.Effect.require $matchingColor)
  let sameNonceSyntax ← `(nlexpr| eq($nonceA, $nonceB))
  let sameNonce ← checkedExpression state.env sameNonceSyntax .bool
  let distinctNonce ← `(Noctium.Expr.select $sameNonce
    (Noctium.Expr.bool Bool.false) (Noctium.Expr.bool Bool.true))
  let requireDistinct ← `(Noctium.Effect.require $distinctNonce)
  state := {state with terms := state.terms.push requireColor |>.push requireDistinct}

  let addressName := s!"noctium_merge_address_{state.terms.size}"
  unless state.env.all (fun binding => binding.1 != addressName) do
    throwErrorAt update "reserved mergeShieldedFromMap binding collides with an existing read"
  let addressTerm ← `(Noctium.Effect.readContractAddress $(stringTerm addressName))
  state := {state with terms := state.terms.push addressTerm}
  state ← bindReadName state addressName addressName (.bytes 32)
  let selfAddress ← `(@Noctium.Expr.ref (Noctium.Ty.bytes 32) $(stringTerm addressName))

  let mergedNonce ← `(Noctium.Wire.shieldedOutputNonce $nonceARecord)
  let mergedAmount ← `(Noctium.Expr.cast (Noctium.Ty.uint (2 ^ 128 - 1))
    (Noctium.Expr.uadd $amountA $amountB))
  let memberKey ← `(Noctium.PathKey.mk (Noctium.Ty.bytes 32) $mergedNonce)
  let memberKeys ← pathKeysTerm [memberKey]
  let memberName := s!"noctium_merge_member_{state.terms.size}"
  unless state.env.all (fun binding => binding.1 != memberName) do
    throwErrorAt update "reserved merge output membership binding collides with an existing read"
  let memberTerm ← `(Noctium.Effect.memberPath
    $(stringTerm storage.getId.toString) $(stringTerm memberName) $memberKeys)
  state := {state with terms := state.terms.push memberTerm}
  state ← bindReadName state memberName memberName .bool
  let absentCondition ← `(Noctium.Expr.eq
    (Noctium.Expr.ref $(stringTerm memberName)) (Noctium.Expr.bool Bool.false))
  let absentTerm ← `(Noctium.Effect.require $absentCondition)
  state := {state with terms := state.terms.push absentTerm}

  let staged ← if incoming.isSome then `(Bool.true) else `(Bool.false)
  let mergeTerm ← `(Noctium.Effect.mergeShieldedFromMap
    $(stringTerm storage.getId.toString)
    $nonceARecord $colorA $amountA $nonceBRecord $colorB $amountB $selfAddress $staged)
  state := {state with terms := state.terms.push mergeTerm}
  let keysA ← do
    let (path, _) ← lowerTreePath state.env treeSchema [nonceA]
    pathKeysTerm path
  let removeA ← `(Noctium.Effect.removePath $(stringTerm storage.getId.toString) $keysA)
  state := {state with terms := state.terms.push removeA}
  if incoming.isNone then
    let (path, _) ← lowerTreePath state.env treeSchema [nonceB]
    let keysB ← pathKeysTerm path
    let removeB ← `(Noctium.Effect.removePath $(stringTerm storage.getId.toString) $keysB)
    state := {state with terms := state.terms.push removeB}
  let receiveTerm ← `(Noctium.Effect.receiveShieldedToMap
    $(stringTerm storage.getId.toString) $mergedNonce $colorA $mergedAmount $selfAddress)
  let noGuard ← `(none)
  let terms := state.terms.push receiveTerm
  let extra := terms.size - priorTerms - 1
  return {state with
    terms := terms
    spans := state.spans ++ Array.replicate extra span
    guards := state.guards ++ Array.replicate extra noGuard}

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
    let guard ← effectGuardTerm state parent effect
    let span ← spanTerm effect
    return ← elaborateListHeadOrDefault schema path present record depth guard span state
  let guard ← effectGuardTerm state parent effect
  let span ← spanTerm effect
  let mut state := {state with
    spans := state.spans.push span
    guards := state.guards.push guard}
  match effect with
  | `(nleffect| $update:nlupdate)
  | `(nleffect| when $_:nlexpr $update:nlupdate) =>
    match update with
    | `(nlupdate| claimContractCall($address:nlexpr, $payload:nlexpr)) => do
      let targetInterface ← checkedContractRef state.contractRefBindings address
      let (operation, commitment) ← match targetInterface with
        | some interfaceName => do
          let some (operation, opening, inputs, outputs, call) := typedClaimCall payload
            | throwErrorAt payload "typed contract references require callCommitment(\"operation\", opening, [arguments], [results])"
          let methods ← interfaceMethods interfaceName
          let some method := methods.find? (·.operation == operation)
            | throwErrorAt call s!"contract interface '{interfaceName}' has no entry '{operation}'"
          let (_, commitment) ← commitmentHashWith state.env
            (fun value ty contractRef nominalUInt =>
              checkedSourceValue state.env state.nominalUIntBindings state.contractRefBindings
                value {type := ty, contractRef, nominalUInt})
            method opening inputs outputs call
          pure (operation, ← wrapClaimDisclosures payload commitment)
        | none => do
          if (typedClaimCall payload).isSome then
            throwErrorAt payload "interface callCommitment requires a typed contract reference"
          let some operation := typedClaimOperation payload
            | throwErrorAt payload "two-argument claimContractCall requires callCommitment, optionally wrapped in disclose"
          pure (operation, ← checkedExpression state.env payload .native)
      let address ← checkedExpression state.env address (.bytes 32)
      let digest ← natListTerm (EntryPointHash.hash operation)
      let term ← `(Noctium.Effect.claimContractCall $address (Noctium.Expr.bytes32Literal $digest) $commitment)
      state := {state with terms := state.terms.push term}
    | `(nlupdate| claimContractCall($address:nlexpr, $entryPointHash:nlexpr, $commitment:nlexpr)) => do
      if (← checkedContractRef state.contractRefBindings address).isSome then
        throwErrorAt address "typed contract references require the interface-based claimContractCall form"
      if (typedClaimCall commitment).isSome then
        throwErrorAt commitment "interface callCommitment requires a typed contract reference"
      let address ← checkedExpression state.env address (.bytes 32)
      let entryPointHash ← checkedExpression state.env entryPointHash (.bytes 32)
      let commitment ← checkedExpression state.env commitment .native
      let term ← `(Noctium.Effect.claimContractCall $address $entryPointHash $commitment)
      state := {state with terms := state.terms.push term}
    | `(nlupdate| claimShielded($kind:ident, $digest:nlexpr)) => do
      let kind ← match kind.getId.toString with
        | "nullifier" => `(Noctium.ShieldedClaimKind.nullifier)
        | "receive" => `(Noctium.ShieldedClaimKind.receive)
        | "spend" => `(Noctium.ShieldedClaimKind.spend)
        | _ => throwErrorAt kind "expected shielded claim kind nullifier, receive, or spend"
      let digest ← checkedExpression state.env digest (.bytes 32)
      let term ← `(Noctium.Effect.claimShielded $kind $digest)
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
      checkNominalBytes32Argument state recipient .contractAddress "relayShieldedImmediate"
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
    | `(nlupdate| insertShieldedCoinMap($path:nlpath, $key:nlexpr,
        $nonce:nlexpr, $color:nlexpr, $amount:nlexpr,
        $isContract:nlexpr, $recipient:nlexpr)) => do
      unless depth == 0 do
        throwErrorAt update "insertShieldedCoinMap must be unguarded"
      match guard with
      | `(term| none) => pure ()
      | _ => throwErrorAt update "insertShieldedCoinMap must be unguarded"
      let (storage, keys) ← lowerQualifiedCoinMapPath schema state.env path
      let key ← checkedExpression state.env key (.bytes 32)
      let nonce ← checkedExpression state.env nonce (.bytes 32)
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint (2 ^ 128 - 1))
      let isContract ← checkedExpression state.env isContract .bool
      let recipient ← checkedExpression state.env recipient (.bytes 32)
      let insertTerm ← `(Noctium.Effect.insertShieldedCoinMap
        $(stringTerm storage.getId.toString) $key $nonce $color $amount $isContract $recipient $keys)
      state := {state with terms := state.terms.push insertTerm}
    | `(nlupdate| insertShieldedCoinSet($path:nlpath, $nonce:nlexpr,
        $color:nlexpr, $amount:nlexpr, $isContract:nlexpr, $recipient:nlexpr)) => do
      unless depth == 0 do
        throwErrorAt update "insertShieldedCoinSet must be unguarded"
      match guard with
      | `(term| none) => pure ()
      | _ => throwErrorAt update "insertShieldedCoinSet must be unguarded"
      let (storage, keys) ← lowerQualifiedCoinSetPath schema state.env path
      let nonce ← checkedExpression state.env nonce (.bytes 32)
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint (2 ^ 128 - 1))
      let isContract ← checkedExpression state.env isContract .bool
      let recipient ← checkedExpression state.env recipient (.bytes 32)
      let insertTerm ← `(Noctium.Effect.insertShieldedCoinSetTo
        $(stringTerm storage.getId.toString) $nonce $color $amount $isContract $recipient $keys)
      state := {state with terms := state.terms.push insertTerm}
    | `(nlupdate| insertShieldedCoinSet($path:nlpath, $nonce:nlexpr,
        $color:nlexpr, $amount:nlexpr)) => do
      unless depth == 0 do
        throwErrorAt update "insertShieldedCoinSet must be unguarded"
      match guard with
      | `(term| none) => pure ()
      | _ => throwErrorAt update "insertShieldedCoinSet must be unguarded"
      let (storage, keys) ← lowerQualifiedCoinSetPath schema state.env path
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
        $(stringTerm storage.getId.toString) $nonce $color $amount $selfAddress $keys)
      let noGuard ← `(none)
      state := {state with
        terms := state.terms.push insertTerm
        spans := state.spans.push span
        guards := state.guards.push noGuard}
    | `(nlupdate| writeShieldedCoinCell($storage:ident, $nonce:nlexpr,
        $color:nlexpr, $amount:nlexpr, $isContract:nlexpr, $recipient:nlexpr)) => do
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
      let isContract ← checkedExpression state.env isContract .bool
      let recipient ← checkedExpression state.env recipient (.bytes 32)
      let writeTerm ← `(Noctium.Effect.writeShieldedCoinCellTo
        $(stringTerm storage.getId.toString) $nonce $color $amount $isContract $recipient)
      state := {state with terms := state.terms.push writeTerm}
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
    | `(nlupdate| pushFrontCoin($path:nlpath, $nonce:nlexpr,
        $color:nlexpr, $amount:nlexpr, $isContract:nlexpr, $recipient:nlexpr)) => do
      unless depth == 0 do
        throwErrorAt update "pushFrontCoin must be unguarded"
      match guard with
      | `(term| none) => pure ()
      | _ => throwErrorAt update "pushFrontCoin must be unguarded"
      let (storage, keys) ← lowerQualifiedCoinListPath schema state.env path
      let nonce ← checkedExpression state.env nonce (.bytes 32)
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint (2 ^ 128 - 1))
      let isContract ← checkedExpression state.env isContract .bool
      let recipient ← checkedExpression state.env recipient (.bytes 32)
      let pushTerm ← `(Noctium.Effect.pushFrontCoinTo
        $(stringTerm storage.getId.toString) $nonce $color $amount $isContract $recipient $keys)
      state := {state with terms := state.terms.push pushTerm}
    | `(nlupdate| pushFrontCoin($path:nlpath, $nonce:nlexpr,
        $color:nlexpr, $amount:nlexpr)) => do
      unless depth == 0 do
        throwErrorAt update "pushFrontCoin must be unguarded"
      match guard with
      | `(term| none) => pure ()
      | _ => throwErrorAt update "pushFrontCoin must be unguarded"
      let (storage, keys) ← lowerQualifiedCoinListPath schema state.env path
      let nonce ← checkedExpression state.env nonce (.bytes 32)
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint (2 ^ 128 - 1))
      let addressName := s!"noctium_coin_list_address_{state.terms.size}"
      unless state.env.all (fun binding => binding.1 != addressName) do
        throwErrorAt update "reserved pushFrontCoin binding collides with an existing read"
      let addressTerm ← `(Noctium.Effect.readContractAddress $(stringTerm addressName))
      state := {state with terms := state.terms.push addressTerm}
      state ← bindReadName state addressName addressName (.bytes 32)
      let selfAddress ← `(@Noctium.Expr.ref (Noctium.Ty.bytes 32) $(stringTerm addressName))
      let pushTerm ← `(Noctium.Effect.pushFrontCoin
        $(stringTerm storage.getId.toString) $nonce $color $amount $selfAddress $keys)
      let noGuard ← `(none)
      state := {state with
        terms := state.terms.push pushTerm
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
    | `(nlupdate| mergeShieldedFromMap($storage:ident, $nonceA:nlexpr, $nonceB:nlexpr)) =>
      state ← elaborateShieldedMerge schema depth state update storage nonceA nonceB none guard span
    | `(nlupdate| mergeShieldedImmediateFromMap($storage:ident, $nonceA:nlexpr, $nonceB:nlexpr,
          $color:nlexpr, $amount:nlexpr)) =>
      state ← elaborateShieldedMerge schema depth state update storage nonceA nonceB
        (some (color, amount)) guard span
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
      checkNominalBytes32Argument state recipient .zswapCoinPublicKey "sendShieldedFromMap"
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
    | `(nlupdate| receiveUnshielded($color:nlexpr, $amount:nlexpr)) => do
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint balanceMaximum)
      let term ← `(Noctium.Effect.incUnshieldedInputs $color $amount
        (Noctium.Expr.bool Bool.true))
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
    | `(nlupdate| claimUnshieldedCoinSpendTo($color:nlexpr, $amount:nlexpr,
        $isUnshielded:nlexpr, $address:nlexpr)) => do
      let color ← checkedExpression state.env color (.bytes 32)
      let amount ← checkedExpression state.env amount (.uint balanceMaximum)
      let isUnshielded ← checkedExpression state.env isUnshielded .bool
      let (isContract, recipient) ← match address with
        | `(nlexpr| publicAddressContract($value)) => do
          requireNominalBytes32Argument state value .contractAddress "contract"
          let recipient ← checkedExpression state.env value (.bytes 32)
          pure (← `(Noctium.Expr.bool Bool.true), recipient)
        | `(nlexpr| publicAddressUser($value)) => do
          requireNominalBytes32Argument state value .userAddress "user"
          let recipient ← checkedExpression state.env value (.bytes 32)
          pure (← `(Noctium.Expr.bool Bool.false), recipient)
        | _ => throwErrorAt address
          "claimUnshieldedCoinSpendTo requires publicAddressContract(...) or publicAddressUser(...)"
      let term ← `(Noctium.Effect.claimUnshieldedCoinSpend
        $color $amount $isUnshielded $isContract $recipient)
      state := {state with terms := state.terms.push term}
    | `(nlupdate| claimUnshieldedCoinSpend($color:nlexpr, $amount:nlexpr,
        $isUnshielded:nlexpr, $isContract:nlexpr, $recipient:nlexpr)) => do
      checkUnshieldedRecipientTag state isContract recipient
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
    let condition ← checkedCircuitSourceExpression state.env state.nominalUIntBindings value
      {type := .bool}
    let term ← `(Noctium.Effect.require $condition)
    state := {state with terms := state.terms.push term}
  | `(nleffect| when $_:nlexpr require $value:nlexpr) =>
    let condition ← checkedCircuitSourceExpression state.env state.nominalUIntBindings value
      {type := .bool}
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
  | `(nleffect| read $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ] as $destination:ident)
  | `(nleffect| when $_:nlexpr read $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ] as $destination:ident) =>
    if ← nestedRecordMapCompositeAt schema storage [owner] state then
      state := ← elaborateRecordMapCompositeRead schema storage [owner]
        payload destination depth state
    else
      state := ← elaborateRecordMapRead schema storage [owner] payload destination depth state
  | `(nleffect| read $storage:ident [ $payload:nlleaves ] as $destination:ident)
  | `(nleffect| when $_:nlexpr read $storage:ident [ $payload:nlleaves ] as $destination:ident) =>
    match (← statePathSchema schema storage) with
    | .recordMapComposite .. =>
      state := ← elaborateRecordMapCompositeRead schema storage []
        payload destination depth state
    | _ => state := ← elaborateRecordMapRead schema storage [] payload destination depth state
  | `(nleffect| read $path:nlpath as $destination:ident)
  | `(nleffect| when $_:nlexpr read $path:nlpath as $destination:ident) =>
    state := ← elaborateNamedPathRead schema "read" path destination depth guard state
  | `(nleffect| readSelf as $destination:ident)
  | `(nleffect| when $_:nlexpr readSelf as $destination:ident) => do
    let (readName, updated) ← freshReadName depth state destination
    let term ← `(Noctium.Effect.readContractAddress $(stringTerm readName))
    let updated ← bindReadName {updated with terms := updated.terms.push term}
      destination.getId.toString readName (.bytes 32)
    state := addNominalBytes32Binding updated destination.getId.toString .contractAddress
  | `(nleffect| mintUnshieldedTo($domain, $amount, $isContract, $recipient) as $destination:ident)
  | `(nleffect| when $_:nlexpr mintUnshieldedTo($domain, $amount, $isContract, $recipient) as $destination:ident) =>
    state := ← elaborateUnshieldedMintTo state domain amount isContract recipient destination guard span
  | `(nleffect| member $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ] as $destination:ident)
  | `(nleffect| when $_:nlexpr member $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ] as $destination:ident) => do
    if ← nestedRecordMapAt schema storage [owner] state then
      state ← elaborateRecordMapMember schema storage [owner] payload destination depth state
    else
      state ← elaborateNestedRecordSetMember schema storage owner payload destination depth state
  | `(nleffect| member $storage:ident [ $payload:nlleaves ] as $destination:ident)
  | `(nleffect| when $_:nlexpr member $storage:ident [ $payload:nlleaves ] as $destination:ident) =>
    match (← statePathSchema schema storage) with
    | .recordMapKey .. | .recordMapComposite .. =>
      state := ← elaborateRecordMapMember schema storage [] payload destination depth state
    | _ => state := ← elaborateRecordSetMember schema storage payload destination depth state
  | `(nleffect| member $path:nlpath as $destination:ident)
  | `(nleffect| when $_:nlexpr member $path:nlpath as $destination:ident) =>
    state := ← elaborateNamedPathRead schema "member" path destination depth guard state
  | `(nleffect| blockTimeBefore($deadline) as $destination:ident)
  | `(nleffect| when $_:nlexpr blockTimeBefore($deadline) as $destination:ident) =>
    state := ← elaborateBlockTimeRead state depth destination Bool.true deadline
  | `(nleffect| blockTimeAfter($deadline) as $destination:ident)
  | `(nleffect| when $_:nlexpr blockTimeAfter($deadline) as $destination:ident) =>
    state := ← elaborateBlockTimeRead state depth destination Bool.false deadline
  | `(nleffect| blockTimeAtOrAfter($deadline) as $destination:ident)
  | `(nleffect| when $_:nlexpr blockTimeAtOrAfter($deadline) as $destination:ident) =>
    state := ← elaborateBlockTimeRead state depth destination Bool.true deadline (some guard)
  | `(nleffect| blockTimeAtOrBefore($deadline) as $destination:ident)
  | `(nleffect| when $_:nlexpr blockTimeAtOrBefore($deadline) as $destination:ident) =>
    state := ← elaborateBlockTimeRead state depth destination Bool.false deadline (some guard)
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
    let nominalUInt := state.nominalUIntCells.lookup storage.getId.toString
    let nominalField := state.nominalFieldCells.lookup storage.getId.toString
    let contractRef := state.contractRefState.lookup storage.getId.toString
    let loweredValue ← checkedSourceValue state.env state.nominalUIntBindings state.contractRefBindings value
      {type := ty, nominalUInt, nominalField, contractRef} state.nominalFieldBindings
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
  | `(nleffect| insert $storage:ident [ $payload:nlleaves ] := $value:nlexpr)
  | `(nleffect| when $_:nlexpr insert $storage:ident [ $payload:nlleaves ] := $value:nlexpr) =>
    state := ← elaborateRecordMapWrite schema storage [] payload value state
  | `(nleffect| insert $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ] := $valuePayload:nlleaves)
  | `(nleffect| when $_:nlexpr insert $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ] := $valuePayload:nlleaves) =>
    state := ← elaborateRecordMapCompositeWrite schema storage [owner]
      payload valuePayload state
  | `(nleffect| insert $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ] := $value:nlexpr)
  | `(nleffect| when $_:nlexpr insert $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ] := $value:nlexpr) =>
    state := ← elaborateRecordMapWrite schema storage [owner] payload value state
  | `(nleffect| insert $storage:ident [ $payload:nlleaves ] := $valuePayload:nlleaves)
  | `(nleffect| when $_:nlexpr insert $storage:ident [ $payload:nlleaves ] := $valuePayload:nlleaves) =>
    state := ← elaborateRecordMapCompositeWrite schema storage []
      payload valuePayload state
  | `(nleffect| insert $storage:ident [ $key:nlexpr ] := $value:nlexpr)
  | `(nleffect| when $_:nlexpr insert $storage:ident [ $key:nlexpr ] := $value:nlexpr) => do
    let term ← match schema.lookup storage.getId.toString with
      | some (.map keyTy valueTy) => do
        let loweredKey ← checkedRootMapKey state storage key keyTy
        let loweredValue ← checkedMapValue state storage value valueTy
        `(Noctium.Effect.writeMap
          $(stringTerm storage.getId.toString) $(← tyTerm keyTy) $(← tyTerm valueTy)
          $loweredKey $loweredValue)
      | some (.tree _) => do
        let treeSchema ← treeStateSchema schema storage
        let (path, selected) ← lowerTreePath state.env treeSchema [key]
        let valueTy ← match selected with
          | .scalar .opaqueBytes => pure .opaqueBytes
          | .scalar .opaqueString => pure .opaqueString
          | _ => throwErrorAt storage "single-key tree insertion supports only OpaqueBytes or OpaqueString leaves"
        let loweredValue ← checkedExpression state.env value valueTy
        let keys ← pathKeysTerm path
        `(Noctium.Effect.insertPath $(stringTerm storage.getId.toString) $keys
          $(← tyTerm valueTy) $loweredValue)
      | _ => throwErrorAt storage "insert requires a declared state map or opaque-value tree"
    state := {state with terms := state.terms.push term}
  | `(nleffect| insert $storage:ident [$owner:nlexpr] := emptyMap) => do
    let schema ← treeStateSchema schema storage
    let (path, result) ← lowerMapPath state storage schema [owner]
    unless result.isCollection do throwErrorAt effect "emptyMap assignment must select a map or Set value"
    let keys ← pathKeysTerm path
    let term ← `(Noctium.Effect.emptyMapPath $(stringTerm storage.getId.toString) $keys)
    state := {state with terms := state.terms.push term}
  | `(nleffect| insert $storage:ident [ $key:nlexpr ] := $payload:nlleaves)
  | `(nleffect| write $storage:ident [ $key:nlexpr ] := $payload:nlleaves) => do
    state ← elaborateCompositePathWrite schema storage [key] payload state
  | `(nleffect| write $storage:ident := $payload:nlleaves) => do
    state ← elaborateCompositePathWrite schema storage [] payload state
  | `(nleffect| insert $storage:ident [ $owner:nlexpr ] [ $spender:nlexpr ] := $payload:nlleaves)
  | `(nleffect| write $storage:ident [ $owner:nlexpr ] [ $spender:nlexpr ] := $payload:nlleaves) => do
    state ← elaborateCompositePathWrite schema storage [owner, spender] payload state
  | `(nleffect| insert $storage:ident [$owner:nlexpr] [$spender:nlexpr] := $value:nlexpr)
  | `(nleffect| write $storage:ident [$owner:nlexpr] [$spender:nlexpr] := $value:nlexpr) => do
    let schema ← treeStateSchema schema storage
    let (path, result) ← lowerMapPath state storage schema [owner, spender]
    let .scalar ty := result | throwErrorAt effect "nested scalar write must select a scalar value"
    let loweredValue ← checkedMapValue state storage value ty
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
  | `(nleffect| remove $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ])
  | `(nleffect| when $_:nlexpr remove $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ]) => do
    if ← nestedRecordMapAt schema storage [owner] state then
      state ← elaborateRecordMapRemove schema storage [owner] payload state
    else
      state ← elaborateNestedRecordSetMutation schema storage owner payload Bool.false state
  | `(nleffect| remove $storage:ident [ $payload:nlleaves ])
  | `(nleffect| when $_:nlexpr remove $storage:ident [ $payload:nlleaves ]) =>
    match (← statePathSchema schema storage) with
    | .recordMapKey .. | .recordMapComposite .. => state := ← elaborateRecordMapRemove schema storage [] payload state
    | _ => state := ← elaborateRecordSetMutation schema storage payload Bool.false state
  | `(nleffect| remove $path:nlpath)
  | `(nleffect| when $_:nlexpr remove $path:nlpath) =>
    state := ← elaborateMapRemove schema path state
  | `(nleffect| insert $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ])
  | `(nleffect| when $_:nlexpr insert $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ]) => do
    if ← nestedRecordMapAt schema storage [owner] state then
      throwErrorAt storage "record-key Map insert requires a value"
    else
      state ← elaborateNestedRecordSetMutation schema storage owner payload Bool.true state
  | `(nleffect| insert $storage:ident [ $payload:nlleaves ])
  | `(nleffect| when $_:nlexpr insert $storage:ident [ $payload:nlleaves ]) =>
    match (← statePathSchema schema storage) with
    | .recordMapKey .. | .recordMapComposite .. => throwErrorAt storage "record-key Map insert requires a value"
    | _ => state := ← elaborateRecordSetMutation schema storage payload Bool.true state
  | `(nleffect| insert $path:nlpath)
  | `(nleffect| when $_:nlexpr insert $path:nlpath) =>
    state := ← elaborateSetInsert schema path state
  | `(nleffect| insertDefault $path:nlpath)
  | `(nleffect| when $_:nlexpr insertDefault $path:nlpath) =>
    state := ← elaborateMapDefault schema path state
  | `(nleffect| insertDefault $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ])
  | `(nleffect| when $_:nlexpr insertDefault $storage:ident [ $owner:nlexpr ] [ $payload:nlleaves ]) =>
    state := ← elaborateRecordMapDefault schema storage [owner] payload state
  | `(nleffect| insertDefault $storage:ident [ $payload:nlleaves ])
  | `(nleffect| when $_:nlexpr insertDefault $storage:ident [ $payload:nlleaves ]) =>
    state := ← elaborateRecordMapDefault schema storage [] payload state
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
    let loweredKey ← checkedRootMapKey state storage key keyTy
    let term ← `(Noctium.Effect.requireAbsent
      $(stringTerm storage.getId.toString) $(← tyTerm keyTy) $loweredKey)
    state := {state with terms := state.terms.push term}
  | _ => throwErrorAt effect "unsupported Noctium state effect"
  pure state

private def hasNominalFieldRootRecordMapKey (schema : List (String × StateKind))
    (state : EntryEffects) (storage : TSyntax `ident) (keyFields : TSyntax `nlleaves) : _root_.Bool := Id.run do
  let storageName := storage.getId.toString
  let rootRecordMap := match schema.lookup storageName with
    | some (.tree (.recordMapKey ..)) | some (.tree (.recordMapComposite ..)) => _root_.Bool.true
    | _ => _root_.Bool.false
  let keyHasNominalField :=
    ((state.recordKeyFieldTypes.lookup storageName).getD []).any fun (_, sourceType) =>
      sourceType.nominalField.isSome
  return rootRecordMap && keyHasNominalField &&
    hasCircuitNominalFieldReference state.nominalFieldBindings keyFields.raw

private def hasNominalFieldRecordSetKey (schema : List (String × StateKind))
    (state : EntryEffects) (storage : TSyntax `ident) (parent : Option (TSyntax `nlexpr))
    (keyFields : TSyntax `nlleaves) : _root_.Bool := Id.run do
  let storageName := storage.getId.toString
  let recordSet := match schema.lookup storageName, parent with
    | some (.tree (.recordSet ..)), none => _root_.Bool.true
    | some (.tree (.map _ (.recordSet ..))), some owner =>
        !hasCircuitNominalFieldReference state.nominalFieldBindings owner.raw
    | _, _ => _root_.Bool.false
  let keyHasNominalField :=
    ((state.recordKeyFieldTypes.lookup storageName).getD []).any fun (_, sourceType) =>
      sourceType.nominalField.isSome
  return recordSet && keyHasNominalField &&
    hasCircuitNominalFieldReference state.nominalFieldBindings keyFields.raw

private def hasNominalFieldRootScalarSetKey (schema : List (String × StateKind))
    (state : EntryEffects) (storage : TSyntax `ident) (key : TSyntax `nlexpr) : _root_.Bool := Id.run do
  let storageName := storage.getId.toString
  let scalarSet := match schema.lookup storageName with
    | some (.tree (.set .native)) => _root_.Bool.true
    | _ => _root_.Bool.false
  let keyHasNominalField :=
    ((state.collectionNominals storage).pathFieldKeys.head?).join.isSome
  return scalarSet && keyHasNominalField &&
    hasCircuitNominalFieldReference state.nominalFieldBindings key.raw

private def hasNominalFieldRootScalarSetPath (schema : List (String × StateKind))
    (state : EntryEffects) (path : TSyntax `nlpath) : _root_.Bool :=
  match path with
  | `(nlpath| $storage:ident [ $key:nlexpr ]) =>
    hasNominalFieldRootScalarSetKey schema state storage key
  | _ => _root_.Bool.false

private def hasOnlyCheckedNominalFieldPosition (schema : List (String × StateKind))
    (state : EntryEffects) (effect : TSyntax `nleffect) : _root_.Bool := Id.run do
  let fieldBindings := state.nominalFieldBindings
  let typedKey storage keyFields :=
    hasNominalFieldRootRecordMapKey schema state storage keyFields
  let typedRecordSetKey storage keyFields :=
    hasNominalFieldRecordSetKey schema state storage none keyFields
  let typedNestedRecordSetKey storage owner keyFields :=
    hasNominalFieldRecordSetKey schema state storage (some owner) keyFields
  let typedScalarSetPath := hasNominalFieldRootScalarSetPath schema state
  match effect with
  | `(nleffect| write $_:ident := $_:nlexpr) => _root_.Bool.true
  | `(nleffect| when $condition:nlexpr write $_:ident := $value:nlexpr) =>
      !hasCircuitNominalFieldReference fieldBindings condition.raw &&
        hasCircuitNominalFieldReference fieldBindings value.raw
  | `(nleffect| write $_:ident := $payload:nlleaves) =>
      hasCircuitNominalFieldReference fieldBindings payload.raw
  | `(nleffect| write $_:ident [ $key:nlexpr ] := $payload:nlleaves)
  | `(nleffect| insert $_:ident [ $key:nlexpr ] := $payload:nlleaves) =>
      !hasCircuitNominalFieldReference fieldBindings key.raw &&
        hasCircuitNominalFieldReference fieldBindings payload.raw
  | `(nleffect| write $_:ident [ $first:nlexpr ] [ $second:nlexpr ] := $payload:nlleaves)
  | `(nleffect| insert $_:ident [ $first:nlexpr ] [ $second:nlexpr ] := $payload:nlleaves) =>
      !hasCircuitNominalFieldReference fieldBindings first.raw &&
        !hasCircuitNominalFieldReference fieldBindings second.raw &&
        hasCircuitNominalFieldReference fieldBindings payload.raw
  | `(nleffect| insert $storage:ident [ $keyFields:nlleaves ] := $payload:nlleaves) =>
      (typedKey storage keyFields ||
        !hasCircuitNominalFieldReference fieldBindings keyFields.raw) &&
        (hasCircuitNominalFieldReference fieldBindings payload.raw ||
          hasCircuitNominalFieldReference fieldBindings keyFields.raw)
  | `(nleffect| when $condition:nlexpr insert $storage:ident [ $keyFields:nlleaves ] := $payload:nlleaves) =>
      !hasCircuitNominalFieldReference fieldBindings condition.raw &&
        (typedKey storage keyFields ||
          !hasCircuitNominalFieldReference fieldBindings keyFields.raw) &&
        (hasCircuitNominalFieldReference fieldBindings payload.raw ||
          hasCircuitNominalFieldReference fieldBindings keyFields.raw)
  | `(nleffect| insert $storage:ident [ $keyFields:nlleaves ] := $_:nlexpr) =>
      typedKey storage keyFields
  | `(nleffect| when $condition:nlexpr insert $storage:ident [ $keyFields:nlleaves ] := $_:nlexpr) =>
      !hasCircuitNominalFieldReference fieldBindings condition.raw &&
        typedKey storage keyFields
  | `(nleffect| insert $storage:ident [ $owner:nlexpr ] [ $keyFields:nlleaves ])
  | `(nleffect| remove $storage:ident [ $owner:nlexpr ] [ $keyFields:nlleaves ])
  | `(nleffect| member $storage:ident [ $owner:nlexpr ] [ $keyFields:nlleaves ] as $_:ident) =>
      typedNestedRecordSetKey storage owner keyFields
  | `(nleffect| when $condition:nlexpr insert $storage:ident [ $owner:nlexpr ]
      [ $keyFields:nlleaves ])
  | `(nleffect| when $condition:nlexpr remove $storage:ident [ $owner:nlexpr ]
      [ $keyFields:nlleaves ])
  | `(nleffect| when $condition:nlexpr member $storage:ident [ $owner:nlexpr ]
      [ $keyFields:nlleaves ] as $_:ident) =>
      !hasCircuitNominalFieldReference fieldBindings condition.raw &&
        typedNestedRecordSetKey storage owner keyFields
  | `(nleffect| insert $storage:ident [ $keyFields:nlleaves ])
  | `(nleffect| remove $storage:ident [ $keyFields:nlleaves ]) =>
      typedRecordSetKey storage keyFields
  | `(nleffect| when $condition:nlexpr insert $storage:ident [ $keyFields:nlleaves ])
  | `(nleffect| when $condition:nlexpr remove $storage:ident [ $keyFields:nlleaves ]) =>
      !hasCircuitNominalFieldReference fieldBindings condition.raw &&
        typedRecordSetKey storage keyFields
  | `(nleffect| insert $path:nlpath)
  | `(nleffect| remove $path:nlpath)
  | `(nleffect| member $path:nlpath as $_:ident) =>
      typedScalarSetPath path
  | `(nleffect| when $condition:nlexpr insert $path:nlpath)
  | `(nleffect| when $condition:nlexpr remove $path:nlpath)
  | `(nleffect| when $condition:nlexpr member $path:nlpath as $_:ident) =>
      !hasCircuitNominalFieldReference fieldBindings condition.raw && typedScalarSetPath path
  | `(nleffect| read $storage:ident [ $keyFields:nlleaves ] as $_:ident)
  | `(nleffect| member $storage:ident [ $keyFields:nlleaves ] as $_:ident) =>
      typedKey storage keyFields || typedRecordSetKey storage keyFields
  | `(nleffect| when $condition:nlexpr read $storage:ident [ $keyFields:nlleaves ] as $_:ident)
  | `(nleffect| when $condition:nlexpr member $storage:ident [ $keyFields:nlleaves ] as $_:ident) =>
      !hasCircuitNominalFieldReference fieldBindings condition.raw &&
        (typedKey storage keyFields || typedRecordSetKey storage keyFields)
  | `(nleffect| insert $_:ident [ $outerKey:nlexpr ] [ $keyFields:nlleaves ] := $payload:nlleaves) =>
      !hasCircuitNominalFieldReference fieldBindings outerKey.raw &&
        !hasCircuitNominalFieldReference fieldBindings keyFields.raw &&
        hasCircuitNominalFieldReference fieldBindings payload.raw
  | `(nleffect| when $condition:nlexpr insert $_:ident [ $outerKey:nlexpr ]
      [ $keyFields:nlleaves ] := $payload:nlleaves) =>
      !hasCircuitNominalFieldReference fieldBindings condition.raw &&
        !hasCircuitNominalFieldReference fieldBindings outerKey.raw &&
        !hasCircuitNominalFieldReference fieldBindings keyFields.raw &&
        hasCircuitNominalFieldReference fieldBindings payload.raw
  | `(nleffect| pushFront $path:nlpath := $payload:nlleaves) =>
      !hasCircuitNominalFieldReference fieldBindings path.raw &&
        hasCircuitNominalFieldReference fieldBindings payload.raw
  | `(nleffect| when $condition:nlexpr pushFront $path:nlpath := $payload:nlleaves) =>
      !hasCircuitNominalFieldReference fieldBindings condition.raw &&
        !hasCircuitNominalFieldReference fieldBindings path.raw &&
        hasCircuitNominalFieldReference fieldBindings payload.raw
  | _ => _root_.Bool.false

private partial def elaborateStatements (schema : List (String × StateKind))
    (parent : Option (TSyntax `term)) (depth : Nat)
    (statements : Array (TSyntax `nlstatement)) (initial : EntryEffects) :
    CommandElabM EntryEffects := do
  let mut state := initial
  for statement in statements do
    match statement with
    | `(nlstatement| $effect:nleffect) =>
      if hasCircuitNominalFieldReference state.nominalFieldBindings effect.raw &&
          !hasOnlyCheckedNominalFieldPosition schema state effect then
        throwErrorAt effect "nominal Field effects require a direct scalar Cell write"
      state ← elaborateEffect schema parent depth state effect
    | `(nlstatement| if $condition:nlexpr then { $thenStatements:nlstatement* }
        else { $elseStatements:nlstatement* }) => do
      let condition ← checkedSourceValue state.env state.nominalUIntBindings state.contractRefBindings condition
        {type := .bool} state.nominalFieldBindings
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
      let branchNominalUIntBindings := state.nominalUIntBindings
      let branchNominalFieldBindings := state.nominalFieldBindings
      let branchContractRefs := state.contractRefBindings
      let branchNominalBytes32Bindings := state.nominalBytes32Bindings
      let branchOptionalRecordHeads := state.optionalRecordHeads
      let afterThen ← elaborateStatements schema thenPath (depth + 1) thenStatements state
      let afterElse ← elaborateStatements schema elsePath (depth + 1) elseStatements
        {afterThen with
          env := branchEnv
          nominalUIntBindings := branchNominalUIntBindings
          nominalFieldBindings := branchNominalFieldBindings
          contractRefBindings := branchContractRefs
          nominalBytes32Bindings := branchNominalBytes32Bindings
          optionalRecordHeads := branchOptionalRecordHeads}
      state := {afterElse with
        env := branchEnv
        nominalUIntBindings := branchNominalUIntBindings
        nominalFieldBindings := branchNominalFieldBindings
        contractRefBindings := branchContractRefs
        nominalBytes32Bindings := branchNominalBytes32Bindings
        optionalRecordHeads := branchOptionalRecordHeads}
    | _ => throwErrorAt statement "unsupported Noctium state statement"
  pure state

private def maybeReturnBinding (environment : Bindings) (name : String) :
    Option (Ty × TSyntax `term) := do
  let (_, ty, expression) ← environment.find? (fun binding => binding.1 == name)
  pure (ty, expression)

private def sourceSpanValueTerm (span : SourceSpan) : CommandElabM (TSyntax `term) := do
  `({ file := $(stringTerm span.file), line := $(natTerm span.line),
      column := $(natTerm span.column) : Noctium.SourceSpan })

private def maybeCompositeTypeTerm (type : Types.CompositeType) : CommandElabM (TSyntax `term) := do
  match type with
  | .scalar ty => `(Noctium.Types.CompositeType.scalar $(← tyTerm ty))
  | .structure id => `(Noctium.Types.CompositeType.structure $(stringTerm id))
  | _ => throwError "returnMaybe nested records only support scalar leaves and named structs"

private def returnMaybeListFieldTySupported : Ty → _root_.Bool
  | .native => _root_.Bool.true
  | .bool => _root_.Bool.true
  | .uint _ => _root_.Bool.true
  | _ => _root_.Bool.false

private def flatMaybeRecordId (head : OptionalRecordHead) : Option String := do
  let .structure typeId := head.type | none
  let declaration ← head.environment.structures.find? (·.id == typeId)
  guard (!declaration.fields.isEmpty)
  let fields := head.fieldPaths.map fun (_, name, ty) => (name, ty)
  guard (!fields.isEmpty)
  guard (fields.all fun (_, ty) => returnMaybeListFieldTySupported ty)
  guard (head.fields == fields)
  pure typeId

private def maybeRecordTypeId (contractName recordId : String) : CommandElabM String := do
  let recordName := (recordId.splitOn ".").getLast!
  let typeId := s!"{contractName}.Maybe{recordName}"
  unless Types.validDeclId typeId do
    throwError "generated record Maybe type id is invalid"
  pure typeId

private def recordMaybeEnvironment (environment : Types.CompositeEnv) (recordId typeId : String)
    (span : SourceSpan) : CommandElabM (TSyntax `term) := do
  let some record := environment.structures.find? (·.id == recordId)
    | throwError s!"List record declaration '{recordId}' is missing"
  let expectedFields : List (String × Types.CompositeType) := [
    ("is_some", .scalar .bool),
    ("value", .structure recordId)
  ]
  if environment.enumerations.any (·.id == typeId) then
    throwError s!"generated record Maybe type id '{typeId}' collides with an enum"
  if environment.structures.any (·.id == typeId) then
    throwError s!"generated record Maybe type id '{typeId}' collides with another structure"
  let sourceStructures ← environment.structures.toArray.mapM fun declaration => do
    let sourceFields ← declaration.fields.toArray.mapM fun field => do
      let name := stringTerm field.name
      let fieldType ← maybeCompositeTypeTerm field.type
      let fieldSpan ← sourceSpanValueTerm field.span
      `(Noctium.Types.Field.mk $name $fieldType $fieldSpan)
    let id := stringTerm declaration.id
    let declarationSpan ← sourceSpanValueTerm declaration.span
    `(Noctium.Types.StructDecl.mk $id [$sourceFields,*] $declarationSpan)
  let generated : Types.StructDecl := {
    id := typeId
    fields := expectedFields.map fun (name, type) => {name, type, span}
    span
  }
  let extended : Types.CompositeEnv := {
    environment with structures := environment.structures ++ [generated]
  }
  match Types.compileType extended (.structure typeId) with
    | .ok _ => pure ()
    | .error diagnostic => throwError diagnostic.message
  let typeIdTerm := stringTerm typeId
  let recordIdTerm := stringTerm recordId
  let isSomeName := stringTerm "is_some"
  let isSomeType ← `(Noctium.Types.CompositeType.scalar $(← tyTerm .bool))
  let isSomeSpan ← sourceSpanValueTerm span
  let isSomeField ← `(Noctium.Types.Field.mk $isSomeName $isSomeType $isSomeSpan)
  let valueName := stringTerm "value"
  let valueType ← `(Noctium.Types.CompositeType.structure $recordIdTerm)
  let valueSpan ← sourceSpanValueTerm span
  let valueField ← `(Noctium.Types.Field.mk $valueName $valueType $valueSpan)
  let generatedSpan ← sourceSpanValueTerm span
  let generatedTerm ← `(Noctium.Types.StructDecl.mk $typeIdTerm [$isSomeField, $valueField] $generatedSpan)
  let allStructures := sourceStructures.push generatedTerm
  let term ← `(Noctium.Types.CompositeEnv.mk [$allStructures,*]
    ([] : List Noctium.Types.EnumDecl))
  pure term

private def elaborateRecordMaybeReturn (contractName : String) (label : TSyntax `ident)
    (presentExpression : TSyntax `term)
    (statement : TSyntax `nlreturn) (state : EntryEffects) (head : OptionalRecordHead) :
    CommandElabM EntryEffects := do
  let some recordId := flatMaybeRecordId head
    | throwErrorAt statement
      "returnMaybe record payload must be a checked Native, Bool, or UInt List record"
  let labelName := label.getId.toString
  let typeId ← maybeRecordTypeId contractName recordId
  let compositeType ← `(Noctium.Types.CompositeType.structure $(stringTerm typeId))
  let span ← spanTerm statement
  let file ← getFileName
  let fileMap ← getFileMap
  let position := fileMap.toPosition (statement.raw.getPos?.getD 0)
  let spanValue : SourceSpan := {
    file
    line := position.line
    column := position.column + 1
  }
  let environmentTerm ←
    recordMaybeEnvironment head.environment recordId typeId spanValue
  let isSomeReturnName := s!"{labelName}_is_some"
  let valueReturnNames := head.fieldPaths.map fun (_, field, _) => s!"{labelName}_value_{field}"
  let physicalNames := isSomeReturnName :: valueReturnNames
  let physicalNameTerms := physicalNames.toArray.map stringTerm
  for returnName in physicalNames do
    if state.env.any (fun binding => binding.1 == returnName) then
      throwErrorAt label s!"structured return field '{returnName}' collides with an input or read binding"
  let isSomeReturn ← `(Noctium.Output.mk $(stringTerm isSomeReturnName) Noctium.Ty.native
    (Noctium.Expr.cast Noctium.Ty.native $presentExpression) $span)
  let mut returnTerms := #[isSomeReturn]
  for ((_, fieldName, fieldTy), returnName) in head.fieldPaths.zip valueReturnNames do
    let bindingName := s!"{head.recordName}_{fieldName}"
    let expectedNominalUInt := head.nominalUIntFields.lookup fieldName
    let actualNominalUInt := (state.nominalUIntBindings.lookup bindingName).join
    unless actualNominalUInt == expectedNominalUInt do
      throwErrorAt statement
        s!"returnMaybe record field '{bindingName}' does not match its declared nominal UInt identity"
    let some (bindingTy, fieldExpression) := maybeReturnBinding state.env bindingName
      | throwErrorAt statement s!"returnMaybe record field '{bindingName}' is not a typed binding"
    unless bindingTy == fieldTy do
      throwErrorAt statement s!"returnMaybe record field '{bindingName}' has the wrong type"
    -- Keep the physical ledger ABI Native. The logical return view restores the
    -- checked Bool or UInt field type for host reconstruction.
    let canonicalField ← if fieldTy == .native then pure fieldExpression else
      `(Noctium.Expr.cast Noctium.Ty.native $fieldExpression)
    let fieldReturn ← `(Noctium.Output.mk $(stringTerm returnName) Noctium.Ty.native
      $canonicalField $span)
    returnTerms := returnTerms.push fieldReturn
  let orderedNominalUIntFields := head.fieldPaths.filterMap fun (fieldPath, fieldName, _) =>
    (head.nominalUIntFields.lookup fieldName).map fun nominalUInt => (fieldPath, nominalUInt)
  let nominalUIntFieldTerms ← orderedNominalUIntFields.toArray.mapM fun (fieldPath, nominalUInt) => do
    let name := stringTerm nominalUInt.name
    let maximum := natTerm nominalUInt.maximum
    let nominalUIntTerm ← `({name := $name, maximum := $maximum : Noctium.NominalUIntType})
    let path := (#[(stringTerm "value")] ++ fieldPath.toArray.map stringTerm)
    `(Noctium.NominalUIntReturnField.mk [$path,*] $nominalUIntTerm)
  let view ← `({
    name := $(stringTerm labelName)
    environment := $environmentTerm
    type := $compositeType
    fields := [$physicalNameTerms,*]
    nominalUIntFields := [$nominalUIntFieldTerms,*]
    : Noctium.ReturnView })
  pure {state with
    returns := state.returns ++ returnTerms
    returnViews := state.returnViews.push view
  }

private def elaborateMaybeReturn (contractName : String) (label : TSyntax `ident)
    (presentName payloadName : TSyntax `ident) (statement : TSyntax `nlreturn)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let labelName := label.getId.toString
  let presentBindingName := presentName.getId.toString
  let payloadBindingName := payloadName.getId.toString
  let some (.bool, presentExpression) := maybeReturnBinding state.env presentBindingName
    | throwErrorAt presentName "returnMaybe tag must reference a Bool binding"
  if let some head := state.optionalRecordHeads.find? fun candidate =>
      candidate.presentName == presentBindingName && candidate.recordName == payloadBindingName then
    return ← elaborateRecordMaybeReturn contractName label presentExpression
      statement state head
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

private def scalarDefault (payloadType : Ty) : CommandElabM (TSyntax `term) := do
  match payloadType with
  | .native => `(Noctium.Expr.native 0)
  | .bool => `(Noctium.Expr.bool Bool.false)
  | .uint maximum => `(Noctium.Expr.uint $(natTerm maximum) 0)
  | _ => throwError "scalar tagged return payload must be Native, Bool, or UInt"

private def elaborateEitherReturn (contractName : String) (label : TSyntax `ident)
    (isLeftName leftName rightName : TSyntax `ident) (statement : TSyntax `nlreturn)
    (state : EntryEffects) : CommandElabM EntryEffects := do
  let labelName := label.getId.toString
  let isLeftBindingName := isLeftName.getId.toString
  let leftBindingName := leftName.getId.toString
  let rightBindingName := rightName.getId.toString
  let some (.bool, isLeftExpression) := maybeReturnBinding state.env isLeftBindingName
    | throwErrorAt isLeftName "returnEither tag must reference a Bool binding"
  let some (leftType, leftExpression) := maybeReturnBinding state.env leftBindingName
    | throwErrorAt leftName "returnEither left value must reference a scalar binding"
  let some (rightType, rightExpression) := maybeReturnBinding state.env rightBindingName
    | throwErrorAt rightName "returnEither right value must reference a scalar binding"
  let typeId ← match Noctium.Types.Either.scalarTypeId contractName leftType rightType with
    | .ok value => pure value
    | .error message => throwErrorAt statement message
  let _environment ← match Noctium.Types.Either.scalarEnvironment typeId leftType rightType with
    | .ok value => pure value
    | .error message => throwErrorAt statement message
  let fieldTypes ← match Noctium.Types.Either.scalarFieldTypes leftType rightType with
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
  let leftDefault ← scalarDefault leftType
  let rightDefault ← scalarDefault rightType
  let canonicalLeft ← `(Noctium.Expr.select $isLeftExpression $leftExpression $leftDefault)
  let canonicalRight ← `(Noctium.Expr.select $isLeftExpression $rightDefault $rightExpression)
  let isLeftReturnName := s!"{labelName}_is_left"
  let leftReturnName := s!"{labelName}_left"
  let rightReturnName := s!"{labelName}_right"
  for returnName in [isLeftReturnName, leftReturnName, rightReturnName] do
    if state.env.any (fun binding => binding.1 == returnName) then
      throwErrorAt label s!"structured return field '{returnName}' collides with an input or read binding"
  let isLeftReturn ← `({ name := $(stringTerm isLeftReturnName), ty := Noctium.Ty.native, value := (Noctium.Expr.cast Noctium.Ty.native $isLeftExpression), span := $span : Noctium.Output })
  let leftReturn ← `({ name := $(stringTerm leftReturnName), ty := Noctium.Ty.native, value := (Noctium.Expr.cast Noctium.Ty.native $canonicalLeft), span := $span : Noctium.Output })
  let rightReturn ← `({ name := $(stringTerm rightReturnName), ty := Noctium.Ty.native, value := (Noctium.Expr.cast Noctium.Ty.native $canonicalRight), span := $span : Noctium.Output })
  let compositeType ← `(Noctium.Types.CompositeType.structure $typeIdTerm)
  let view ← `({ name := $(stringTerm labelName), environment := $environmentTerm, type := $compositeType, fields := [$(stringTerm isLeftReturnName), $(stringTerm leftReturnName), $(stringTerm rightReturnName)] : Noctium.ReturnView })
  pure {state with
    returns := state.returns.push isLeftReturn |>.push leftReturn |>.push rightReturn
    returnViews := state.returnViews.push view}

private def elaborateReturns (contractName : String) (statements : Array (TSyntax `nlreturn))
    (info : CircuitInfo) (initial : EntryEffects)
    (allowNominalField : _root_.Bool := _root_.Bool.false) : CommandElabM EntryEffects := do
  let mut state := initial
  let mut labels : List String := []
  for statement in statements do
    match statement with
    | `(nlreturn| returnMaybe $label:ident as ($present:ident, $payload:ident)) => do
      if state.nominalFieldBindings.any (·.2.isSome) then
        throwErrorAt label "nominal Field values are only supported in scalar contract returns"
      let labelName := label.getId.toString
      if labels.contains labelName then
        throwErrorAt label "duplicate entry return label '{labelName}'"
      if state.env.any (fun binding => binding.1 == labelName) then
        throwErrorAt label "entry return label '{labelName}' collides with an input or read binding"
      state ← elaborateMaybeReturn contractName label present payload statement state
      labels := labelName :: labels
    | `(nlreturn| returnEither $label:ident as ($isLeft:ident, $left:ident, $right:ident)) => do
      if state.nominalFieldBindings.any (·.2.isSome) then
        throwErrorAt label "nominal Field values are only supported in scalar contract returns"
      let labelName := label.getId.toString
      if labels.contains labelName then
        throwErrorAt label "duplicate entry return label '{labelName}'"
      if state.env.any (fun binding => binding.1 == labelName) then
        throwErrorAt label "entry return label '{labelName}' collides with an input or read binding"
      state ← elaborateEitherReturn contractName label isLeft left right statement state
      labels := labelName :: labels
    | `(nlreturn| return $label:ident : $returnTy:nltype := $value:nlexpr) => do
      let labelName := label.getId.toString
      if labels.contains labelName then
        throwErrorAt label "duplicate entry return label '{labelName}'"
      if state.env.any (fun binding => binding.1 == labelName) then
        throwErrorAt label "entry return label '{labelName}' collides with an input or read binding"
      labels := labelName :: labels
      let sourceType ← readCircuitSourceType returnTy allowNominalField
      let ty := sourceType.type
      let value ← checkedSourceValue state.env state.nominalUIntBindings state.contractRefBindings
        value sourceType state.nominalFieldBindings
      let span ← spanTerm statement
      state := {state with
        returns := state.returns.push (← `({
        name := $(stringTerm labelName), ty := $(← tyTerm ty), value := $value,
        span := $span : Noctium.Output }))
        returnContractRefs := match sourceType.contractRef with
          | some interface => state.returnContractRefs ++ [(labelName, interface)]
          | none => state.returnContractRefs
        returnNominalUInts := match sourceType.nominalUInt with
          | some nominalUInt => state.returnNominalUInts ++ [(labelName, nominalUInt)]
          | none => state.returnNominalUInts
        returnNominalFields := match sourceType.nominalField with
          | some nominalField => state.returnNominalFields ++ [(labelName, nominalField)]
          | none => state.returnNominalFields
      }
    | `(nlreturn| return $label:ident) => do
      let labelName := label.getId.toString
      let some (_, schema, sourceFields) := info.aggregateOutputs.find? (·.1 == labelName)
        | throwErrorAt label "unknown aggregate circuit output '{labelName}'"
      if sourceFields.any fun field => info.nominalFieldOutputs.any (·.1 == field) then
        throwErrorAt label "aggregate contract returns do not retain nominal Field output identity"
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
    CommandElabM (String × CircuitSourceType) := do
  let `(nlcompositefield| $fieldName:ident : $fieldType:nltype) := field
    | throwErrorAt field "unsupported composite record field"
  pure (fieldName.getId.toString, ← readCircuitSourceType fieldType)

private partial def readMerkleCompositeField (rootId path : String)
    (field : TSyntax `nlmerkleafield) :
    CommandElabM (Types.Field × List Types.StructDecl × List (String × Ty)) := do
  match field with
  | `(nlmerkleafield| $fieldName:ident : $fieldType:nltype) => do
    let name := fieldName.getId.toString
    let ty ← readTy fieldType
    let compositeType := match ty with
      | .bytes length => Types.CompositeType.bytes length
      | _ => Types.CompositeType.scalar ty
    let leafName := if path.isEmpty then name else path ++ "." ++ name
    pure ({name, type := compositeType}, [], [(leafName, ty)])
  | `(nlmerkleafield| $fieldName:ident : struct $recordName:ident { $fields:nlmerkleafield* }) => do
    let name := fieldName.getId.toString
    let fieldPath := if path.isEmpty then name else path ++ "." ++ name
    let nestedId := rootId ++ "." ++ fieldPath ++ "." ++ recordName.getId.toString
    let mut nestedFields : Array Types.Field := #[]
    let mut nestedDeclarations : Array Types.StructDecl := #[]
    let mut leafFields : Array (String × Ty) := #[]
    for nestedField in fields do
      let (layoutField, declarations, leaves) ←
        readMerkleCompositeField rootId fieldPath nestedField
      nestedFields := nestedFields.push layoutField
      for declaration in declarations do
        nestedDeclarations := nestedDeclarations.push declaration
      for leaf in leaves do
        leafFields := leafFields.push leaf
    let declaration : Types.StructDecl := {
      id := nestedId
      fields := nestedFields.toList
    }
    let parent : Types.Field := {name, type := .structure nestedId}
    pure (parent, declaration :: nestedDeclarations.toList, leafFields.toList)
  | _ => throwErrorAt field "expected a scalar or nested struct MerkleTree field"

private partial def elaborateTypedLedgerFields (parentId pathPrefix : String)
    (recordFields : Array (TSyntax `nlcompositefield)) (owner : Syntax)
    (allowNominalField : _root_.Bool := _root_.Bool.false) :
    CommandElabM (Array (TSyntax `term) × List Types.Field × Array (TSyntax `term) ×
      List Types.StructDecl × List (String × CircuitSourceType)) := do
  let mut fieldTerms : Array (TSyntax `term) := #[]
  let mut fieldValues : List Types.Field := []
  let mut nestedTerms : Array (TSyntax `term) := #[]
  let mut nestedValues : List Types.StructDecl := []
  let mut fieldTypes : List (String × CircuitSourceType) := []
  for field in recordFields do
    match field with
    | `(nlcompositefield| $fieldName:ident : $fieldType:nltype) => do
      let name := fieldName.getId.toString
      let sourceType ← readCircuitSourceType fieldType (allowNominalField && pathPrefix.isEmpty)
      let fieldTy := sourceType.type
      let physicalName := if pathPrefix.isEmpty then name else s!"{pathPrefix}_{name}"
      if sourceType.contractRef.isSome || sourceType.nominalUInt.isSome ||
          sourceType.nominalField.isSome then
        fieldTypes := fieldTypes ++ [(physicalName, sourceType)]
      fieldValues := fieldValues ++ [{name, type := .scalar fieldTy}]
      let fieldTypeTerm ← `(Noctium.Types.CompositeType.scalar $(← tyTerm fieldTy))
      let fieldSpan ← spanTerm field
      fieldTerms := fieldTerms.push (← `({ name := $(stringTerm name), type := $fieldTypeTerm, span := $fieldSpan : Noctium.Types.Field }))
    | `(nlcompositefield| $fieldName:ident : struct $record:ident { $children:nlcompositefield* }) => do
      let name := fieldName.getId.toString
      let path := if pathPrefix.isEmpty then name else s!"{pathPrefix}_{name}"
      let nestedId := s!"{parentId}.{path}.{record.getId}"
      let (childTerms, childFields, descendantTerms, descendants, childTypes) ←
        elaborateTypedLedgerFields nestedId path children owner allowNominalField
      let structSpan ← spanTerm field
      let nestedTerm ← `({ id := $(stringTerm nestedId), fields := [$childTerms,*], span := $structSpan : Noctium.Types.StructDecl })
      let structureFieldType ← `(Noctium.Types.CompositeType.structure $(stringTerm nestedId))
      let fieldSpan ← spanTerm field
      fieldTerms := fieldTerms.push (← `({ name := $(stringTerm name), type := $structureFieldType, span := $fieldSpan : Noctium.Types.Field }))
      fieldValues := fieldValues ++ [{name, type := .structure nestedId}]
      nestedTerms := nestedTerms ++ descendantTerms
      nestedTerms := nestedTerms.push nestedTerm
      nestedValues := nestedValues ++ descendants ++ [{id := nestedId, fields := childFields}]
      fieldTypes := fieldTypes ++ childTypes
    | _ => throwErrorAt field "expected a scalar or nested named ledger record field"
  pure (fieldTerms, fieldValues, nestedTerms, nestedValues, fieldTypes)

private def elaborateTypedLedgerRecord (contractName : Name) (record : TSyntax `ident)
    (recordFields : Array (TSyntax `nlcompositefield)) (owner : Syntax)
    (allowNested : _root_.Bool := _root_.Bool.false)
    (allowNominalField : _root_.Bool := _root_.Bool.false) :
    CommandElabM ((Types.CompositeEnv × Types.CompositeType × TSyntax `term × TSyntax `term) ×
      List (String × CircuitSourceType)) := do
  let containsNested := recordFields.any fun field =>
      match field with
      | `(nlcompositefield| $_:ident : struct $_:ident { $_:nlcompositefield* }) => _root_.Bool.true
      | _ => _root_.Bool.false
  if !allowNested && containsNested then
    throwErrorAt owner "nested named records are supported only by root Lists"
  let typeId := contractName.toString ++ "." ++ record.getId.toString
  let (fieldTerms, fieldValues, nestedTerms, nestedValues, fieldTypes) ←
    elaborateTypedLedgerFields typeId "" recordFields owner allowNominalField
  let structSpan ← spanTerm owner
  let structureTerm ← `({ id := $(stringTerm typeId), fields := [$fieldTerms,*], span := $structSpan : Noctium.Types.StructDecl })
  let allTerms := #[structureTerm] ++ nestedTerms
  let environmentTerm ← `({ structures := [$allTerms,*] : Noctium.Types.CompositeEnv })
  let compositeType := Types.CompositeType.structure typeId
  let compositeTypeTerm ← `(Noctium.Types.CompositeType.structure $(stringTerm typeId))
  let environment : Types.CompositeEnv := {
    structures := [{id := typeId, fields := fieldValues}] ++ nestedValues
  }
  pure ((environment, compositeType, environmentTerm, compositeTypeTerm), fieldTypes)

private def elaborateNamedRecord (contractName : Name) (record : TSyntax `ident)
    (recordFields : Array (TSyntax `nlcompositefield)) (owner : Syntax) :
    CommandElabM (Types.CompositeEnv × Types.CompositeType × TSyntax `term × TSyntax `term) := do
  let (layout, fieldTypes) ← elaborateTypedLedgerRecord contractName record recordFields owner
  if fieldTypes.any (fun (_, field) => field.contractRef.isSome) then
    throwErrorAt owner "typed contract reference fields are unsupported for this ledger layout"
  if fieldTypes.any (fun (_, field) => field.nominalField.isSome) then
    throwErrorAt owner "nominal Field record fields are unsupported for this ledger layout"
  unless fieldTypes.isEmpty do
    throwErrorAt owner "nominal UInt record fields are unsupported for this ledger layout"
  pure layout

private def elaborateScalarListDecl (keys : List (TSyntax `nltype)) (elementTy : Ty) :
    CommandElabM (StateKind × TSyntax `term) := do
  let mut valueSchema := LedgerValueType.«list» {} (.scalar elementTy)
  let mut valueTerm ← `(Noctium.LedgerValueType.«list» {}
    (Noctium.Types.CompositeType.scalar $(← tyTerm elementTy)))
  for key in keys.reverse do
    let keyTy ← readTy key
    valueSchema := .map keyTy valueSchema
    valueTerm ← `(Noctium.LedgerValueType.map $(← tyTerm keyTy) $valueTerm)
  pure (.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))

set_option maxHeartbeats 1000000 in
private def elaborateConstructor (source : TSyntax `nlstate)
    (schema : List (String × StateKind))
    (nominalUIntCells : List (String × NominalUIntType))
    (nominalFieldCells : List (String × NominalFieldType))
    (nominalUIntLists : List (String × NominalUIntType))
    (nominalCollections : List (String × CollectionNominals))
    (contractRefState : List (String × Name))
    (recordFieldTypes recordKeyFieldTypes : List (String × List (String × CircuitSourceType))) :
    CommandElabM (TSyntax `term) := do
  let `(nlstate| constructor($parameters:nlconstructorparam,*) where $initializers:nlconstructorinit* end) := source
    | throwErrorAt source "invalid Noctium constructor declaration"
  let hasCounterReads := initializers.any fun initializer =>
    match initializer with
    | `(nlconstructorinit| initializeCounter $_:ident from $_:ident) => _root_.Bool.true
    | _ => _root_.Bool.false
  let mut parameterTerms : Array (TSyntax `term) := #[]
  let mut scalarBindings : Bindings := []
  let mut nominalUIntBindings : CircuitNominalEnv := []
  let mut nominalFieldBindings : List (String × Option NominalFieldType) := []
  let mut contractRefs : List (String × Name) := []
  let mut opaqueParameters : List String := []
  let mut parameterNames : List String := []
  for parameter in parameters.getElems.toList do
    let (name, parameterType, typeTerm, bytePattern) ← match parameter with
      | `(nlconstructorparam| $id:ident : $sourceTy:nltype as [$patterns,*]) => do
        let name := id.getId.toString
        let sourceType ← readCircuitSourceType sourceTy
        let ty := sourceType.type
        nominalUIntBindings := bindCircuitNominal nominalUIntBindings name sourceType.nominalUInt
        contractRefs := bindContractRef contractRefs name sourceType.contractRef
        if ty == .opaqueString then
          throwErrorAt parameter "byte constructor patterns require a fixed Bytes parameter"
        let .bytes length := ty
          | throwErrorAt parameter "byte constructor patterns require a fixed Bytes parameter"
        let pattern := patterns.getElems.toList.map fun item =>
          if item.raw.isIdent then some item.raw.getId.toString else none
        unless pattern.length == length do
          throwErrorAt parameter s!"byte constructor pattern requires exactly {length} items"
        pure (name, ConstructorType.scalar ty,
          ← `(Noctium.ConstructorType.scalar $(← tyTerm ty)), some (length, pattern))
      | `(nlconstructorparam| $id:ident : $sourceTy:nltype) => do
        let name := id.getId.toString
        let sourceType ← readCircuitSourceType sourceTy _root_.Bool.true
        let ty := sourceType.type
        nominalUIntBindings := bindCircuitNominal nominalUIntBindings name sourceType.nominalUInt
        if sourceType.nominalField.isSome then
          nominalFieldBindings := (name, sourceType.nominalField) :: nominalFieldBindings
        contractRefs := bindContractRef contractRefs name sourceType.contractRef
        if ty == .opaqueString then
          pure (name, ConstructorType.opaqueString, ← `(Noctium.ConstructorType.opaqueString), none)
        else
          pure (name, ConstructorType.scalar ty,
            ← `(Noctium.ConstructorType.scalar $(← tyTerm ty)), none)
      | _ => throwErrorAt parameter "unsupported constructor parameter"
    if parameterNames.contains name then throwErrorAt parameter s!"duplicate constructor parameter '{name}'"
    parameterNames := name :: parameterNames
    if parameterType == .opaqueString then
      opaqueParameters := name :: opaqueParameters
    else
      let .scalar ty := parameterType | throwErrorAt parameter "invalid scalar constructor parameter"
      let reference ← `(@Noctium.Expr.ref $(← tyTerm ty) $(stringTerm name))
      scalarBindings := (name, ty, reference) :: scalarBindings
      if let some (_, pattern) := bytePattern then
        for (binding?, index) in pattern.zipIdx do
          match binding? with
          | none => pure ()
          | some binding =>
            if parameterNames.contains binding then
              throwErrorAt parameter s!"duplicate constructor parameter or byte binding '{binding}'"
            parameterNames := binding :: parameterNames
            let byteReference ← `(Noctium.Expr.bytesAt $(reference) $(natTerm index))
            scalarBindings := (binding, .uint 255, byteReference) :: scalarBindings
    parameterTerms := parameterTerms.push (← `(Noctium.ConstructorParameter.mk $(stringTerm name) $typeTerm))
  let mut initializerTerms : Array (TSyntax `term) := #[]
  let mut mapInsertTerms : Array (TSyntax `term) := #[]
  let mut orderedActionTerms : Array (TSyntax `term) := #[]
  let mut hasOrderedActions : _root_.Bool := _root_.Bool.false
  let mut counterIncrementTerms : Array (TSyntax `term) := #[]
  let mut listPushTerms : Array (TSyntax `term) := #[]
  let mut setInsertTerms : Array (TSyntax `term) := #[]
  let mut initializedNames : List String := []
  let bindings : EntryEffects := {
    env := scalarBindings, nominalUIntBindings, nominalFieldBindings,
    contractRefBindings := contractRefs, recordFieldTypes, recordKeyFieldTypes
  }
  let isNominalFieldScalarSet (storage : TSyntax `ident) : _root_.Bool :=
    match schema.lookup storage.getId.toString with
    | some (.tree (.set .native)) =>
      ((nominalCollections.lookup storage.getId.toString).getD {}).pathFieldKeys.head?.join.isSome
    | _ => _root_.Bool.false
  for initializer in initializers do
    let hasUncheckedNominalField := match initializer with
      | `(nlconstructorinit| initialize $_:ident := $_:nlexpr)
      | `(nlconstructorinit| insert $_:ident[$_:nlleaves]) => _root_.Bool.false
      | `(nlconstructorinit| when $condition:nlexpr insert $_:ident[$_:nlleaves]) =>
        hasCircuitNominalFieldReference nominalFieldBindings condition.raw
      | `(nlconstructorinit| insert $storage:ident [ $key:nlexpr ]) =>
        hasCircuitNominalFieldReference nominalFieldBindings key.raw &&
          !isNominalFieldScalarSet storage
      | `(nlconstructorinit| when $condition:nlexpr insert $storage:ident [ $key:nlexpr ]) =>
        hasCircuitNominalFieldReference nominalFieldBindings condition.raw ||
          (hasCircuitNominalFieldReference nominalFieldBindings key.raw &&
            !isNominalFieldScalarSet storage)
      | _ => hasCircuitNominalFieldReference nominalFieldBindings initializer.raw
    if hasUncheckedNominalField then
      throwErrorAt initializer "nominal Field constructor values require a direct scalar Cell initializer or typed Set key"
    match initializer with
    | `(nlconstructorinit| initialize $stateName:ident := $payload:nlleaves) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      let some (.tree (.composite environment type)) := schema.lookup destination
        | throwErrorAt stateName "constructor fields initialization requires a root record Cell"
      if initializedNames.contains destination then
        throwErrorAt initializer s!"duplicate constructor initializer for '{destination}'"
      let fields ← match LedgerValueType.cellWriteRecordFields environment type with
        | .ok fields => pure fields
        | .error message => throwErrorAt payload message
      let values ← elaborateLedgerFieldValues bindings payload fields
        ((recordFieldTypes.lookup destination).getD [])
      initializedNames := destination :: initializedNames
      orderedActionTerms := orderedActionTerms.push
        (← `(Noctium.ConstructorAction.initializeRecordCell $(stringTerm destination) $values))
      hasOrderedActions := _root_.Bool.true
    | `(nlconstructorinit| insert $stateName:ident[$key:nlexpr] := $payload:nlleaves)
    | `(nlconstructorinit|
        when $_:nlexpr insert $stateName:ident[$key:nlexpr] := $payload:nlleaves) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      let some (.tree (.map (.bytes 32) (.composite environment type))) := schema.lookup destination
        | throwErrorAt stateName "constructor fields insert requires a Bytes32-keyed record Map"
      let keyExpression ← checkedSourceValue scalarBindings nominalUIntBindings contractRefs key
        {type := .bytes 32}
      let key ← `(Noctium.PathKey.mk (Noctium.Ty.bytes 32) $keyExpression)
      let fields ← match LedgerValueType.rootMapRecordWriteFields environment type with
        | .ok fields => pure fields
        | .error message => throwErrorAt payload message
      let values ← elaborateLedgerFieldValues bindings payload fields
        ((recordFieldTypes.lookup destination).getD [])
      let guard ← match initializer with
        | `(nlconstructorinit|
            when $condition:nlexpr insert $_:ident[$_:nlexpr] := $_:nlleaves) => do
          let conditionExpression ← checkedCircuitSourceExpression scalarBindings
            nominalUIntBindings condition {type := .bool}
          `(some $conditionExpression)
        | `(nlconstructorinit|
            insert $_:ident[$_:nlexpr] := $_:nlleaves) => `(none)
        | _ => throwErrorAt initializer "invalid constructor record Map insert"
      orderedActionTerms := orderedActionTerms.push
        (← `(Noctium.ConstructorAction.insertRecordMap $(stringTerm destination) $key $values $guard))
      hasOrderedActions := _root_.Bool.true
    | `(nlconstructorinit| insert $stateName:ident[$keyPayload:nlleaves] := $payload:nlleaves)
    | `(nlconstructorinit|
        when $condition:nlexpr insert $stateName:ident[$keyPayload:nlleaves] := $payload:nlleaves) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      let some (.tree (.recordMapComposite keyEnvironment keyType valueEnvironment valueType)) :=
          schema.lookup destination
        | throwErrorAt stateName
            "constructor fields insert requires a root record-valued record-key Map"
      let .structure valueTypeId := valueType
        | throwErrorAt stateName "constructor record Map values require a named structure"
      let checkedKeyFields ← match LedgerValueType.recordMapKeyFields keyEnvironment keyType with
        | .ok fields => pure fields
        | .error message => throwErrorAt stateName message
      let keyValues ← elaborateRecordMapKeyFields bindings stateName keyPayload checkedKeyFields
      let valueFields ← match LedgerValueType.ledgerRecordWriteFields valueEnvironment valueType with
        | .ok fields => pure fields
        | .error message => throwErrorAt stateName message
      let valueValues ← elaborateLedgerFieldValues bindings payload valueFields
        ((recordFieldTypes.lookup destination).getD [])
      let guard ← match initializer with
        | `(nlconstructorinit|
            when $condition:nlexpr insert $_:ident[$_:nlleaves] := $_:nlleaves) => do
          let expression ← checkedCircuitSourceExpression bindings.env
            bindings.nominalUIntBindings condition {type := .bool}
          `(some $expression)
        | `(nlconstructorinit|
            insert $_:ident[$_:nlleaves] := $_:nlleaves) => `(none)
        | _ => throwErrorAt initializer "invalid constructor record-valued Map insert"
      let valueType ← `(Noctium.Types.CompositeType.structure $(stringTerm valueTypeId))
      let value ← `(Noctium.ConstructorRecordKeyMapValue.record $valueType $valueValues)
      let insertion ← `(Noctium.ConstructorRecordKeyMapInsert.mk
        $(stringTerm destination) $keyValues $value $guard)
      orderedActionTerms := orderedActionTerms.push
        (← `(Noctium.ConstructorAction.insertRecordKeyMap $insertion))
      hasOrderedActions := _root_.Bool.true
    | `(nlconstructorinit| insert $stateName:ident[$keyFields:nlleaves] := $value:nlexpr)
    | `(nlconstructorinit|
        when $condition:nlexpr insert $stateName:ident[$keyFields:nlleaves] := $value:nlexpr) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      let some (.tree (.recordMapKey environment recordType valueTy)) := schema.lookup destination
        | throwErrorAt stateName
            "constructor fields insert requires a root scalar-valued record-key Map"
      let fields ← match LedgerValueType.recordMapKeyFields environment recordType with
        | .ok fields => pure fields
        | .error message => throwErrorAt stateName message
      let values ← elaborateRecordMapKeyFields bindings stateName keyFields fields
      let nominal := (bindings.nominalCollections.lookup destination).getD {}
      let value ← checkedSourceValue bindings.env bindings.nominalUIntBindings
        bindings.contractRefBindings value {type := valueTy, nominalUInt := nominal.scalarValue}
      let valueType ← tyTerm valueTy
      let guard ← match initializer with
        | `(nlconstructorinit| when $condition:nlexpr insert $_:ident[$_:nlleaves] := $_:nlexpr) => do
          let expression ← checkedCircuitSourceExpression bindings.env
            bindings.nominalUIntBindings condition {type := .bool}
          `(some $expression)
        | `(nlconstructorinit| insert $_:ident[$_:nlleaves] := $_:nlexpr) => `(none)
        | _ => throwErrorAt initializer "invalid constructor record-key Map insert"
      let recordKeyMapValue ← `(Noctium.ConstructorRecordKeyMapValue.scalar
        $valueType $value)
      let insertion ← `(Noctium.ConstructorRecordKeyMapInsert.mk
        $(stringTerm destination) $values $recordKeyMapValue $guard)
      orderedActionTerms := orderedActionTerms.push
        (← `(Noctium.ConstructorAction.insertRecordKeyMap $insertion))
      hasOrderedActions := _root_.Bool.true
    | `(nlconstructorinit| when $condition:nlexpr insert $stateName:ident[$key:nlexpr] := $value:nlexpr) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      match schema.find? (·.1 == destination) with
      | some (_, .map keyTy valueTy) => do
        let conditionExpression ← checkedCircuitSourceExpression scalarBindings
          nominalUIntBindings condition {type := .bool}
        let nominal := (nominalCollections.lookup destination).getD {}
        let keyExpression ← checkedSourceValue scalarBindings nominalUIntBindings contractRefs key
          {type := keyTy, nominalUInt := nominal.pathKeys.head?.join}
        let valueExpression ← checkedSourceValue scalarBindings nominalUIntBindings contractRefs value
          {type := valueTy, nominalUInt := nominal.scalarValue}
        let key ← `(Noctium.PathKey.mk $(← tyTerm keyTy) $keyExpression)
        let valueType ← tyTerm valueTy
        let orderedInsert ← `(Noctium.ConstructorOrderedMapInsert.mk $(stringTerm destination)
          $key $valueType $valueExpression (some $conditionExpression))
        orderedActionTerms := orderedActionTerms.push
          (← `(Noctium.ConstructorAction.mapInsert $orderedInsert))
        hasOrderedActions := _root_.Bool.true
      | some _ => throwErrorAt stateName "constructor insert requires a Map"
      | none => throwErrorAt stateName s!"constructor inserts into unknown Map '{destination}'"
    | `(nlconstructorinit| initializeMember $stateName from $mapNameStx[$key:nlexpr]) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      let mapName := mapNameStx.getId.toString
      match schema.find? (·.1 == destination), schema.find? (·.1 == mapName) with
      | some (_, .cell .bool), some (_, .map keyTy _) => do
        let nominal := (nominalCollections.lookup mapName).getD {}
        let keyExpression ← checkedSourceValue scalarBindings nominalUIntBindings contractRefs key
          {type := keyTy, nominalUInt := nominal.pathKeys.head?.join}
        let key ← `(Noctium.PathKey.mk $(← tyTerm keyTy) $keyExpression)
        let mapMemberInitializer ← `(Noctium.ConstructorMapMemberInitializer.mk
          $(stringTerm destination) $(stringTerm mapName) $key)
        orderedActionTerms := orderedActionTerms.push
          (← `(Noctium.ConstructorAction.initializeCellFromMapMember $mapMemberInitializer))
        hasOrderedActions := _root_.Bool.true
      | some (_, .cell _), some (_, .map ..) =>
        throwErrorAt stateName "Map membership constructor initialization requires a Bool cell"
      | some _, some _ => throwErrorAt mapNameStx "constructor membership read requires a Map"
      | none, _ => throwErrorAt stateName s!"constructor initializes unknown state '{destination}'"
      | _, none => throwErrorAt mapNameStx s!"constructor reads unknown Map '{mapName}'"
    | `(nlconstructorinit| initializeCounter $stateName:ident from $counterName:ident) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      let counterState := counterName.getId.toString
      unless (nominalUIntCells.lookup destination).isNone do
        throwErrorAt stateName "counter snapshot requires a plain UInt64 Cell"
      match schema.find? (·.1 == destination), schema.find? (·.1 == counterState) with
      | some (_, .cell (.uint maximum)), some (_, .tree .counter) => do
        unless maximum == 2 ^ 64 - 1 do
          throwErrorAt stateName "counter snapshot requires a UInt64 Cell"
        if initializedNames.contains destination then
          throwErrorAt initializer s!"duplicate constructor initializer for '{destination}'"
        initializedNames := destination :: initializedNames
        orderedActionTerms := orderedActionTerms.push
          (← `(Noctium.ConstructorAction.initializeCellFromCounter
            $(stringTerm destination) $(stringTerm counterState)))
        hasOrderedActions := _root_.Bool.true
      | some _, some _ => throwErrorAt stateName "counter snapshot requires a root Counter and a UInt64 Cell"
      | none, _ => throwErrorAt stateName s!"constructor initializes unknown state '{destination}'"
      | _, none => throwErrorAt counterName s!"constructor reads unknown Counter '{counterState}'"
    | `(nlconstructorinit| when $condition:nlexpr pushFront $stateName:ident := $payload:nlleaves)
    | `(nlconstructorinit| pushFront $stateName:ident := $payload:nlleaves) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let action ← elaborateConstructorRecordListPush schema bindings initializer stateName payload
      orderedActionTerms := orderedActionTerms.push
        action
      hasOrderedActions := _root_.Bool.true
    | `(nlconstructorinit| when $_:nlexpr insert $stateName:ident[$payload:nlleaves])
    | `(nlconstructorinit| insert $stateName:ident[$payload:nlleaves]) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      let some (.tree (.recordSet environment type)) := schema.lookup destination
        | throwErrorAt stateName "constructor fields insert requires a root record Set"
      let fields ← match LedgerValueType.recordSetKeyFields environment type with
        | .ok fields => pure fields
        | .error message => throwErrorAt stateName message
      let values ← elaborateLedgerFieldValues bindings payload fields
        ((bindings.recordKeyFieldTypes.lookup destination).getD [])
      let guard ← match initializer with
        | `(nlconstructorinit| when $condition:nlexpr insert $_:ident[$_:nlleaves]) => do
          let conditionExpression ← checkedCircuitSourceExpression scalarBindings
            nominalUIntBindings condition {type := .bool}
          `(some $conditionExpression)
        | _ => `(none)
      orderedActionTerms := orderedActionTerms.push
        (← `(Noctium.ConstructorAction.insertRecordSet $(stringTerm destination) $values $guard))
      hasOrderedActions := _root_.Bool.true
    | `(nlconstructorinit| when $_:nlexpr insert $stateName:ident [ $key:nlexpr ])
    | `(nlconstructorinit| insert $stateName:ident [ $key:nlexpr ]) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      match schema.find? (·.1 == destination) with
      | some (_, .tree (.set keyTy)) => do
        let guard ← match initializer with
          | `(nlconstructorinit| when $condition:nlexpr insert $_:ident [ $_:nlexpr ]) => do
            let conditionExpression ← checkedCircuitSourceExpression scalarBindings
              nominalUIntBindings condition {type := .bool}
            `(some $conditionExpression)
          | `(nlconstructorinit| insert $_:ident [ $_:nlexpr ]) => `(none)
          | _ => throwErrorAt initializer "invalid constructor Set insert"
        let nominal := (nominalCollections.lookup destination).getD {}
        let keyExpression ← checkedSourceValue scalarBindings nominalUIntBindings contractRefs key
          {type := keyTy, nominalUInt := nominal.pathKeys.head?.join,
            nominalField := nominal.pathFieldKeys.head?.join} nominalFieldBindings
        let key ← `(Noctium.PathKey.mk $(← tyTerm keyTy) $keyExpression)
        setInsertTerms := setInsertTerms.push
          (← `(Noctium.ConstructorSetInsert.mk $(stringTerm destination) $key $guard))
      | some _ => throwErrorAt stateName "constructor insert requires a root Set"
      | none => throwErrorAt stateName s!"constructor inserts into unknown Set '{destination}'"
    | `(nlconstructorinit| insert $stateName:ident[$key:nlexpr] := $value:nlexpr) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      match schema.find? (·.1 == destination) with
      | some (_, .map keyTy valueTy) => do
        let nominal := (nominalCollections.lookup destination).getD {}
        let keyExpression ← checkedSourceValue scalarBindings nominalUIntBindings contractRefs key
          {type := keyTy, nominalUInt := nominal.pathKeys.head?.join}
        let valueExpression ← checkedSourceValue scalarBindings nominalUIntBindings contractRefs value
          {type := valueTy, nominalUInt := nominal.scalarValue}
        let key ← `(Noctium.PathKey.mk $(← tyTerm keyTy) $keyExpression)
        let valueType ← tyTerm valueTy
        mapInsertTerms := mapInsertTerms.push
          (← `(Noctium.ConstructorMapInsert.mk $(stringTerm destination) $key $valueType $valueExpression))
        let orderedInsert ← `(Noctium.ConstructorOrderedMapInsert.mk $(stringTerm destination)
          $key $valueType $valueExpression none)
        orderedActionTerms := orderedActionTerms.push
          (← `(Noctium.ConstructorAction.mapInsert $orderedInsert))
      | some _ => throwErrorAt stateName "constructor insert requires a Map"
      | none => throwErrorAt stateName s!"constructor inserts into unknown Map '{destination}'"
    | `(nlconstructorinit| when $_:nlexpr increment $stateName:ident by $amount:nlexpr)
    | `(nlconstructorinit| increment $stateName:ident by $amount:nlexpr) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      let amountExpression ← match amount with
        | `(nlexpr| $literal:num) => do
          let maximum := 2 ^ 32 - 1
          unless literal.getNat ≤ maximum do
            throwErrorAt amount "Counter adjustment exceeds the native u32 immediate"
          `(Noctium.Expr.uint $(natTerm maximum) $(natTerm literal.getNat))
        | _ => do
          let value ← checkedExpression scalarBindings amount (.uint (2 ^ 16 - 1))
          `(Noctium.Expr.cast $(← tyTerm (.uint (2 ^ 32 - 1))) $value)
      let guard ← match initializer with
        | `(nlconstructorinit| when $condition:nlexpr increment $_:ident by $_:nlexpr) => do
          let conditionExpression ← checkedCircuitSourceExpression scalarBindings
            nominalUIntBindings condition {type := .bool}
          `(some $conditionExpression)
        | `(nlconstructorinit| increment $_:ident by $_:nlexpr) => `(none)
        | _ => throwErrorAt initializer "invalid constructor Counter increment"
      match schema.find? (·.1 == destination) with
      | some (_, .tree .counter) => do
        let incrementTerm ← `(Noctium.ConstructorCounterIncrement.mk $(stringTerm destination)
          $amountExpression $guard)
        if hasCounterReads then
          orderedActionTerms := orderedActionTerms.push
            (← `(Noctium.ConstructorAction.counterIncrement $incrementTerm))
          hasOrderedActions := _root_.Bool.true
        else
          counterIncrementTerms := counterIncrementTerms.push incrementTerm
      | some _ => throwErrorAt stateName "constructor increment requires a root Counter"
      | none => throwErrorAt stateName s!"constructor increments unknown Counter '{destination}'"
    | `(nlconstructorinit| when $_:nlexpr pushFront $stateName:ident := $value:nlexpr)
    | `(nlconstructorinit| pushFront $stateName:ident := $value:nlexpr) => do
      if orderedActionTerms.size + counterIncrementTerms.size + listPushTerms.size +
          setInsertTerms.size >= 64 then
        throwErrorAt initializer "constructor collection action limit exceeded"
      let destination := stateName.getId.toString
      let guard ← match initializer with
        | `(nlconstructorinit| when $condition:nlexpr pushFront $_:ident := $_:nlexpr) => do
          let conditionExpression ← checkedCircuitSourceExpression scalarBindings
            nominalUIntBindings condition {type := .bool}
          `(some $conditionExpression)
        | `(nlconstructorinit| pushFront $_:ident := $_:nlexpr) => `(none)
        | _ => throwErrorAt initializer "invalid constructor List pushFront"
      match schema.find? (·.1 == destination) with
      | some (_, .tree (.«list» _ (.scalar valueTy))) => do
        let contractRef := contractRefState.lookup destination
        let nominalUInt := nominalUIntLists.lookup destination
        let valueExpression ← checkedSourceValue scalarBindings nominalUIntBindings contractRefs value
          {type := valueTy, nominalUInt, contractRef}
        listPushTerms := listPushTerms.push
          (← `(Noctium.ConstructorListPush.mk $(stringTerm destination)
            $(← tyTerm valueTy) $valueExpression $guard))
      | some _ => throwErrorAt stateName "constructor pushFront requires a root scalar List"
      | none => throwErrorAt stateName s!"constructor pushes to unknown List '{destination}'"
    | _ => do
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
            let nominalUInt := nominalUIntCells.lookup destination
            let nominalField := nominalFieldCells.lookup destination
            let contractRef := contractRefState.lookup destination
            let expression ← checkedSourceValue scalarBindings nominalUIntBindings contractRefs value
              {type := ty, nominalUInt, nominalField, contractRef} nominalFieldBindings
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
  let mapInserts := if hasOrderedActions then #[] else mapInsertTerms
  let actions := if hasOrderedActions then orderedActionTerms else #[]
  let counterIncrements := counterIncrementTerms
  let listPushes := listPushTerms
  let setInserts := setInsertTerms
  `(some (Noctium.Constructor.mk [$parameters,*] [$initializers,*] [$mapInserts,*]
    [$counterIncrements,*] [$listPushes,*] [$setInserts,*] [$actions,*]))

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
    | `(nlmerklespec| $depth:num of struct $name:ident { $fields:nlmerkleafield* }) => do
      let id := name.getId.toString
      let mut layoutFields : Array Types.Field := #[]
      let mut nestedDeclarations : Array Types.StructDecl := #[]
      let mut leafFields : Array (String × Ty) := #[]
      for field in fields do
        let (layoutField, nested, leaves) ← readMerkleCompositeField id "" field
        layoutFields := layoutFields.push layoutField
        for declaration in nested do
          nestedDeclarations := nestedDeclarations.push declaration
        for leaf in leaves do
          leafFields := leafFields.push leaf
      let flattenedFields := leafFields.toList
      checkMerkleLeafWidth spec (flattenedFields.map Prod.snd)
      let environment : Types.CompositeEnv := {
        structures := {id, fields := layoutFields.toList} :: nestedDeclarations.toList
      }
      match Types.checkedLayout Types.defaultLimits environment (.structure id) with
      | .ok _ => pure (depth.getNat, MerkleLeafType.record flattenedFields)
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

private def nestedRecordSetSchema (keyTy : Ty)
    (environment : Types.CompositeEnv) (recordType : Types.CompositeType)
    (environmentTerm recordTypeTerm : TSyntax `term) (source : TSyntax `nlstate) :
    CommandElabM (LedgerValueType × TSyntax `term) := do
  match keyTy, LedgerValueType.shieldedCoinRecordFields environment recordType with
  | .bytes 32, .ok _ => do
    let keyTerm ← tyTerm keyTy
    let schema := LedgerValueType.map keyTy (.shieldedCoinSet environment recordType)
    let term ← `(Noctium.LedgerValueType.map $keyTerm
      (Noctium.LedgerValueType.shieldedCoinSet $environmentTerm $recordTypeTerm))
    pure (schema, term)
  | _, _ => do
    match LedgerValueType.recordSetKeyFields environment recordType with
    | .error message => throwErrorAt source message
    | .ok _ => pure ()
    let keyTerm ← tyTerm keyTy
    let schema := LedgerValueType.map keyTy (.recordSet environment recordType)
    let term ← `(Noctium.LedgerValueType.map $keyTerm
      (Noctium.LedgerValueType.recordSet $environmentTerm $recordTypeTerm))
    pure (schema, term)

private partial def readMapRecordTail (tail : TSyntax `nlmaprecordtail) :
    CommandElabM (List Ty × _root_.Bool × TSyntax `ident × Array (TSyntax `nlcompositefield)) := do
  match tail with
  | `(nlmaprecordtail| struct $record:ident { $recordFields:nlcompositefield* }) =>
    pure ([], _root_.Bool.false, record, recordFields)
  | `(nlmaprecordtail| $kind:ident struct $record:ident { $recordFields:nlcompositefield* }) => do
    unless kind.getId.toString == "List" do
      throwErrorAt kind "unsupported recursive tree value declaration"
    pure ([], _root_.Bool.true, record, recordFields)
  | `(nlmaprecordtail| $key:nltype => $rest:nlmaprecordtail) => do
    let keyTy ← readTy key
    let (restTypes, asList, record, recordFields) ← readMapRecordTail rest
    pure (keyTy :: restTypes, asList, record, recordFields)
  | _ => throwErrorAt tail "expected a nested Map key or record leaf"

private def readCollectionScalarSourceType (source : TSyntax `nltype)
    (allowNominalField : _root_.Bool := _root_.Bool.false) : CommandElabM CircuitSourceType := do
  let sourceType ← readCircuitSourceType source allowNominalField
  unless sourceType.contractRef.isNone do
    throwErrorAt source "typed contract references are not supported in scalar Maps or Sets"
  pure sourceType

private partial def readMapSetTail (tail : TSyntax `nlmapsettail) :
    CommandElabM (List Ty × TSyntax `ident × Array (TSyntax `nlcompositefield)) := do
  match tail with
  | `(nlmapsettail| Set struct $record:ident { $recordFields:nlcompositefield* }) =>
    pure ([], record, recordFields)
  | `(nlmapsettail| $key:nltype => $rest:nlmapsettail) => do
    let keyTy ← readTy key
    let (restTypes, record, recordFields) ← readMapSetTail rest
    pure (keyTy :: restTypes, record, recordFields)
  | _ => throwErrorAt tail "expected a nested Map key or record Set leaf"

private def checkedRootNativeVectorKeyLayout (length : Nat) (source : TSyntax `nlstate)
    (label : String) :
    CommandElabM (Types.CompositeEnv × Types.CompositeType × TSyntax `term × TSyntax `term) := do
  unless 0 < length && length ≤ Types.defaultLimits.maxVectorLength do
    throwErrorAt source
      s!"root {label} length must be between 1 and {Types.defaultLimits.maxVectorLength}"
  let environment : Types.CompositeEnv := {}
  let compositeType : Types.CompositeType := .vector length (.scalar .native)
  let environmentTerm ← `(({} : Noctium.Types.CompositeEnv))
  let nativeType ← tyTerm .native
  let compositeTypeTerm ← `(Noctium.Types.CompositeType.vector $(natTerm length)
    (Noctium.Types.CompositeType.scalar $nativeType))
  match LedgerValueType.ledgerRecordWriteFields environment compositeType with
  | .error message => throwErrorAt source message
  | .ok fields =>
    unless fields.length == length && fields.all (fun field => field.2 == .native) do
      throwErrorAt source s!"root {label} layout does not match its Native width"
  pure (environment, compositeType, environmentTerm, compositeTypeTerm)

@[command_elab contractCommand] unsafe def elabContract : CommandElab := fun stx => do
  match stx with
  | `(noctium_contract $name:ident where $states:nlstate* $entries:nlentry* end) =>
    let mut stateTerms : Array (TSyntax `term) := #[]
    let mut schema : List (String × StateKind) := []
    let mut nominalUIntCells : List (String × NominalUIntType) := []
    let mut nominalFieldCells : List (String × NominalFieldType) := []
    let mut nominalUIntLists : List (String × NominalUIntType) := []
    let mut nominalCollections : List (String × CollectionNominals) := []
    let mut contractRefState : List (String × Name) := []
    let mut recordFieldTypes : List (String × List (String × CircuitSourceType)) := []
    let mut recordKeyFieldTypes : List (String × List (String × CircuitSourceType)) := []
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
        | `(nlstate| set $id:ident : Vector($length:num, $element:nltype)) => do
          let element ← readCircuitSourceType element
          unless element.type == .native && element.nominalUInt.isNone do
            throwErrorAt state "root Set vectors require Native elements"
          let length := length.getNat
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            checkedRootNativeVectorKeyLayout length state "Set vector"
          let valueSchema := LedgerValueType.recordSet environment compositeType
          let valueTerm ← `(Noctium.LedgerValueType.recordSet $environmentTerm $compositeTypeTerm)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| set $id:ident : struct $record:ident { $recordFields:nlcompositefield* })
        | `(nlstate| sealed set $id:ident : struct $record:ident { $recordFields:nlcompositefield* }) => do
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((environment, compositeType, environmentTerm, compositeTypeTerm), sourceFields) ←
            elaborateTypedLedgerRecord contractName record recordFields state
              _root_.Bool.false _root_.Bool.true
          match LedgerValueType.shieldedCoinRecordFields environment compositeType with
          | .ok _ =>
            if sourceFields.any (fun (_, field) => field.contractRef.isSome) then
              throwErrorAt state "typed contract reference fields are unsupported for this ledger layout"
            if sourceFields.any (fun (_, field) => field.nominalField.isSome) then
              throwErrorAt state "nominal Field record fields are unsupported for this ledger layout"
            if sourceFields.any (fun (_, field) => field.nominalUInt.isSome) then
              throwErrorAt state "nominal UInt record fields are unsupported for this ledger layout"
            let valueSchema := LedgerValueType.shieldedCoinSet environment compositeType
            let valueTerm ← `(Noctium.LedgerValueType.shieldedCoinSet $environmentTerm $compositeTypeTerm)
            pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
          | .error _ => do
            if sourceFields.any (fun (_, field) => field.contractRef.isSome) then
              throwErrorAt state "typed contract reference fields are unsupported for this ledger layout"
            if sourceFields.any (fun (_, field) => field.nominalUInt.isSome) then
              throwErrorAt state "nominal UInt record fields are unsupported for this ledger layout"
            match LedgerValueType.recordSetKeyFields environment compositeType with
            | .ok _ =>
              unless sourceFields.isEmpty do
                recordKeyFieldTypes := (id.getId.toString, sourceFields) :: recordKeyFieldTypes
              let valueSchema := LedgerValueType.recordSet environment compositeType
              let valueTerm ← `(Noctium.LedgerValueType.recordSet $environmentTerm $compositeTypeTerm)
              pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
            | .error message => throwErrorAt state message
        | `(nlstate| tree $id:ident : struct $record:ident { $recordFields:nlcompositefield* } => $valueType:nltype) => do
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((environment, compositeType, environmentTerm, compositeTypeTerm), sourceKeys) ←
            elaborateTypedLedgerRecord contractName record recordFields state
              _root_.Bool.false _root_.Bool.true
          unless sourceKeys.isEmpty do
            recordKeyFieldTypes := (id.getId.toString, sourceKeys) :: recordKeyFieldTypes
          match LedgerValueType.recordMapKeyFields environment compositeType with
          | .error message => throwErrorAt state message
          | .ok _ => pure ()
          let valueSource ← readCircuitSourceType valueType
          let valueTy := valueSource.type
          if let some interface := valueSource.contractRef then
            contractRefState := (id.getId.toString, interface) :: contractRefState
          if valueSource.nominalUInt.isSome then
            nominalCollections := (id.getId.toString, {scalarValue := valueSource.nominalUInt}) ::
              nominalCollections
          let valueSchema := LedgerValueType.recordMapKey environment compositeType valueTy
          let valueTerm ← `(Noctium.LedgerValueType.recordMapKey
            $environmentTerm $compositeTypeTerm $(← tyTerm valueTy))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : struct $keyRecord:ident { $keyFields:nlcompositefield* } =>
            struct $valueRecord:ident { $valueFields:nlcompositefield* }) => do
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((keyEnvironment, keyType, keyEnvironmentTerm, keyTypeTerm), sourceKeys) ←
            elaborateTypedLedgerRecord contractName keyRecord keyFields state
              _root_.Bool.false _root_.Bool.true
          let ((valueEnvironment, valueType, valueEnvironmentTerm, valueTypeTerm), sourceValues) ←
            elaborateTypedLedgerRecord contractName valueRecord valueFields state
              _root_.Bool.false _root_.Bool.true
          unless sourceKeys.isEmpty do
            recordKeyFieldTypes := (id.getId.toString, sourceKeys) :: recordKeyFieldTypes
          unless sourceValues.isEmpty do
            recordFieldTypes := (id.getId.toString, sourceValues) :: recordFieldTypes
          match LedgerValueType.recordMapKeyFields keyEnvironment keyType with
          | .error message => throwErrorAt state message
          | .ok _ => pure ()
          match LedgerValueType.rootMapRecordWriteFields valueEnvironment valueType with
          | .error message => throwErrorAt state message
          | .ok _ => pure ()
          let valueSchema := LedgerValueType.recordMapComposite
            keyEnvironment keyType valueEnvironment valueType
          let valueTerm ← `(Noctium.LedgerValueType.recordMapComposite
            $keyEnvironmentTerm $keyTypeTerm $valueEnvironmentTerm $valueTypeTerm)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| cell $id:ident : struct $record:ident { $recordFields:nlcompositefield* }) => do
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((environment, compositeType, environmentTerm, compositeTypeTerm), fieldTypes) ←
            elaborateTypedLedgerRecord contractName record recordFields state
              _root_.Bool.false _root_.Bool.true
          if !fieldTypes.isEmpty then
            recordFieldTypes := (id.getId.toString, fieldTypes) :: recordFieldTypes
          match LedgerValueType.cellRecordFields environment compositeType with
          | .ok _ => pure ()
          | .error message => throwErrorAt state message
          let valueSchema := LedgerValueType.composite environment compositeType
          let valueTerm ← `(Noctium.LedgerValueType.composite $environmentTerm $compositeTypeTerm)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| sealed cell $id:ident : $ty:nltype) => do
          let sourceType ← readCircuitSourceType ty _root_.Bool.true
          let t := sourceType.type
          if let some nominalUInt := sourceType.nominalUInt then
            nominalUIntCells := nominalUIntCells ++ [(id.getId.toString, nominalUInt)]
          if let some nominalField := sourceType.nominalField then
            nominalFieldCells := (id.getId.toString, nominalField) :: nominalFieldCells
          if let some interface := sourceType.contractRef then
            contractRefState := (id.getId.toString, interface) :: contractRefState
          if t == .opaqueString then
            pure (id, StateKind.opaqueString, ← `(Noctium.StateKind.opaqueString))
          else
            pure (id, StateKind.cell t, ← `(Noctium.StateKind.cell $(← tyTerm t)))
        | `(nlstate| cell $id:ident : $ty:nltype alignedBytes) => do
          let sourceType ← readCircuitSourceType ty
          let t := sourceType.type
          unless t == .uint (2 ^ 128 - 1) do
            throwErrorAt state "alignedBytes is supported only for UInt 128 cells"
          if let some nominalUInt := sourceType.nominalUInt then
            nominalUIntCells := nominalUIntCells ++ [(id.getId.toString, nominalUInt)]
          pure (id, StateKind.cell t, ← `(Noctium.StateKind.cell $(← tyTerm t)))
        | `(nlstate| cell $id:ident : $ty:nltype) => do
          let sourceType ← readCircuitSourceType ty _root_.Bool.true
          let t := sourceType.type
          if let some nominalUInt := sourceType.nominalUInt then
            nominalUIntCells := nominalUIntCells ++ [(id.getId.toString, nominalUInt)]
          if let some nominalField := sourceType.nominalField then
            nominalFieldCells := (id.getId.toString, nominalField) :: nominalFieldCells
          if let some interface := sourceType.contractRef then
            contractRefState := (id.getId.toString, interface) :: contractRefState
          pure (id, StateKind.cell t, ← `(Noctium.StateKind.cell $(← tyTerm t)))
        | `(nlstate| map $id:ident : Vector($length:num, $element:nltype) =>
            struct $record:ident { $recordFields:nlcompositefield* }) => do
          let elementSource ← readCircuitSourceType element
          unless elementSource.type == .native && elementSource.nominalUInt.isNone do
            throwErrorAt state "root Map vector keys require Native elements"
          let length := length.getNat
          let (keyEnvironment, keyType, keyEnvironmentTerm, keyTypeTerm) ←
            checkedRootNativeVectorKeyLayout length state "Map vector key"
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((valueEnvironment, valueType, valueEnvironmentTerm, valueTypeTerm),
              sourceValues) ← elaborateTypedLedgerRecord contractName record recordFields state
                _root_.Bool.false _root_.Bool.true
          unless sourceValues.isEmpty do
            recordFieldTypes := (id.getId.toString, sourceValues) :: recordFieldTypes
          match LedgerValueType.rootMapRecordWriteFields valueEnvironment valueType with
          | .ok _ => pure ()
          | .error message => throwErrorAt state message
          let valueSchema := LedgerValueType.recordMapComposite
            keyEnvironment keyType valueEnvironment valueType
          let valueTerm ← `(Noctium.LedgerValueType.recordMapComposite
            $keyEnvironmentTerm $keyTypeTerm $valueEnvironmentTerm $valueTypeTerm)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| map $id:ident : Vector($length:num, $element:nltype) => $valueType:nltype) => do
          let elementSource ← readCircuitSourceType element
          unless elementSource.type == .native && elementSource.nominalUInt.isNone do
            throwErrorAt state "root Map vector keys require Native elements"
          let length := length.getNat
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            checkedRootNativeVectorKeyLayout length state "Map vector key"
          let valueSource ← readCircuitSourceType valueType
          let valueTy := valueSource.type
          if let some interface := valueSource.contractRef then
            contractRefState := (id.getId.toString, interface) :: contractRefState
          if valueSource.nominalUInt.isSome then
            nominalCollections := (id.getId.toString, {scalarValue := valueSource.nominalUInt}) ::
              nominalCollections
          let valueSchema := LedgerValueType.recordMapKey environment compositeType valueTy
          let valueTerm ← `(Noctium.LedgerValueType.recordMapKey
            $environmentTerm $compositeTypeTerm $(← tyTerm valueTy))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| sealed map $id:ident : $key:nltype => $value:nltype)
        | `(nlstate| map $id:ident : $key:nltype => $value:nltype) => do
          let key ← readCollectionScalarSourceType key
          let value ← readCollectionScalarSourceType value
          let nominal : CollectionNominals := {
            pathKeys := [key.nominalUInt], scalarValue := value.nominalUInt}
          unless nominal.isEmpty do
            nominalCollections := (id.getId.toString, nominal) :: nominalCollections
          pure (id, StateKind.map key.type value.type,
            ← `(Noctium.StateKind.map $(← tyTerm key.type) $(← tyTerm value.type)))
        | `(nlstate| sealed counter $id:ident) =>
          pure (id, StateKind.tree .counter,
            ← `(Noctium.StateKind.tree Noctium.LedgerValueType.counter))
        | `(nlstate| sealed set $id:ident : $element:nltype) => do
          let memberSource ← readCollectionScalarSourceType element _root_.Bool.true
          let nominal : CollectionNominals := {
            pathKeys := [memberSource.nominalUInt]
            pathFieldKeys := [memberSource.nominalField]}
          unless nominal.isEmpty do
            nominalCollections := (id.getId.toString, nominal) :: nominalCollections
          let keyTy := memberSource.type
          pure (id, StateKind.tree (.set keyTy), ← `(Noctium.StateKind.tree
            (Noctium.LedgerValueType.set $(← tyTerm keyTy))))
        | `(nlstate| sealed $listKind:ident $id:ident : $element:nltype) => do
          unless listKind.getId.toString == "list" do
            throwErrorAt listKind "expected a sealed scalar List declaration"
          let sourceType ← readCircuitSourceType element
          if let some nominalUInt := sourceType.nominalUInt then
            nominalUIntLists := nominalUIntLists ++ [(id.getId.toString, nominalUInt)]
          if let some interface := sourceType.contractRef then
            contractRefState := (id.getId.toString, interface) :: contractRefState
          let (kind, term) ← elaborateScalarListDecl [] sourceType.type
          pure (id, kind, term)
        | `(nlstate| set $id:ident : $key:nltype) => do
          let memberSource ← readCollectionScalarSourceType key _root_.Bool.true
          let nominal : CollectionNominals := {
            pathKeys := [memberSource.nominalUInt]
            pathFieldKeys := [memberSource.nominalField]}
          unless nominal.isEmpty do
            nominalCollections := (id.getId.toString, nominal) :: nominalCollections
          let keyTy := memberSource.type
          pure (id, StateKind.tree (.set keyTy), ← `(Noctium.StateKind.tree
            (Noctium.LedgerValueType.set $(← tyTerm keyTy))))
        | `(nlstate| tree $id:ident : $key:nltype => Set $memberType:nltype) => do
          let mapKey ← readCollectionScalarSourceType key
          let memberSource ← readCollectionScalarSourceType memberType
          let nominal : CollectionNominals := {
            pathKeys := [mapKey.nominalUInt, memberSource.nominalUInt]}
          unless nominal.isEmpty do
            nominalCollections := (id.getId.toString, nominal) :: nominalCollections
          let mapKeyTy := mapKey.type
          let memberTy := memberSource.type
          let mapKeyTerm ← tyTerm mapKeyTy
          let memberTerm ← tyTerm memberTy
          let valueSchema := LedgerValueType.map mapKeyTy (.set memberTy)
          let valueTerm ← `(Noctium.LedgerValueType.map $mapKeyTerm
            (Noctium.LedgerValueType.set $memberTerm))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => Set $memberType:nltype) => do
          let outer ← readCollectionScalarSourceType outer
          let inner ← readCollectionScalarSourceType inner
          let memberSource ← readCollectionScalarSourceType memberType
          let nominal : CollectionNominals := {
            pathKeys := [outer.nominalUInt, inner.nominalUInt, memberSource.nominalUInt]}
          unless nominal.isEmpty do
            nominalCollections := (id.getId.toString, nominal) :: nominalCollections
          let outerTy := outer.type
          let innerTy := inner.type
          let memberTy := memberSource.type
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
          let ((environment, compositeType, environmentTerm, compositeTypeTerm), fieldTypes) ←
            elaborateTypedLedgerRecord contractName record recordFields state
              _root_.Bool.false _root_.Bool.true
          if !fieldTypes.isEmpty then
            recordFieldTypes := (id.getId.toString, fieldTypes) :: recordFieldTypes
          let valueSchema := LedgerValueType.map keyTy (.composite environment compositeType)
          let valueTerm ← `(Noctium.LedgerValueType.map $(← tyTerm keyTy)
            (Noctium.LedgerValueType.composite $environmentTerm $compositeTypeTerm))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $key:nltype => $value:nltype) => do
          let keyTy ← readTy key
          let valueTy ← readTy value
          unless keyTy == .bytes 32 && (valueTy == .opaqueBytes || valueTy == .opaqueString) do
            throwErrorAt state "single-key scalar trees currently support only Bytes32 => OpaqueBytes or OpaqueString"
          let valueSchema := LedgerValueType.map keyTy (.scalar valueTy)
          let valueTerm ← `(Noctium.LedgerValueType.map $(← tyTerm keyTy)
            (Noctium.LedgerValueType.scalar $(← tyTerm valueTy)))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => struct $record:ident { $recordFields:nlcompositefield* }) => do
          let outerTy ← readTy outer
          let innerTy ← readTy inner
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((environment, compositeType, environmentTerm, compositeTypeTerm), fieldTypes) ←
            elaborateTypedLedgerRecord contractName record recordFields state
              _root_.Bool.false _root_.Bool.true
          if !fieldTypes.isEmpty then
            recordFieldTypes := (id.getId.toString, fieldTypes) :: recordFieldTypes
          let valueSchema := LedgerValueType.map outerTy
            (.map innerTy (.composite environment compositeType))
          let outerTerm ← tyTerm outerTy
          let innerTerm ← tyTerm innerTy
          let valueTerm ← `(Noctium.LedgerValueType.map $outerTerm
            (Noctium.LedgerValueType.map $innerTerm
              (Noctium.LedgerValueType.composite $environmentTerm $compositeTypeTerm)))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $first:nltype => $second:nltype =>
            $tail:nlmapsettail) => do
          let firstTy ← readTy first
          let secondTy ← readTy second
          let (tailTypes, record, recordFields) ← readMapSetTail tail
          let keyTypes := [firstTy, secondTy] ++ tailTypes
          let some finalKey := keyTypes.getLast?
            | throwErrorAt state "nested record Set requires at least two Map keys"
          let contractName := (← getCurrNamespace) ++ name.getId
          let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
            elaborateNamedRecord contractName record recordFields state
          let (leafSchema, leafTerm) ← nestedRecordSetSchema finalKey environment compositeType
            environmentTerm compositeTypeTerm state
          let parentTypes := keyTypes.dropLast
          let valueSchema := parentTypes.reverse.foldl
            (fun value keyType => LedgerValueType.map keyType value) leafSchema
          let mut valueTerm := leafTerm
          for keyType in parentTypes.reverse do
            let keyTerm ← tyTerm keyType
            valueTerm ← `(Noctium.LedgerValueType.map $keyTerm $valueTerm)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $first:nltype => $second:nltype =>
            $third:nltype => $tail:nlmaprecordtail) => do
          let firstTy ← readTy first
          let secondTy ← readTy second
          let thirdTy ← readTy third
          let (tailTypes, asList, record, recordFields) ← readMapRecordTail tail
          let keyTypes := [firstTy, secondTy, thirdTy] ++ tailTypes
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((environment, compositeType, environmentTerm, compositeTypeTerm), fieldTypes) ←
            elaborateTypedLedgerRecord contractName record recordFields state
              _root_.Bool.false _root_.Bool.true
          if fieldTypes.any (fun (_, field) => field.contractRef.isSome) then
            throwErrorAt state "typed contract reference fields are unsupported for this ledger layout"
          if !fieldTypes.isEmpty then
            recordFieldTypes := (id.getId.toString, fieldTypes) :: recordFieldTypes
          let leafSchema := if asList then LedgerValueType.«list» environment compositeType
            else .composite environment compositeType
          let valueSchema := keyTypes.reverse.foldl
            (fun value keyType => LedgerValueType.map keyType value) leafSchema
          let mut valueTerm ← if asList then
            `(Noctium.LedgerValueType.«list» $environmentTerm $compositeTypeTerm)
          else
            `(Noctium.LedgerValueType.composite $environmentTerm $compositeTypeTerm)
          for keyType in keyTypes.reverse do
            let keyTerm ← tyTerm keyType
            valueTerm ← `(Noctium.LedgerValueType.map $keyTerm $valueTerm)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $outer:nltype => struct $keyRecord:ident
            { $keyFields:nlcompositefield* } => $valueType:nltype) => do
          let outerTy ← readTy outer
          let valueSource ← readCircuitSourceType valueType
          let valueTy := valueSource.type
          if let some interface := valueSource.contractRef then
            contractRefState := (id.getId.toString, interface) :: contractRefState
          if valueSource.nominalUInt.isSome then
            nominalCollections := (id.getId.toString, {scalarValue := valueSource.nominalUInt}) ::
              nominalCollections
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((environment, compositeType, environmentTerm, compositeTypeTerm), sourceKeys) ←
            elaborateTypedLedgerRecord contractName keyRecord keyFields state
          unless sourceKeys.isEmpty do
            recordKeyFieldTypes := (id.getId.toString, sourceKeys) :: recordKeyFieldTypes
          match LedgerValueType.recordMapKeyFieldsAtDepth environment compositeType 1 with
          | .ok _ => pure ()
          | .error message => throwErrorAt state message
          let nestedSchema := LedgerValueType.recordMapKey environment compositeType valueTy
          let valueSchema := LedgerValueType.map outerTy nestedSchema
          let outerTerm ← tyTerm outerTy
          let valueTerm ← tyTerm valueTy
          let treeTerm ← `(Noctium.LedgerValueType.map $outerTerm
            (Noctium.LedgerValueType.recordMapKey
              $environmentTerm $compositeTypeTerm $valueTerm))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $treeTerm))
        | `(nlstate| tree $id:ident : $outer:nltype => struct $keyRecord:ident
            { $keyFields:nlcompositefield* } => struct $valueRecord:ident
            { $valueFields:nlcompositefield* }) => do
          let outerTy ← readTy outer
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((keyEnvironment, keyType, keyEnvironmentTerm, keyTypeTerm), sourceKeys) ←
            elaborateTypedLedgerRecord contractName keyRecord keyFields state
          let ((valueEnvironment, valueType, valueEnvironmentTerm, valueTypeTerm), sourceValues) ←
            elaborateTypedLedgerRecord contractName valueRecord valueFields state
              _root_.Bool.false _root_.Bool.true
          unless sourceKeys.isEmpty do
            recordKeyFieldTypes := (id.getId.toString, sourceKeys) :: recordKeyFieldTypes
          unless sourceValues.isEmpty do
            recordFieldTypes := (id.getId.toString, sourceValues) :: recordFieldTypes
          match LedgerValueType.recordMapKeyFieldsAtDepth keyEnvironment keyType 1 with
          | .ok _ => pure ()
          | .error message => throwErrorAt state message
          match LedgerValueType.ledgerRecordWriteFields valueEnvironment valueType with
          | .ok _ => pure ()
          | .error message => throwErrorAt state message
          let valueSchema := LedgerValueType.map outerTy
            (.recordMapComposite keyEnvironment keyType valueEnvironment valueType)
          let outerTerm ← tyTerm outerTy
          let treeTerm ← `(Noctium.LedgerValueType.map $outerTerm
            (Noctium.LedgerValueType.recordMapComposite
              $keyEnvironmentTerm $keyTypeTerm $valueEnvironmentTerm $valueTypeTerm))
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $treeTerm))
        | `(nlstate| tree $id:ident : $key:nltype => Set struct $record:ident { $recordFields:nlcompositefield* }) => do
          let keyTy ← readTy key
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((environment, compositeType, environmentTerm, compositeTypeTerm), fieldTypes) ←
            elaborateTypedLedgerRecord contractName record recordFields state
              _root_.Bool.false _root_.Bool.true
          if fieldTypes.any (fun (_, field) => field.contractRef.isSome) then
            throwErrorAt state "typed contract reference fields are unsupported for this ledger layout"
          if fieldTypes.any (fun (_, field) => field.nominalUInt.isSome) then
            throwErrorAt state "nominal UInt record fields are unsupported for this ledger layout"
          unless fieldTypes.isEmpty do
            recordKeyFieldTypes := (id.getId.toString, fieldTypes) :: recordKeyFieldTypes
          let (valueSchema, valueTerm) ← nestedRecordSetSchema keyTy environment compositeType
            environmentTerm compositeTypeTerm state
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| $listKind:ident $id:ident : struct $record:ident { $recordFields:nlcompositefield* }) => do
          unless listKind.getId.toString == "list" do
            throwErrorAt listKind "unsupported recursive List state declaration"
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((environment, compositeType, environmentTerm, compositeTypeTerm), fieldTypes) ←
            elaborateTypedLedgerRecord contractName record recordFields state
              _root_.Bool.true _root_.Bool.true
          match LedgerValueType.listElementFields environment compositeType with
          | .ok _ => pure ()
          | .error message => throwErrorAt state message
          if !fieldTypes.isEmpty then
            recordFieldTypes := (id.getId.toString, fieldTypes) :: recordFieldTypes
          let valueSchema := LedgerValueType.«list» environment compositeType
          let valueTerm ← `(Noctium.LedgerValueType.«list» $environmentTerm $compositeTypeTerm)
          pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
        | `(nlstate| tree $id:ident : $key:nltype => $listKind:ident struct $record:ident { $recordFields:nlcompositefield* }) => do
          let keyTy ← readTy key
          let contractName := (← getCurrNamespace) ++ name.getId
          if listKind.getId.toString == "List" then
            let ((environment, compositeType, environmentTerm, compositeTypeTerm), fieldTypes) ←
              elaborateTypedLedgerRecord contractName record recordFields state
                _root_.Bool.false _root_.Bool.true
            match LedgerValueType.listElementFields environment compositeType with
            | .ok _ => pure ()
            | .error message => throwErrorAt state message
            if !fieldTypes.isEmpty then
              recordFieldTypes := (id.getId.toString, fieldTypes) :: recordFieldTypes
            let valueSchema := LedgerValueType.map keyTy (.«list» environment compositeType)
            let valueTerm ← `(Noctium.LedgerValueType.map $(← tyTerm keyTy)
              (Noctium.LedgerValueType.«list» $environmentTerm $compositeTypeTerm))
            pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
          else if listKind.getId.toString == "Set" then
            let (environment, compositeType, environmentTerm, compositeTypeTerm) ←
              elaborateNamedRecord contractName record recordFields state
            let (valueSchema, valueTerm) ← nestedRecordSetSchema keyTy environment compositeType
              environmentTerm compositeTypeTerm state
            pure (id, StateKind.tree valueSchema, ← `(Noctium.StateKind.tree $valueTerm))
          else
            throwErrorAt listKind "unsupported recursive tree value declaration"
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => $listKind:ident struct $record:ident { $recordFields:nlcompositefield* }) => do
          unless listKind.getId.toString == "List" do
            throwErrorAt listKind "unsupported recursive tree value declaration"
          let outerTy ← readTy outer
          let innerTy ← readTy inner
          let contractName := (← getCurrNamespace) ++ name.getId
          let ((environment, compositeType, environmentTerm, compositeTypeTerm), fieldTypes) ←
            elaborateTypedLedgerRecord contractName record recordFields state
              _root_.Bool.false _root_.Bool.true
          match LedgerValueType.listElementFields environment compositeType with
          | .ok _ => pure ()
          | .error message => throwErrorAt state message
          if !fieldTypes.isEmpty then
            recordFieldTypes := (id.getId.toString, fieldTypes) :: recordFieldTypes
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
          let sourceType ← readCircuitSourceType element
          if let some nominalUInt := sourceType.nominalUInt then
            nominalUIntLists := nominalUIntLists ++ [(id.getId.toString, nominalUInt)]
          if let some interface := sourceType.contractRef then
            contractRefState := (id.getId.toString, interface) :: contractRefState
          let (kind, term) ← elaborateScalarListDecl [] sourceType.type
          pure (id, kind, term)
        | `(nlstate| tree $id:ident : $key:nltype => $listKind:ident $element:nltype) => do
          unless listKind.getId.toString == "List" do
            throwErrorAt listKind "expected a List value in the recursive tree"
          let sourceType ← readCircuitSourceType element
          unless sourceType.contractRef.isNone do
            throwErrorAt element "typed contract reference Lists require root storage"
          if let some nominalUInt := sourceType.nominalUInt then
            nominalUIntLists := nominalUIntLists ++ [(id.getId.toString, nominalUInt)]
          let (kind, term) ← elaborateScalarListDecl [key] sourceType.type
          pure (id, kind, term)
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => $listKind:ident $element:nltype) => do
          unless listKind.getId.toString == "List" do
            throwErrorAt listKind "expected a List value in the recursive tree"
          let sourceType ← readCircuitSourceType element
          unless sourceType.contractRef.isNone do
            throwErrorAt element "typed contract reference Lists require root storage"
          if let some nominalUInt := sourceType.nominalUInt then
            nominalUIntLists := nominalUIntLists ++ [(id.getId.toString, nominalUInt)]
          let (kind, term) ← elaborateScalarListDecl [outer, inner] sourceType.type
          pure (id, kind, term)
        | `(nlstate| tree $id:ident : $outer:nltype => $inner:nltype => $value:nltype) => do
          let outer ← readCollectionScalarSourceType outer
          let inner ← readCollectionScalarSourceType inner
          let value ← readCollectionScalarSourceType value
          let nominal : CollectionNominals := {
            pathKeys := [outer.nominalUInt, inner.nominalUInt],
            scalarValue := value.nominalUInt}
          unless nominal.isEmpty do
            nominalCollections := (id.getId.toString, nominal) :: nominalCollections
          let outerTy := outer.type
          let innerTy := inner.type
          let valueTy := value.type
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
      let isSealed : _root_.Bool := match state with
        | `(nlstate| sealed cell $_:ident : $_:nltype)
        | `(nlstate| sealed map $_:ident : $_:nltype => $_:nltype)
        | `(nlstate| sealed counter $_:ident)
        | `(nlstate| sealed set $_:ident : $_:nltype)
        | `(nlstate| sealed set $_:ident : struct $_:ident { $_:nlcompositefield* }) => Bool.true
        | `(nlstate| sealed $listKind:ident $_:ident : $_:nltype) =>
            listKind.getId.toString == "list"
        | _ => Bool.false
      let cellAlignment? : Option CellAlignment := match state with
        | `(nlstate| cell $_:ident : $_:nltype alignedBytes) => some .u128
        | _ => none
      concreteSchema := concreteSchema ++
        [StateDecl.mk id.getId.toString kind isSealed {} cellAlignment?]
      let sealedTerm ← if isSealed then `(Bool.true) else `(Bool.false)
      let cellAlignmentTerm ← match cellAlignment? with
        | some .u128 => `(some Noctium.CellAlignment.u128)
        | none => `(none)
      stateTerms := stateTerms.push (← `(Noctium.StateDecl.mk $(stringTerm id.getId.toString)
        $term $sealedTerm $(← spanTerm state) $cellAlignmentTerm))
    let constructorTerm ← match constructorSyntax? with
      | none => `(none)
      | some ctor =>
        elaborateConstructor ctor schema nominalUIntCells nominalFieldCells nominalUIntLists nominalCollections
          contractRefState recordFieldTypes recordKeyFieldTypes
    let mut entryTerms : Array (TSyntax `term) := #[]
    let mut entryNames : List Name := []
    let mut interfaceSourceRefs : List CallInterfaceSourceRefs := []
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
        unless info.stateNominalFieldCells.isEmpty do
          throwErrorAt circuit "use 'entry from' to bind a structured nominal Field Cell circuit to its contract"
        unless info.stateNominalUIntCells.isEmpty && info.stateNominalUIntMaps.isEmpty do
          throwErrorAt circuit "use 'entry from' to bind a structured nominal UInt circuit to its contract"
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
        let initial : EntryEffects := {
          env := env
          nominalUIntBindings := circuitNominalEnvironment info
          nominalFieldBindings :=
            (info.nominalFieldInputs.map fun (field, nominalField) => (field, some nominalField)) ++
            (info.nominalFieldOutputs.map fun (field, nominalField) => (field, some nominalField))
          nominalUIntCells := nominalUIntCells
          nominalFieldCells := nominalFieldCells
          nominalUIntLists := nominalUIntLists
          nominalCollections := nominalCollections
          contractRefBindings := info.contractRefBindings
          contractRefState := contractRefState
          recordFieldTypes := recordFieldTypes
          recordKeyFieldTypes := recordKeyFieldTypes
          merkleLeafTypes := merkleLeafTypes
          usedLocalNames := reserved
          nominalBytes32Bindings := info.nominalBytes32Outputs
        }
        let lowered ← elaborateStatements schema none 0 statements initial
        let lowered ← elaborateReturns ((← getCurrNamespace) ++ name.getId).toString returns info lowered
          _root_.Bool.true
        interfaceSourceRefs := interfaceSourceRefs ++ [{
          contract := (← getCurrNamespace) ++ name.getId
          operation := id.getId.toString
          argumentContractRefs := info.contractRefBindings
          resultContractRefs := lowered.returnContractRefs
          argumentNominalUInts := info.nominalUIntInputs
          resultNominalUInts := lowered.returnNominalUInts
          argumentNominalFields := info.nominalFieldInputs
          resultNominalFields := lowered.returnNominalFields
        }]
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
        unless info.stateNominalFieldCells.isEmpty do
          throwErrorAt circuit "use 'entry from' to bind a structured nominal Field Cell circuit to its contract"
        unless info.stateNominalUIntCells.isEmpty && info.stateNominalUIntMaps.isEmpty do
          throwErrorAt circuit "use 'entry from' to bind a structured nominal UInt circuit to its contract"
        let env ← addReferences [] (info.inputs ++ info.outputs)
        let env ← addLogicalReferences env info.logicalOutputs
        let reserved := statements.toList.flatMap (fun statement => syntaxIdentifiers statement.raw) ++
          returns.toList.flatMap (fun statement => syntaxIdentifiers statement.raw)
        let initial : EntryEffects := {
          env := env
          nominalUIntBindings := circuitNominalEnvironment info
          nominalFieldBindings :=
            (info.nominalFieldInputs.map fun (field, nominalField) => (field, some nominalField)) ++
            (info.nominalFieldOutputs.map fun (field, nominalField) => (field, some nominalField))
          nominalUIntCells := nominalUIntCells
          nominalFieldCells := nominalFieldCells
          nominalUIntLists := nominalUIntLists
          nominalCollections := nominalCollections
          contractRefBindings := info.contractRefBindings
          contractRefState := contractRefState
          recordFieldTypes := recordFieldTypes
          recordKeyFieldTypes := recordKeyFieldTypes
          merkleLeafTypes := merkleLeafTypes
          usedLocalNames := reserved
          nominalBytes32Bindings := info.nominalBytes32Outputs
        }
        let lowered ← elaborateStatements schema none 0 statements initial
        let lowered ← elaborateReturns ((← getCurrNamespace) ++ name.getId).toString returns info lowered
          _root_.Bool.true
        interfaceSourceRefs := interfaceSourceRefs ++ [{
          contract := (← getCurrNamespace) ++ name.getId
          operation := id.getId.toString
          argumentContractRefs := info.contractRefBindings
          resultContractRefs := lowered.returnContractRefs
          argumentNominalUInts := info.nominalUIntInputs
          resultNominalUInts := lowered.returnNominalUInts
          argumentNominalFields := info.nominalFieldInputs
          resultNominalFields := lowered.returnNominalFields
        }]
        let circuitTerm := mkIdent info.declName
        entryTerms := entryTerms.push (← `({ name := $(stringTerm id.getId.toString), circuit := $circuitTerm, effects := [$lowered.terms,*], returns := [$lowered.returns,*], returnViews := [$lowered.returnViews,*], span := $(← spanTerm entryStx), effectSpans := [$lowered.spans,*], effectGuards := [$lowered.guards,*] : Noctium.Entrypoint }))
      | `(nlentry| entry $id:ident from $source:ident entry $exportName:str end) =>
        if entryNames.contains id.getId then throwErrorAt id "duplicate Noctium entrypoint"
        entryNames := id.getId :: entryNames
        let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
        let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
        let entryNominalUIntMaps := directNominalUIntMaps schema nominalCollections
        let entryNominalFieldCells := nominalFieldCells.map fun (storage, field) => (storage, field.name)
        let program := Helpers.Program.withNominalFieldState
          (program.withNominalUIntState nominalUIntCells entryNominalUIntMaps)
          entryNominalFieldCells
        let value ← match Witness.compileStateEntrypoint program exportName.getString concreteSchema with
          | .ok value => pure value
          | .error diagnostic => failDisclosure diagnostic *> throwError "structured ledger compilation failed"
        for effect in value.effects do
          match effect with
          | .readCell storage _ _ | .writeCell storage _ _ =>
            if (contractRefState.lookup storage).isSome then
              throwErrorAt entryStx "structured helpers do not support typed contract reference cells"
          | .readPath storage .. | .memberPath storage .. | .mapIsEmpty storage .. |
              .mapSize storage .. | .insertPath storage .. | .writePath storage .. |
              .emptyMapPath storage .. | .setInsert storage .. | .removePath storage .. =>
            if (nominalCollections.lookup storage).isSome then
              throwErrorAt entryStx "structured helpers do not support nominal UInt collection paths"
          | _ => pure ()
        let localCircuitName := name.getId ++ id.getId ++ `circuit
        let fullCircuitName := (← getCurrNamespace) ++ localCircuitName
        let circuitId := mkIdent localCircuitName
        let circuitName := stringTerm fullCircuitName.toString
        let sourceTerm := mkIdent sourceName
        let quoteNominal (nominal : NominalUIntType) : CommandElabM (TSyntax `term) :=
          `(({name := $(stringTerm nominal.name), maximum := $(natTerm nominal.maximum)}
            : Noctium.NominalUIntType))
        let quoteOptionalNominal (nominal : Option NominalUIntType) :
            CommandElabM (TSyntax `term) :=
          match nominal with
          | none => `(none)
          | some label => do `(some $(← quoteNominal label))
        let nominalUIntCellTerms ← nominalUIntCells.toArray.mapM fun (storage, nominal) => do
          `(($(stringTerm storage), $(← quoteNominal nominal)))
        let nominalUIntMapTerms ← entryNominalUIntMaps.toArray.mapM fun (storage, nominalMap) => do
          let key ← quoteOptionalNominal nominalMap.key
          let value ← quoteOptionalNominal nominalMap.value
          `(($(stringTerm storage), ({key := $key, value := $value} : Noctium.NominalUIntMap)))
        let nominalFieldCellTerms ← entryNominalFieldCells.toArray.mapM fun (storage, nominal) => do
          `(($(stringTerm storage), $(stringTerm nominal)))
        let taggedProgram ← `(Noctium.Helpers.Program.withNominalFieldState
          (Noctium.Helpers.Program.withNominalUIntState $sourceTerm
            [$nominalUIntCellTerms,*] [$nominalUIntMapTerms,*])
          [$nominalFieldCellTerms,*])
        elabCommand (← `(def $circuitId : Noctium.Circuit :=
          match Noctium.Witness.compileStateEntrypoint $taggedProgram $exportName [$stateTerms,*] with
          | .ok compiledEntry => {compiledEntry.circuit with name := $circuitName}
          | .error _ => {name := $circuitName}))
        unsafe checkGeneratedCircuit fullCircuitName
        modifyEnv fun env => circuitRegistry.addEntry env {
          declName := fullCircuitName
          inputs := value.circuit.inputs.map fun input => (input.name, input.ty)
          publicInputs := (value.circuit.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty)
          outputs := []
          stateProgram? := some (sourceName, exportName.getString)
          stateNominalUIntCells := nominalUIntCells
          stateNominalFieldCells := nominalFieldCells
          stateNominalUIntMaps := entryNominalUIntMaps}
        let circuitTerm := mkIdent fullCircuitName
        entryTerms := entryTerms.push (← `(
          match Noctium.Witness.compileStateEntrypoint $taggedProgram $exportName [$stateTerms,*] with
          | .ok compiledEntry => {compiledEntry with name := $(stringTerm id.getId.toString), circuit := $circuitTerm}
          | .error _ => {name := $(stringTerm id.getId.toString), circuit := $circuitTerm}))
      | _ => throwErrorAt entryStx "unsupported Noctium entrypoint"
    let span ← spanTerm stx
    let fullName := (← getCurrNamespace) ++ name.getId
    elabCommand (← `(def $name : Noctium.Contract := Noctium.Contract.mk
      $(stringTerm fullName.toString) [$stateTerms,*] $constructorTerm [$entryTerms,*] $span))
    unsafe checkGeneratedContract fullName interfaceSourceRefs
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
      let (argumentFields, argumentContractRefs, argumentNominalUInts, argumentViews) ←
        elaborateInterfaceValues arguments
      let (resultFields, resultContractRefs, resultNominalUInts, resultViews) ←
        elaborateInterfaceValues results
      let argumentCount := (argumentFields.map (Ty.nativeCallFieldCount ∘ Prod.snd)).sum
      let resultCount := (resultFields.map (Ty.nativeCallFieldCount ∘ Prod.snd)).sum
      unless argumentCount ≤ 256 && resultCount ≤ maxEntrypointReturnFields do
        throwErrorAt methodDecl "contract interface ABI exceeds 256 fields"
      methods := methods.push {
        contract := interfaceName
        operation := operationName
        argumentFields
        argumentContractRefs
        argumentNominalUInts
        argumentViews
        resultFields
        resultContractRefs
        resultNominalUInts
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
scoped syntax (name := genericWitnessCircuitCommand) "noctium_witness_circuit" ident
  "from" "generic(" ident ")" "entry" str : command

/-- Share checked registration between generated authoring programs and explicit IR sources. -/
unsafe def registerWitnessCircuit (name : Syntax) (sourceName : Name) (exportName : String)
    (outputName : String := "") (observationArtifact? : Option String := none)
    (describeOutputs : Helpers.Program → Witness.Compiled →
      CommandElabM (List (String × Ty × Name) × List (String × Name × List String) ×
        List (String × NominalBytes32) × List (String × NominalUIntType)) :=
      fun _ _ => pure ([], [], [], []))
    (specializationArtifact? : Option String := none)
    (useCheckedCircuitValue : _root_.Bool := _root_.Bool.false)
    (nominalUIntInputs : List (String × NominalUIntType) := []) : CommandElabM Unit := do
    let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
    let fullName := (← getCurrNamespace) ++ name.getId
    let compiled ← match Witness.compile program exportName fullName.toString outputName with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "typed witness compilation failed"
    let (logicalOutputs, aggregateOutputs, nominalBytes32Outputs, nominalUIntOutputs) ←
      describeOutputs program compiled
    let sourceTerm := mkIdent sourceName
    let fullNameTerm := stringTerm fullName.toString
    let exportNameTerm := stringTerm exportName
    let outputNameTerm := stringTerm outputName
    let name : TSyntax `ident := ⟨name⟩
    if useCheckedCircuitValue then do
      let circuitValue := Authoring.QuoteCircuit.circuitValueExpr compiled.circuit
      let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) circuitValue + 1)
      liftCoreM <| Lean.addAndCompile <| Declaration.defnDecl {
        name := fullName
        levelParams := []
        type := Authoring.QuoteCircuit.circuitTypeExpr
        value := circuitValue
        hints
        safety := .safe
      }
      Lean.Elab.addDeclarationRangesFromSyntax fullName name.raw
    else do
      let circuitDefinition ← `(def $name : Noctium.Circuit :=
        match Noctium.Witness.compile $sourceTerm $exportNameTerm $fullNameTerm $outputNameTerm with
        | .ok value => value.circuit
        | .error _ => {name := $fullNameTerm, inputs := [], outputs := [], constraints := []})
      elabCommand circuitDefinition
    match Disclosure.circuit compiled.circuit with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let some exported := program.exports.find? (·.name == exportName)
      | throwErrorAt name "unknown witness entrypoint"
    let aggregateInputs ← (exported.compositeInputs.filter (·.visibility == .private)).mapM fun input => do
      let checked ← match Types.checkedLayout {} program.composites input.type input.span with
        | .ok checked => pure checked
        | .error diagnostic => throwError diagnostic.message
      let fields := (Helpers.sourceLeafPaths checked.value input.name).zip
        (Helpers.callViewLeafTypes checked.value)
      pure (CallInputView.mk input.name fields)
    modifyEnv fun env => circuitRegistry.addEntry env {
      declName := fullName,
      inputs := compiled.circuit.inputs.map fun input => (input.name, input.ty),
      publicInputs := (compiled.circuit.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty),
      outputs := compiled.circuit.outputs.map fun value => (value.name, value.ty),
      nominalUIntInputs,
      nominalUIntOutputs,
      logicalOutputs,
      nominalBytes32Outputs,
      aggregateOutputs,
      witnessCallArguments? := some (exported.inputs.map (·.name)),
      aggregateInputs,
      sourceProgram? := some (sourceName, exportName),
      specializationArtifact?}
    modifyEnv fun env => witnessRegistry.addEntry env {
      circuitName := fullName, sourceName, exportName, outputName, observationArtifact?}
    modifyEnv fun env => checkedWitnesses.modifyState env (·.insert fullName compiled)

@[command_elab witnessCircuitCommand] unsafe def elabWitnessCircuit : CommandElab := fun stx => do
  match stx with
  | `(noctium_witness_circuit $name:ident from $source:ident entry $exportName:str) =>
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    registerWitnessCircuit name sourceName exportName.getString
  | _ => throwUnsupportedSyntax

@[command_elab genericWitnessCircuitCommand] unsafe def elabGenericWitnessCircuit :
    CommandElab := fun stx => do
  match stx with
  | `(noctium_witness_circuit $name:ident from generic($source:ident) entry $exportName:str) => do
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    let sourceProgram ← evalConstCheck Helpers.Specialization.Program
      ``Helpers.Specialization.Program sourceName
    let specialized ← match Helpers.Specialization.specialize sourceProgram exportName.getString with
      | .ok value => pure value
      | .error diagnostic => throwErrorAt source diagnostic.message
    let fullName := (← getCurrNamespace) ++ name.getId.eraseMacroScopes
    let programName := fullName ++ `specializedProgram
    if (← getEnv).contains programName then
      throwErrorAt name "generated specialized program name collides with an existing declaration"
    let programIdent := mkIdent (name.getId.eraseMacroScopes ++ `specializedProgram)
    let sourceIdent := mkIdent sourceName
    let envBefore ← getEnv
    try
      elabCommand (← `(def $programIdent : Noctium.Helpers.Program :=
        match Noctium.Helpers.Specialization.specialize $sourceIdent $exportName with
        | .ok result => result.program
        | .error _ => {}))
      registerWitnessCircuit name programName specialized.exportName
        (specializationArtifact? := some (Lean.toJson specialized.signatureArtifact).pretty)
    catch error =>
      modifyEnv fun _ => envBefore
      throw error
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
  let plan ← match expansion.contractPlan expansion.root request.constructorInputs with
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
  let contract ← match specialized.plan.assembleContract buildInfo.contractName.toString circuitValues with
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

scoped syntax (name := moduleTypeCommand) "noctium_module_type" ident "from" ident
  "with" str "," str : command

@[command_elab moduleTypeCommand] unsafe def elabModuleType : CommandElab := fun stx => do
  match stx with
  | `(noctium_module_type $binding:ident from $requestSource:ident with $viewName:str, $memberName:str) => do
    let aliasName := (← getCurrNamespace) ++ binding.getId.eraseMacroScopes
    let types := noctiumNominalUIntTypeRegistry.getState (← getEnv)
    if (← getEnv).contains aliasName || types.any (·.1 == aliasName.toString) then
      throwErrorAt binding s!"duplicate imported type name '{aliasName}'"
    let requestName ← liftCoreM <| resolveGlobalConstNoOverload requestSource
    let request ← evalConstCheck Modules.Request ``Modules.Request requestName
    let registry ← moduleRegistryForBuild
    let info ← match Modules.importedType registry request viewName.getString memberName.getString with
      | .ok info => pure info
      | .error diagnostic => failDisclosure diagnostic *> throwError "module type import failed"
    let registryTerm ← moduleRegistryTerm
    let requestTerm := mkIdent requestName
    elabCommand (← `(def $binding : Noctium.Modules.TypeInfo :=
      match Noctium.Modules.importedType $registryTerm $requestTerm $viewName $memberName with
      | .ok info => info
      | .error _ => default))
    if let some nominalUInt := info.nominalUInt? then
      modifyEnv fun env =>
        noctiumNominalUIntTypeRegistry.addEntry env (aliasName.toString, nominalUInt)
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
