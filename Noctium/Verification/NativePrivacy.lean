import Noctium.Verification
import Noctium.Verification.NativeState

namespace Noctium.Verification.NativePrivacy
open NativeRelation NativeState

inductive ObserverIdentity where
  | successfulClaimPublicTranscriptV1
  deriving Repr, DecidableEq

inductive ExcludedObservable where
  | rejectedOutcomes
  | termination
  | timingAndResources
  | proofBytes
  | hostProviderAccess
  | hostLogs
  deriving Repr, DecidableEq

/-- Native privacy carries a separate identity and scope. A source functional
proof supplies neither this policy nor its observer proof. -/
structure Policy where
  source : AuditPolicy
  observer : ObserverIdentity
  scope : ObservationScope
  excluded : List ExcludedObservable

/-- Host coins and parent context are coupled public environment inputs. The
native theorem gives no license to select them from a private witness. -/
structure HostContext where
  parentPublicContext : List Scalar
  communicationRandomness : Scalar
  deriving DecidableEq

/-- These are observations of existing index/member/insert operations, not
invented source events or an extension to the supported source language. -/
inductive Query where
  | index (slot : Nat) (savedPath : _root_.Bool)
  | member (key : Cell)
  | insert (levels : Nat) (key : Cell)
  deriving Repr, DecidableEq

def queries : List Op → List Query
  | [] => []
  | .index slot saved :: rest => .index slot saved :: queries rest
  | .push key _ :: .member :: rest =>
    .member key :: queries (.member :: rest)
  | .push key _ :: .push value valueStorage :: .insert levels :: rest =>
    .insert levels key :: queries (.push value valueStorage :: .insert levels :: rest)
  | _ :: rest => queries rest

/-- The binding view contains only the observed public call and shared parent
context. Native serialization and the real binding function remain explicit
implementation obligations, rather than an assumed compiler theorem. -/
structure BindingView where
  parentPublicContext : List Scalar
  publicValues : List Scalar
  returnValues : List Scalar
  beforeState : List Node
  afterState : List Node
  reads : List Cell
  publicReadValues : List Scalar
  operations : List Op
  opcodeGroups : List (List Scalar)
  activity : List _root_.Bool
  communicationCommitment : Scalar
  deriving DecidableEq

abbrev BindingFunction := BindingView → Scalar

structure Observation where
  call : BindingView
  queryPaths : List Query
  bindingInput : Scalar
  deriving DecidableEq

/-- This is equality under a shared parent context, not a claim about a
cryptographic binding hash's injectivity or hiding. -/
theorem binding_view_congruence (binding : BindingFunction) (left right : BindingView)
    (same : left = right) : binding left = binding right := congrArg binding same

/-- Reserved composition obligations for the exact-artifact package. These
are proof parameters. No inhabitant or byte/build authentication is supplied. -/
structure ExactArtifactBinding (byteType : Type) (Build : Type) (sourceIdentity : String)
    (planBytes callBytes : byteType) (planTree callTree : Lean.Json) (build : Build)
    (parse : byteType → Except String Lean.Json)
    (authenticates : Build → String → byteType → byteType → Prop) : Prop where
  planParsed : parse planBytes = .ok planTree
  callParsed : parse callBytes = .ok callTree
  authenticatedBuild : authenticates build sourceIdentity planBytes callBytes

/-- A named external assumption when a caller later includes proof bytes in
its observer. The current model proves no proof-system zero knowledge. -/
structure ProofByteZeroKnowledge (PublicStatement Witness ProofBytes : Type)
    (valid : PublicStatement → Witness → Prop)
    (proofDistribution : PublicStatement → Witness → ProofBytes → Prop)
    (sameDistribution : (ProofBytes → Prop) → (ProofBytes → Prop) → Prop) : Prop where
  indistinguishable : ∀ publicStatement left right,
    valid publicStatement left → valid publicStatement right →
    sameDistribution (proofDistribution publicStatement left) (proofDistribution publicStatement right)

end Noctium.Verification.NativePrivacy
