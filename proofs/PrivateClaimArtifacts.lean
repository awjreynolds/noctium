import proofs.PrivateClaimNativePrivacy
import Noctium.Verification.ArtifactCertificate

namespace Noctium.PrivateClaimArtifacts
open Verification Verification.ArtifactBytes Verification.ArtifactCertificate
open PrivateClaimLowering PrivateClaimNativeState PrivateClaimNativePrivacy

/-- The actual four public artifact byte streams pass independent translation
validation and match an external, independently authenticated build authority. -/
structure Certified (authority : Authority) (build : BuildIdentity) (sourceIdentity : String)
    (standaloneBytes planBytes callBytes profileBytes : _root_.Noctium.Verification.ArtifactBytes.«Bytes») : Prop where
  standalone : decodeProgram standaloneBytes = .ok program
  plan : decodePlan planBytes = .ok symbolicPlan
  call : decodeProgram callBytes = .ok callProgram
  profile : decodeProfile profileBytes = .ok selectedProfile
  standaloneIdentity : standaloneBytes = authority.standaloneBytes
  profileIdentity : profileBytes = authority.build.profileBytes
  buildIdentity : Authenticated authority build sourceIdentity planBytes callBytes

theorem exact_byte_build_binding (authority : Authority) (build : BuildIdentity) (sourceIdentity : String)
    (standaloneBytes planBytes callBytes profileBytes : _root_.Noctium.Verification.ArtifactBytes.«Bytes»)
    (certificate : Certified authority build sourceIdentity standaloneBytes planBytes callBytes profileBytes) :
    NativePrivacy.ExactArtifactBinding _root_.Noctium.Verification.ArtifactBytes.«Bytes» BuildIdentity
      sourceIdentity planBytes callBytes (_root_.Noctium.Verification.ArtifactBytes.«tree» planBytes)
      (_root_.Noctium.Verification.ArtifactBytes.«tree» callBytes) build parse (Authenticated authority) :=
  exact_binding authority build sourceIdentity planBytes callBytes ⟨_, certificate.plan⟩ ⟨_, certificate.call⟩
    certificate.buildIdentity

/-- Concrete byte parsing composes with the actual source/native privacy theorem.
Build identity is an external-authority equality checked by the trusted data
process, not a verdict supplied by the untrusted candidate manifest. -/
theorem concrete_privacy (authority : Authority) (build : BuildIdentity) (sourceIdentity : String)
    (standaloneBytes planBytes callBytes profileBytes : _root_.Noctium.Verification.ArtifactBytes.«Bytes»)
    (certificate : Certified authority build sourceIdentity standaloneBytes planBytes callBytes profileBytes) :
    DecodedPrivacyObligation (_root_.Noctium.Verification.ArtifactBytes.«tree» planBytes)
      (_root_.Noctium.Verification.ArtifactBytes.«tree» callBytes) :=
  decoded_obligation _ _ (validated_tree _ _ _ certificate.plan).2 (validated_tree _ _ _ certificate.call).2

/-- Exact-byte target preservation for arbitrary native assignments/traces.
Source success is derived through the previously checked scalar/state chain. -/
def FunctionalPreservation (planTree callTree : Lean.Json) : Prop :=
  ∀ (ctx : EvalContext) (hash : NativeRelation.Hash) (agreement : NativeRelation.HashAgreement ctx hash)
    (input : Inputs) (sr sc presence : NativeRelation.Scalar) (w : NativeRelation.Assignment)
    (root campaign : NativeRelation.Scalar) (entries : List (NativeRelation.Scalar × _root_.Bool))
    (publicGroups : List (List NativeRelation.Scalar)) (after : NativeState.Machine),
    DecodedExecution planTree callTree hash (callStreams input sr sc presence)
      w root campaign entries publicGroups after →
    PrivateClaimProofs.claimEntry.run ctx (PrivateClaimProofs.inputEnvironment input.source)
      (PrivateClaimProofs.state root.val campaign.val (sourceValues entries)) =
      .ok ([("nullifier", .native input.nullifier.val)],
        PrivateClaimProofs.state input.root.val input.campaign.val (sourceValues (mark input.nullifier entries))) ∧
    after.stack = (NativeState.initial input.root input.campaign (encodedEntries (mark input.nullifier entries))).stack

theorem concrete_preservation (authority : Authority) (build : BuildIdentity) (sourceIdentity : String)
    (standaloneBytes planBytes callBytes profileBytes : _root_.Noctium.Verification.ArtifactBytes.«Bytes»)
    (certificate : Certified authority build sourceIdentity standaloneBytes planBytes callBytes profileBytes) :
    FunctionalPreservation (_root_.Noctium.Verification.ArtifactBytes.«tree» planBytes)
      (_root_.Noctium.Verification.ArtifactBytes.«tree» callBytes) :=
  decoded_execution_sound _ _ (validated_tree _ _ _ certificate.plan).2 (validated_tree _ _ _ certificate.call).2

def EligibleCompleteness (planTree callTree : Lean.Json) : Prop :=
  ∀ (ctx : EvalContext) (hash : NativeRelation.Hash) (agreement : NativeRelation.HashAgreement ctx hash)
    (input : PrivateClaimProofs.InputValues) (canonical : PrivateClaimProofs.CanonicalInputs ctx input)
    (leaf node : Nat) (hashes : PrivateClaimProofs.HashTrace ctx input leaf node)
    (entries : List (NativeRelation.Scalar × _root_.Bool)),
    (PrivateClaimProofs.typedEntries (sourceValues entries)).lookup (.native input.nullifier) = none →
    let native := Inputs.ofSource ctx input canonical agreement.modulus
    ∃ assignment after, DecodedExecution planTree callTree hash (callStreams native native.root native.campaign NativeRelation.zero)
      assignment native.root native.campaign entries (NativeState.groups (operations assignment)) after

theorem concrete_complete (authority : Authority) (build : BuildIdentity) (sourceIdentity : String)
    (standaloneBytes planBytes callBytes profileBytes : _root_.Noctium.Verification.ArtifactBytes.«Bytes»)
    (certificate : Certified authority build sourceIdentity standaloneBytes planBytes callBytes profileBytes) :
    EligibleCompleteness (_root_.Noctium.Verification.ArtifactBytes.«tree» planBytes)
      (_root_.Noctium.Verification.ArtifactBytes.«tree» callBytes) :=
  decoded_execution_complete _ _ (validated_tree _ _ _ certificate.plan).2 (validated_tree _ _ _ certificate.call).2

theorem concrete_functional (authority : Authority) (build : BuildIdentity) (sourceIdentity : String)
    (standaloneBytes planBytes callBytes profileBytes : _root_.Noctium.Verification.ArtifactBytes.«Bytes»)
    (certificate : Certified authority build sourceIdentity standaloneBytes planBytes callBytes profileBytes) :
    decodeProgram standaloneBytes = .ok program ∧ decodePlan planBytes = .ok symbolicPlan ∧
      decodeProgram callBytes = .ok callProgram ∧ decodeProfile profileBytes = .ok selectedProfile :=
  ⟨certificate.standalone, certificate.plan, certificate.call, certificate.profile⟩

#print axioms concrete_complete
#print axioms concrete_preservation
#print axioms concrete_privacy
#print axioms exact_byte_build_binding
end Noctium.PrivateClaimArtifacts
