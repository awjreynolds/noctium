import Noctium.Verification.GuardedInputTranscript
import Noctium.Verification.GuardedZkirArtifact
import Noctium.Verification.ScalarGuardedReadAdmission
import Noctium.Verification.ScalarLedgerScalarSchema
import Noctium.Verification.ScalarRawArgumentPrivacy
import Noctium.Verification.GenericStateWriteEvaluation

namespace Noctium.Verification.GuardedSourceReadTranscript

open Lean Backend Backend.Native NativeRelation ScalarNormalization
open GenericStateCircuitParts GuardedInputTranscript GuardedScalarInput
open GenericStateInputValues (scalarType?)
open ScalarGuardedPlanAdmission (ScalarEffect)

/-- Unguarded public circuit inputs in declaration order, before the state
reads. Private body inputs and raw call arguments do not contribute a slot. -/
def publicCircuitObservations (inputs : List Noctium.Input) (assignment : Assignment) :
    List ReadObservation :=
  inputs.filterMap fun input => if input.visibility == .«public» then
    some ⟨one, assignment ("%input_" ++ input.name)⟩ else none

private theorem initialInputSlots (hash : Hash) (assignment : Assignment)
    (inputs : List Noctium.Input)
    (scalar : ∀ input ∈ inputs, Nonempty (ScalarType input.ty)) :
    ((inputs.flatMap Native.Input.requirements).mapM (requirementObservation hash assignment assignment)) =
      some (inputs.map fun input => if input.visibility == .«public» then
        some ⟨one, assignment ("%input_" ++ input.name)⟩ else none) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    obtain ⟨supported⟩ := scalar input (by simp)
    have requirement : Native.Input.requirements input =
        [{identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}] := by
      cases input with
      | mk name ty visibility span => cases supported <;> rfl
    have remaining := ih (fun next present => scalar next (List.mem_cons_of_mem _ present))
    cases visibility : input.visibility <;>
      simp [List.flatMap_cons, requirement, List.mapM_cons, remaining,
        requirementObservation, GuardedPublicInputMeaning.sourceReadGuard, visibility]

private theorem publicFilter_without_callInputs (entry : Entrypoint)
    (privateArgs : ∀ input ∈ entry.circuit.inputs,
      input.name ∈ entry.callInputs → input.visibility = .private) :
    (entry.circuit.inputs.filter (fun input => !entry.callInputs.contains input.name)).filter
        (·.visibility == .«public») =
      entry.circuit.inputs.filter (·.visibility == .«public») := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro input present
  cases visibility : input.visibility with
  | «private» => simp
  | «public» =>
    have notRaw : input.name ∉ entry.callInputs := by
      intro named
      have privateVisibility := privateArgs input present named
      rw [visibility] at privateVisibility
      cases privateVisibility
    simp [notRaw]

private theorem publicCircuitObservations_filter (inputs : List Noctium.Input)
    (assignment : Assignment) :
    publicCircuitObservations inputs assignment =
      (inputs.filter (·.visibility == .«public»)).map
        (fun input => ⟨one, assignment ("%input_" ++ input.name)⟩) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    cases visibility : input.visibility <;>
      simp [publicCircuitObservations, visibility, ← ih]

private theorem initialObservations (hash : Hash) (assignment : Assignment) (entry : Entrypoint)
    (scalar : ∀ input ∈ entry.circuit.inputs, Nonempty (ScalarType input.ty))
    (privateArgs : ∀ input ∈ entry.circuit.inputs,
      input.name ∈ entry.callInputs → input.visibility = .private) :
    ∃ slots,
      (sourceInitialInputRequirements entry).mapM (requirementObservation hash assignment assignment) =
        some slots ∧ slots.filterMap id = publicCircuitObservations entry.circuit.inputs assignment := by
  let body := entry.circuit.inputs.filter fun input => !entry.callInputs.contains input.name
  have observed := initialInputSlots hash assignment body
    (fun input present => scalar input ((List.mem_filter.mp present).1))
  refine ⟨_, observed, ?_⟩
  rw [List.filterMap_map]
  change publicCircuitObservations body assignment = _
  simp only [publicCircuitObservations_filter, body, publicFilter_without_callInputs entry privateArgs]

/-- The checked artifact's public read order comes from unguarded public
circuit declarations, then the accepted state read descriptors with their
normalized guards. Raw call arguments stay private and separate. -/
theorem lower_checked_guarded_source_read_transcript
    (state : List StateDecl) (sourceEntry : Entrypoint) (rewrites : Zkir.Rewrites)
    (expected : Native.Expected) (plan : Impact.Plan)
    (hash : Hash) (values : EvalEnv) (assignment : Assignment)
    (bytes : ArtifactBytes.Bytes) (json : Json) (rows : List GuardedScalarRows.Row)
    (emitted : Zkir.lowerEntrypoint state sourceEntry rewrites = .ok json)
    (artifact : GuardedZkirArtifact.check bytes json = .ok rows)
    (ordinary : ∀ row ∈ rows, GuardedImpactTranscript.ordinaryHolds hash assignment row)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint sourceEntry) = .ok plan)
    (expectedAccepted :
      Native.expectedEntrypoint state (Passes.pruneEntrypoint sourceEntry) = .ok expected)
    (inputs : CanonicalInputs sourceEntry.circuit values assignment)
    (effects : ∀ effect ∈ sourceEntry.effects, ScalarEffect state effect) :
    let entry := Passes.pruneEntrypoint sourceEntry
    let reads := plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs)
    (GuardedZkirArtifact.decodeBytes bytes).map GuardedZkirArtifact.View.rows = .ok rows ∧
    expected.rawInputs = entry.callArguments.flatMap Native.Input.callArgumentRequirements ∧
    (∀ requirement ∈ expected.rawInputs, requirement.visibility = .private) ∧
    ∃ (frame : OutputFrame) (aliases : Native.AliasEnvironment)
        (blocks : List (List Native.InputRequirement)) (observations : List ReadObservation),
      normalizeOutputs (entrypointSeedAliases entry plan) entry.circuit.outputs = .ok frame ∧
      forIn (reads.flatMap Impact.Read.scalarReads) frame.1 (readAliasStep entry) = .ok aliases ∧
      reads.mapM (guardedReadRequirements aliases) = .ok blocks ∧
      expected.inputs = sourceInitialInputRequirements entry ++ blocks.flatten ∧
      ((blocks.flatten.mapM (requirementObservation hash assignment assignment)).map (List.filterMap id)) =
        some observations ∧
      emittedPublicReads assignment rows =
        publicCircuitObservations entry.circuit.inputs assignment ++ observations := by
  let entry := Passes.pruneEntrypoint sourceEntry
  have inputScope : ∀ input ∈ entry.circuit.inputs, Nonempty (ScalarType input.ty) := by
    intro input present
    obtain ⟨_, _, canonical⟩ := inputs.complete input present
    exact GenericStateWriteEvaluation.scalarType_of_canonical canonical
  obtain ⟨plainReads, _, _⟩ := ScalarGuardedReadAdmission.lower_read_admission
    state entry plan planAccepted effects
  have readScope : ∀ readSpec ∈ plan.reads.drop (Impact.publicInputReadCount entry.circuit.inputs),
      ∀ name ty, (name, ty) ∈ readSpec.bindings → Nonempty (ScalarType ty) := by
    intro readSpec present name ty binding
    obtain ⟨plain, supported, _⟩ := plainReads readSpec present
    rw [GenericStateCheckedReadDecode.supported_plain_read_bindings readSpec plain supported] at binding
    have same : ty = readSpec.ty := congrArg Prod.snd (List.mem_singleton.mp binding)
    subst ty
    cases scalar : scalarType? readSpec.ty with
    | none => simp [scalar] at supported
    | some support => exact ⟨support⟩
  have schema := ScalarLedgerScalarSchema.accepted_nonforeign_input_schema
    state entry plan expected planAccepted expectedAccepted inputScope readScope
  have schemaFromExpected (other : Native.Expected)
      (accepted : Native.expectedEntrypoint state entry = .ok other) :
      ∀ requirement ∈ other.rawInputs ++ other.inputs, requirement.ty.isForeign = _root_.Bool.false := by
    have same := Except.ok.inj (accepted.symm.trans expectedAccepted)
    subst other
    exact schema
  obtain ⟨exactRows, instructions, parsed, decoded⟩ := GuardedZkirArtifact.check_sound artifact
  obtain ⟨_, checkedExpected, _, accepted, transcript⟩ :=
    lowerEntrypoint_guardedInputTranscript rewrites emitted parsed decoded schemaFromExpected
  have sameExpected := Except.ok.inj (accepted.symm.trans expectedAccepted)
  subst checkedExpected
  have observed := (transcript (hash := hash) (witness := assignment) ordinary).1
  obtain ⟨frame, aliases, blocks, frameAccepted, aliasesAccepted, blocksAccepted, inputOrder⟩ :=
    expectedEntrypoint_guardedInputRequirements state entry expected plan expectedAccepted planAccepted
  have privateArgs := ScalarRawArgumentPrivacy.lower_callInputs_private state entry plan planAccepted
  have rawExact := expectedEntrypoint_rawInputs state entry expected expectedAccepted
  have rawPrivate : ∀ requirement ∈ expected.rawInputs, requirement.visibility = .private := by
    intro requirement present
    rw [rawExact] at present
    obtain ⟨input, argument, within⟩ := List.mem_flatMap.mp present
    unfold Entrypoint.callArguments at argument
    obtain ⟨name, named, found⟩ := List.mem_filterMap.mp argument
    have declared := List.mem_of_find?_eq_some found
    have inputName : input.name = name :=
      beq_iff_eq.mp (List.find?_some (p := fun argument : Noctium.Input => argument.name == name) found)
    have privacy := privateArgs input declared (inputName.symm ▸ named)
    obtain ⟨supported⟩ := inputScope input declared
    have requirementShape : Native.Input.callArgumentRequirements input =
        [{identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}] := by
      cases input with
      | mk name ty visibility span => cases supported <;> rfl
    rw [requirementShape] at within
    obtain rfl := List.mem_singleton.mp within
    exact privacy
  obtain ⟨slots, initial, circuitOrder⟩ := initialObservations hash assignment entry inputScope privateArgs
  rw [expectedPublicReads_eq_requirements, inputOrder, List.mapM_append, initial] at observed
  cases suffix : blocks.flatten.mapM (requirementObservation hash assignment assignment) with
  | none => simp [suffix, Bind.bind, Option.bind] at observed
  | some effectSlots =>
    have exactOrder : emittedPublicReads assignment rows = slots.filterMap id ++ effectSlots.filterMap id := by
      simpa [suffix, Bind.bind, Option.bind, List.filterMap_append] using observed.symm
    exact ⟨exactRows, rawExact, rawPrivate, frame, aliases, blocks, effectSlots.filterMap id,
      frameAccepted, aliasesAccepted, blocksAccepted, inputOrder, by simp [suffix],
      exactOrder.trans (by rw [circuitOrder])⟩

end Noctium.Verification.GuardedSourceReadTranscript
