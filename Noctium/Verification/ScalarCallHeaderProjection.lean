import Noctium.Backend.NativeProducer
import Noctium.Verification.NativeRelationJson
import Noctium.Verification.ScalarValidationProjection

namespace Noctium.Verification.ScalarCallHeaderProjection

open Lean
open Noctium.Backend.Native
open Noctium.Verification.NativeRelationJson
open Noctium.Verification.ScalarValidationProjection

private theorem bind_ok {α β : Type} {value : Except String α}
    {next : α → Except String β} {result : β} :
    (value >>= next) = .ok result ↔
      ∃ found, value = .ok found ∧ next found = .ok result := by
  cases value <;> simp [Bind.bind, Except.bind]

private theorem decodeScalarCallArgument_name {input : Json} {name : String}
    (accepted : decodeScalarCallArgument input = .ok name) :
    NativeRelationJson.stringField input "name" = .ok name := by
  unfold decodeScalarCallArgument at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, _, _, _, parsedName, nameParsed, _, _, result⟩
  have nameEq : parsedName = name := by
    simpa only [Pure.pure, Except.pure, Except.ok.injEq] using result
  cases nameEq
  exact nameParsed

private theorem decodeScalarCallArguments_names {items : List Json} {names : List String}
    (accepted : items.mapM decodeScalarCallArgument = .ok names) :
    ∃ rawNames,
      items.mapM (fun item => NativeRelationJson.stringField item "name") = .ok rawNames ∧
      names = rawNames := by
  induction items generalizing names with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    subst names
    exact ⟨[], rfl, rfl⟩
  | cons head tail ih =>
    simp only [List.mapM_cons, bind_ok] at accepted
    rcases accepted with ⟨headName, headAccepted, tailNames, tailAccepted, result⟩
    cases result
    obtain ⟨tailRawNames, tailNamesAccepted, tailNamesEq⟩ := ih tailAccepted
    refine ⟨headName :: tailRawNames, ?_, ?_⟩
    · simp only [List.mapM_cons, decodeScalarCallArgument_name headAccepted,
        tailNamesAccepted, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    · simp [tailNamesEq]

private theorem decodeScalarCallHeader_names {json : Json}
    {inputs : Array Json} {arguments : List String}
    (accepted : decodeScalarCallHeader json = .ok (inputs, arguments)) :
    ∃ names,
      NativeRelationJson.arrayField json "inputs" = .ok inputs ∧
      inputs.toList.mapM (fun input => NativeRelationJson.stringField input "name") =
        .ok names ∧ arguments = names := by
  unfold decodeScalarCallHeader at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨parsedInputs, inputsParsed, parsedArguments, argumentsParsed,
    uniqueNames, result⟩
  rcases result with ⟨_, pairAccepted⟩
  have resultEq : (parsedInputs, parsedArguments) = (inputs, arguments) :=
    Except.ok.inj (by simpa only [Pure.pure, Except.pure] using pairAccepted)
  cases resultEq
  obtain ⟨names, namesParsed, namesEq⟩ := decodeScalarCallArguments_names argumentsParsed
  exact ⟨names, inputsParsed, namesParsed, namesEq⟩

/-- The scalar call decoder preserves the ordered input names carried in its
JSON header. -/
theorem decodeScalarCall_header_names {json : Json} {call : ScalarCall}
    (accepted : decodeScalarCall json = .ok call) :
    ∃ rawInputs names,
      Backend.Native.arrayField json "inputs" = .ok rawInputs ∧
      rawInputs.toList.mapM (fun input => Backend.Native.stringField input "name") =
        .ok names ∧
      call.arguments = names := by
  unfold decodeScalarCall at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨fields, fieldsParsed, header, headerParsed, body, bodyParsed, result⟩
  have callEq : ({arguments := header.2, body} : ScalarCall) = call := Except.ok.inj result
  cases callEq
  obtain ⟨names, inputsParsed, namesParsed, namesEq⟩ := decodeScalarCallHeader_names headerParsed
  refine ⟨header.1, names, ?_, ?_, namesEq⟩
  · simpa only [NativeRelationJson.arrayField, Backend.Native.arrayField] using inputsParsed
  · simpa only [NativeRelationJson.stringField, Backend.Native.stringField] using namesParsed

/-- Successful native validation and scalar-call decoding agree on the exact
ordered raw caller input names. -/
theorem validate_decodeScalarCall_header_names {expected : Expected} {json : Json}
    {call : ScalarCall} (validated : Backend.Native.validate expected json = .ok ())
    (decoded : decodeScalarCall json = .ok call) :
    call.arguments = expected.rawInputs.map (·.identifier) := by
  obtain ⟨_, rawInputs, seed, _, driver⟩ := validate_driver_result validated
  obtain ⟨headerInputs, names, inputsParsed, namesParsed, argumentsEq⟩ :=
    decodeScalarCall_header_names decoded
  have sameHeaders : headerInputs = rawInputs :=
    Except.ok.inj (inputsParsed.symm.trans driver.rawInputsParsed)
  subst headerInputs
  have seededNames := Backend.Native.seedRawInputs_header_names
    driver.seededRawInputs driver.rawInputCount
  have relationNames : rawInputs.toList.mapM
      (fun input => NativeRelationJson.stringField input "name") =
        .ok (expected.rawInputs.map (·.identifier)) := by
    simpa only [NativeRelationJson.stringField, Backend.Native.stringField] using seededNames
  have sameNames := Except.ok.inj (namesParsed.symm.trans relationNames)
  exact argumentsEq.trans sameNames

end Noctium.Verification.ScalarCallHeaderProjection
