import Noctium.Verification.GuardedImpactTranscript
import Noctium.Verification.GuardedPlanExecution
import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.GuardedActiveObservation

open Backend NativeRelation ScalarNormalization
open GuardedImpactObservation GuardedImpactTranscript GuardedPlanExecution

private theorem mapM_of_map_eq_some {α β : Type} (f : α → Option β)
    {items : List α} {values : List β}
    (matched : items.map f = values.map some) : items.mapM f = some values := by
  induction items generalizing values with
  | nil => cases values <;> simp_all
  | cons item rest ih =>
    cases values with
    | nil => simp at matched
    | cons value restValues =>
      simp only [List.map_cons, List.cons.injEq] at matched
      simp [List.mapM_cons, matched.1, ih matched.2]

private theorem mapM_nested_of_meaning {α β : Type} (f : α → Option β)
    {groups : List (List α)} {values : List (List β)}
    (matched : groups.map (fun group => group.map f) =
      values.map (List.map some)) :
    groups.mapM (fun group => group.mapM f) = some values := by
  induction groups generalizing values with
  | nil => cases values <;> simp_all
  | cons group rest ih =>
    cases values with
    | nil => simp at matched
    | cons fields restValues =>
      simp only [List.map_cons, List.cons.injEq] at matched
      have groupEvaluated := mapM_of_map_eq_some f matched.1
      have restEvaluated := ih matched.2
      simp [List.mapM_cons, groupEvaluated, restEvaluated]

private theorem mapM_option_frame {α β : Type} (f : α → Option β)
    {items : List α} {results : List β} (evaluated : items.mapM f = some results) :
    results.length = items.length ∧
      ∀ index : Nat, results[index]? = (items[index]?.bind f) := by
  induction items generalizing results with
  | nil => cases evaluated; exact ⟨rfl, fun _ => rfl⟩
  | cons item rest ih =>
    simp only [List.mapM_cons, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
      Option.some.injEq] at evaluated
    obtain ⟨head, first, tail, next, exactList⟩ := evaluated
    cases exactList
    obtain ⟨length, indexed⟩ := ih next
    refine ⟨by simp [length], ?_⟩
    intro index
    cases index with
    | zero => simpa using first.symm
    | succ index => exact indexed index

private def nativeObservation (activity : Option Bool) (payload : List Scalar) : Observation :=
  { active := activity.getD true
    payload := if activity.getD true then payload else List.replicate payload.length zero }

private theorem expectedObservationAt_native (hash : Hash) (witness : Assignment)
    (expected : Backend.Native.Expected) (activities : List (Option Bool))
    (groups : List (List Scalar))
    (groupMeaning : expected.groups.mapM (fun group => group.mapM (interpret hash witness)) =
      some groups)
    (guardMeaning : expected.groupGuards.map (interpret hash witness) =
      activities.map (fun activity => some (bit (activity.getD true))))
    (groupsAligned : expected.groups.length = groups.length)
    (guardsAligned : expected.groupGuards.length = activities.length)
    (activitiesAligned : activities.length = groups.length)
    {index : Nat} (inside : index < expected.groups.length) :
    expectedObservationAt hash witness expected index =
      some (nativeObservation activities[index] groups[index]) := by
  have groupFrame := mapM_option_frame (fun group : List Backend.Native.Term =>
    group.mapM (interpret hash witness)) groupMeaning
  have groupInside : index < groups.length := by omega
  have groupValues : expected.groups[index].mapM (interpret hash witness) = some groups[index] := by
    have selected := (groupFrame.2 index).symm
    simpa only [List.getElem?_eq_getElem inside, List.getElem?_eq_getElem groupInside,
      Option.bind_some, Option.some.injEq] using selected
  have guardInside : index < expected.groupGuards.length := by omega
  have activityInside : index < activities.length := by omega
  have selectedGuard : interpret hash witness expected.groupGuards[index] =
      some (bit (activities[index].getD true)) := by
    have selected := congrArg (fun values : List (Option Scalar) => values[index]?) guardMeaning
    simpa only [List.getElem?_map, List.getElem?_eq_getElem guardInside,
      List.getElem?_eq_getElem activityInside, Option.map_some,
      Option.some.injEq] using selected
  have scheduleNonempty : expected.groupGuards.isEmpty = false := by
    cases h : expected.groupGuards with
    | nil => simp [h] at guardInside
    | cons head tail => simp
  have selectedSourceGuard :
      ScalarValidationOutputMeaning.sourceImpactGuard expected {groupCount := index} =
        some expected.groupGuards[index] := by
    simp [ScalarValidationOutputMeaning.sourceImpactGuard, scheduleNonempty,
      List.getElem?_eq_getElem guardInside]
  simp only [expectedObservationAt, selectedSourceGuard,
    List.getElem?_eq_getElem inside, Bind.bind, Option.bind_some]
  rw [GuardedImpactObservation.sourceObservation, selectedGuard, groupValues]
  cases active : activities[index].getD true <;>
    simp [nativeObservation, active, NativeRelation.bit,
      GuardedImpactObservation.observeImpact, NativeRelation.zero_ne_one]

private theorem active_groups_of_observations
    {native : List NativeState.Op} {activities : List (Option Bool)}
    {observations : List Observation}
    (aligned : activities.length = native.length)
    (rows : observations = List.zipWith nativeObservation activities (NativeState.groups native)) :
    NativeState.groups (GuardedPlanExecution.activeOperations native activities) =
      (observations.filter (·.active)).map (·.payload) := by
  induction native generalizing activities observations with
  | nil =>
    cases activities with
    | nil =>
      have rowsNil : observations = [] := by simpa [NativeState.groups] using rows
      subst observations
      simp [GuardedPlanExecution.activeOperations, NativeState.groups]
    | cons activity rest => simp at aligned
  | cons operation rest ih =>
    cases activities with
    | nil => simp at aligned
    | cons activity restActivities =>
      have tailAligned : restActivities.length = rest.length := by simp at aligned; omega
      have rows' : observations =
          nativeObservation activity operation.fields ::
            List.zipWith nativeObservation restActivities (NativeState.groups rest) := by
        simpa [NativeState.groups] using rows
      subst observations
      have activeHead : GuardedPlanExecution.activeOperations
          (operation :: rest) (activity :: restActivities) =
          (if activity.getD true then [operation] else []) ++
            GuardedPlanExecution.activeOperations rest restActivities := by
        change List.filterMap (fun item =>
          if item.2.getD true then some item.1 else none)
            ((operation :: rest).zip (activity :: restActivities)) = _
        rw [List.zip_cons_cons, List.filterMap_cons]
        cases selected : activity.getD true <;>
          simp [GuardedPlanExecution.activeOperations]
      rw [activeHead]
      have tailEq := ih (activities := restActivities)
        (observations := List.zipWith nativeObservation restActivities (NativeState.groups rest))
        tailAligned rfl
      simp only [NativeState.groups] at tailEq
      cases active : activity.getD true <;>
        simp [NativeState.groups, active, nativeObservation, tailEq]

/-- Project the checked guarded observations to the exact ordered payloads
kept by the native active-operation filter. Inactive rows preserve their
ordinal and width, but contribute no native group. -/
theorem expected_active_groups (hash : Hash) (witness : Assignment)
    (expected : Backend.Native.Expected) (observations : List Observation)
    (native : List NativeState.Op) (activities : List (Option Bool))
    (guardMeaning : expected.groupGuards.map (interpret hash witness) =
      activities.map (fun activity => some (bit (activity.getD true))))
    (groupsMeaning : expected.groups.map (List.map (interpret hash witness)) =
      (NativeState.groups native).map (List.map some))
    (aligned : native.length = activities.length)
    (observed : GuardedImpactTranscript.expectedObservations hash witness expected =
      some observations) :
    NativeState.groups (GuardedPlanExecution.activeOperations native activities) =
      (observations.filter (·.active)).map (·.payload) := by
  have nativeGroupsLength : (NativeState.groups native).length = native.length := by
    simp [NativeState.groups]
  have groupsAligned : expected.groups.length = (NativeState.groups native).length := by
    have lengths := congrArg List.length groupsMeaning
    simpa [NativeState.groups] using lengths
  have guardsAligned : expected.groupGuards.length = activities.length := by
    have lengths := congrArg List.length guardMeaning
    simpa using lengths
  have activitiesAligned : activities.length = (NativeState.groups native).length := by
    rw [nativeGroupsLength]
    exact aligned.symm
  have groupMeaning := mapM_nested_of_meaning (interpret hash witness) groupsMeaning
  have ⟨observationsLength, observationsAt⟩ := mapM_option_frame
    (expectedObservationAt hash witness expected) observed
  have observationsAligned : observations.length = expected.groups.length := by
    simpa [GuardedImpactTranscript.expectedObservations] using observationsLength
  have expectedRows : observations =
      List.zipWith nativeObservation activities (NativeState.groups native) := by
    apply List.ext_getElem?
    intro index
    by_cases inside : index < expected.groups.length
    · have activityInside : index < activities.length := by omega
      have nativeInside : index < (NativeState.groups native).length := by omega
      have observationInside : index < observations.length := by omega
      have atIndex := observationsAt index
      change observations[index]? =
        (List.range expected.groups.length)[index]?.bind
          (expectedObservationAt hash witness expected) at atIndex
      rw [List.getElem?_range inside] at atIndex
      simp only [Option.bind_some] at atIndex
      rw [expectedObservationAt_native hash witness expected activities
        (NativeState.groups native) groupMeaning guardMeaning groupsAligned guardsAligned
        activitiesAligned inside] at atIndex
      have zippedAt :
          (List.zipWith nativeObservation activities (NativeState.groups native))[index]? =
            some (nativeObservation activities[index] (NativeState.groups native)[index]) := by
        simp [List.getElem?_zipWith, List.getElem?_eq_getElem activityInside,
          List.getElem?_eq_getElem nativeInside]
      simpa [List.getElem?_eq_getElem observationInside, zippedAt] using atIndex
    · have observationsOutside : observations.length ≤ index := by
        rw [observationsAligned]
        omega
      have activitiesOutside : activities.length ≤ index := by
        rw [activitiesAligned, ← groupsAligned]
        omega
      have nativeOutside : (NativeState.groups native).length ≤ index := by
        rw [← groupsAligned]
        omega
      simp [List.getElem?_eq_none observationsOutside, List.getElem?_zipWith,
        List.getElem?_eq_none activitiesOutside, List.getElem?_eq_none nativeOutside]
  exact active_groups_of_observations aligned.symm expectedRows

end Noctium.Verification.GuardedActiveObservation
