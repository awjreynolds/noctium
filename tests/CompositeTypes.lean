import Noctium.Types.Composite

open Noctium
open Noctium.Types

private def point : SourceSpan := {file := "composite-fixture.lean", line := 7, column := 4}

private def nestedEnvironment : CompositeEnv := {
  structures := [
    {id := "Fixture.Inner", span := point, fields := [
      {name := "enabled", type := .scalar .bool, span := point},
      {name := "amount", type := .scalar (.uint 255), span := point}
    ]},
    {id := "Fixture.Outer", span := point, fields := [
      {name := "header", type := .scalar .native, span := point},
      {name := "inner", type := .structure "Fixture.Inner", span := point},
      {name := "samples", type := .vector 2 (.scalar (.uint 7)), span := point},
      {name := "memo", type := .bytes 3, span := point}
    ]}
  ]
}

private def layoutResult (environment : CompositeEnv) (type : CompositeType)
    (limits : Limits := defaultLimits) : Option Layout :=
  match layout limits environment type with
  | .ok result => some result
  | .error _ => none

private def errorResult (environment : CompositeEnv) (type : CompositeType)
    (limits : Limits := defaultLimits) : Option LayoutDiagnostic :=
  match layout limits environment type with
  | .ok _ => none
  | .error error => some error

private def isError {α : Type} (result : Except LayoutDiagnostic α) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

private def errorSpan (result : Except LayoutDiagnostic α) : Option SourceSpan :=
  match result with
  | .ok _ => none
  | .error error => some error.span

private def checkedIsOk (result : Except LayoutDiagnostic (CheckedLayout limits)) : Bool :=
  match result with
  | .error _ => false
  | .ok _ => true

private def checkedSummary (limits : Limits) (environment : CompositeEnv)
    (type : CompositeType) : Option (Nat × Nat × Nat × Nat) :=
  match checkedLayout limits environment type with
  | .error _ => none
  | .ok checked => some (checked.expandedNodes, checked.layoutNodes,
      checked.value.expandedNodeCount, checked.value.nodeCount)

-- TYC-ORDER: declaration insertion order is irrelevant, field order remains meaningful.
private def reorderedEnvironment : CompositeEnv := {
  structures := nestedEnvironment.structures.reverse
}

#guard nestedEnvironment.fingerprint == reorderedEnvironment.fingerprint
#guard ((layoutResult nestedEnvironment (.structure "Fixture.Outer")).map Layout.leafCount == some 8)
#guard ((layoutResult nestedEnvironment (.vector 4 (.scalar .native))).map Layout.leafCount == some 4)
#guard ((layoutResult nestedEnvironment (.bytes 16)).map Layout.leafCount == some 16)
#guard ((layoutResult nestedEnvironment (.bytes 32)).map Layout.leafCount == some 32)
#guard isError (layout defaultLimits nestedEnvironment (.scalar (.bytes 32)))
#guard ((layoutResult nestedEnvironment .unit).map Layout.leafCount == some 0)
#guard ((layoutResult nestedEnvironment (.bytes 0)).map Layout.leafCount == some 0)

private def enumEnvironment : CompositeEnv := {
  enumerations := [{id := "Fixture.Result", span := point, variants := [
    {name := "empty", span := point},
    {name := "value", span := point, fields := [
      {name := "payload", type := .scalar (.uint 31), span := point}
    ]}
  ]}]
}

private def enumSummary : Option (ScalarLeaf × Nat × Nat × EnumPayloadPolicy) :=
  match layout defaultLimits enumEnvironment (.enumeration "Fixture.Result") with
  | .ok (.enumeration _ tag maximum payload policy _) => some (tag, maximum, payload, policy)
  | _ => none

-- Enum layouts use UInt(variantCount - 1), then pad each variant to the maximum payload width.
#guard enumSummary == some (.enumTagField 1, 1, 1, .zeroPadToMaximum)
#guard layoutResult {enumEnvironment with enumerations := [{id := "Fixture.Empty", variants := []}]}
    (.enumeration "Fixture.Empty") == none

-- TYC-IDENTITY: same physical fields do not collapse distinct nominal declarations.
private def nominalTwins : CompositeEnv := {
  structures := [
    {id := "Fixture.Left", fields := [{name := "x", type := .scalar .native}]},
    {id := "Fixture.Right", fields := [{name := "x", type := .scalar .native}]}
  ]
}

#guard (CompositeType.fingerprint nominalTwins (.structure "Fixture.Left") !=
  CompositeType.fingerprint nominalTwins (.structure "Fixture.Right"))
#guard (CompositeType.fingerprint nominalTwins (.tuple [.scalar .native, .scalar .bool]) ==
  CompositeType.fingerprint nominalTwins (.tuple [.scalar .native, .scalar .bool]))
private def withUnrelatedDeclaration : CompositeEnv := {
  structures := nominalTwins.structures ++ [
    {id := "Fixture.Unrelated", fields := [{name := "value", type := .bytes 17}]}
  ]
}
#guard CompositeType.fingerprint nominalTwins (.structure "Fixture.Left") ==
  CompositeType.fingerprint withUnrelatedDeclaration (.structure "Fixture.Left")

private def changedReachableInner : CompositeEnv := {
  structures := [
    {id := "Fixture.Inner", fields := [
      {name := "enabled", type := .scalar .bool},
      {name := "amount", type := .scalar (.uint 256)}
    ]},
    {id := "Fixture.Outer", fields := [
      {name := "header", type := .scalar .native},
      {name := "inner", type := .structure "Fixture.Inner"},
      {name := "samples", type := .vector 2 (.scalar (.uint 7))},
      {name := "memo", type := .bytes 3}
    ]}
  ]
}
#guard CompositeType.fingerprint nestedEnvironment (.structure "Fixture.Outer") !=
  CompositeType.fingerprint changedReachableInner (.structure "Fixture.Outer")

private def changedFieldOrder : CompositeEnv := {
  structures := [{id := "Fixture.Record", fields := [
    {name := "second", type := .scalar .bool},
    {name := "first", type := .scalar .native}
  ]}]
}
private def originalFieldOrder : CompositeEnv := {
  structures := [{id := "Fixture.Record", fields := [
    {name := "first", type := .scalar .native},
    {name := "second", type := .scalar .bool}
  ]}]
}
#guard (originalFieldOrder.fingerprint != changedFieldOrder.fingerprint)

private def changedVariantOrder : CompositeEnv := {
  enumerations := [{id := "Fixture.Ordered", variants := [
    {name := "second"}, {name := "first"}
  ]}]
}
private def originalVariantOrder : CompositeEnv := {
  enumerations := [{id := "Fixture.Ordered", variants := [
    {name := "first"}, {name := "second"}
  ]}]
}
#guard (originalVariantOrder.fingerprint != changedVariantOrder.fingerprint)

-- TYC-LENGTH: limits reject before an expanded layout is built and report the source span.
#guard ((errorResult nestedEnvironment (.vector 1025 (.scalar .native))).isSome)
#guard errorSpan (layout defaultLimits nestedEnvironment (.vector 1025 (.scalar .native)) point) == some point
#guard ((errorResult nestedEnvironment (.vector 3 (.scalar .native))
    {defaultLimits with maxVectorLength := 2}).isSome)
#guard ((errorResult nestedEnvironment (.vector 4 (.scalar .native))
    {defaultLimits with maxExpandedLeaves := 3}).isSome)
#guard ((errorResult nestedEnvironment (.vector 2 (.scalar .native))
    {defaultLimits with maxExpandedNodes := 2}).isSome)
#guard ((layoutResult nestedEnvironment (.vector 1024 (.scalar .bool))).map Layout.leafCount == some 1024)
#guard ((layoutResult nestedEnvironment (.bytes 1054)).map Layout.leafCount == some 1054)
#guard ((errorResult nestedEnvironment (.bytes 1055)).isSome)
#guard ((errorResult nestedEnvironment (.scalar (.uint (ScalarPolicy.maxUint + 1)))).isSome)
#guard isError (layout {defaultLimits with maxExpandedLeaves := 1_000_000}
  nestedEnvironment .unit)
#guard ((layoutResult nestedEnvironment (.vector 0 (.scalar .native))).map Layout.leafCount == some 0)

-- TYC-CYCLE: forward references resolve, direct and indirect recursive layouts reject.
private def indirectCycle : CompositeEnv := {
  structures := [
    {id := "Fixture.First", span := point, fields := [
      {name := "next", type := .structure "Fixture.Second", span := point}
    ]},
    {id := "Fixture.Second", span := point, fields := [
      {name := "previous", type := .structure "Fixture.First", span := point}
    ]}
  ]
}
#guard isError (layout defaultLimits indirectCycle (.structure "Fixture.First"))
#guard ((errorResult indirectCycle (.structure "Fixture.First")).map LayoutDiagnostic.span == some point)
#guard ((layoutResult nestedEnvironment (.structure "Fixture.Outer")).isSome)
#guard isError (layout defaultLimits nestedEnvironment (.structure "Fixture.Missing"))

private def unknownFieldReference : CompositeEnv := {
  structures := [{id := "Fixture.UnknownRef", fields := [
    {name := "missing", type := .structure "Fixture.Absent", span := point}
  ]}]
}
#guard errorSpan (layout defaultLimits unknownFieldReference (.structure "Fixture.UnknownRef")) == some point

private def directCycle : CompositeEnv := {
  structures := [{id := "Fixture.Self", span := point, fields := [
    {name := "self", type := .structure "Fixture.Self", span := point}
  ]}]
}
#guard isError (layout defaultLimits directCycle (.structure "Fixture.Self"))
#guard checkedIsOk (checkedLayout defaultLimits nestedEnvironment (.structure "Fixture.Outer"))

example (checked : CheckedLayout defaultLimits) :
    checked.value.leafCount ≤ defaultLimits.maxExpandedLeaves := by
  rw [checked.leafCountMatches]
  exact checked.leafCountBound

example (checked : CheckedLayout defaultLimits) :
    checked.expandedNodes ≤ defaultLimits.maxExpandedNodes := checked.expandedNodeBound

example (checked : CheckedLayout defaultLimits) :
    checked.value.nodeCount = checked.layoutNodes := checked.layoutNodeCountMatches

example (checked : CheckedLayout defaultLimits) :
    checked.value.expandedNodeCount = checked.expandedNodes := checked.expandedNodeCountMatches

example (checked : CheckedLayout defaultLimits) :
    checked.value.nodeCount ≤ defaultLimits.maxLayoutNodes := by
  rw [checked.layoutNodeCountMatches]
  exact checked.layoutNodeBound

example (checked : CheckedLayout defaultLimits) :
    checked.value.expandedNodeCount ≤ defaultLimits.maxExpandedNodes := by
  rw [checked.expandedNodeCountMatches]
  exact checked.expandedNodeBound

private def duplicateIdentity : CompositeEnv := {
  structures := [
    {id := "Fixture.Duplicate", fields := []},
    {id := "Fixture.Duplicate", fields := [], span := point}
  ]
}
#guard isError (layout defaultLimits duplicateIdentity (.structure "Fixture.Duplicate"))
#guard errorSpan (layout defaultLimits duplicateIdentity (.structure "Fixture.Duplicate")) == some point

private def invalidIdentity : CompositeEnv := {
  structures := [{id := "Fixture.Bad-Name", span := point, fields := []}]
}
#guard errorSpan (layout defaultLimits invalidIdentity (.structure "Fixture.Bad-Name")) == some point

-- TYC-LENGTH regression: zero-length vectors retain their element type layout.
private def chainName (depth : Nat) : String := s!"Fixture.S{depth}"

private def chainDeclaration (depth : Nat) : StructDecl :=
  if depth == 0 then
    {id := chainName 0, fields := []}
  else
    {id := chainName depth, fields := [
      {name := "left", type := .vector 0 (.structure (chainName (depth - 1)))},
      {name := "right", type := .vector 0 (.structure (chainName (depth - 1)))}
    ]}

private def zeroVectorChain : CompositeEnv := {
  structures := (List.range 9).map chainDeclaration
}

-- S8 has 3 logical expanded nodes but 1,021 retained Layout constructors.
#guard checkedSummary {defaultLimits with maxExpandedNodes := 100, maxLayoutNodes := 100}
  zeroVectorChain (.structure (chainName 8)) == none
#guard checkedSummary {defaultLimits with maxExpandedNodes := 100, maxLayoutNodes := 1021}
  zeroVectorChain (.structure (chainName 8)) == some (3, 1021, 3, 1021)

private def duplicateVariantNames : CompositeEnv := {
  enumerations := [{id := "Fixture.DuplicateVariant", variants := [
    {name := "same"}, {name := "same", span := point}
  ]}]
}
#guard isError (layout defaultLimits duplicateVariantNames (.enumeration "Fixture.DuplicateVariant"))
#guard errorSpan (layout defaultLimits duplicateVariantNames
  (.enumeration "Fixture.DuplicateVariant")) == some point

private def overLimitDeclarations : CompositeEnv := {
  structures := [
    {id := "Fixture.One", fields := []},
    {id := "Fixture.Two", fields := []}
  ]
}
#guard isError (layout {defaultLimits with maxDeclarations := 1}
  overLimitDeclarations (.structure "Fixture.One"))

private def duplicateFields : CompositeEnv := {
  structures := [{id := "Fixture.Fields", span := point, fields := [
    {name := "same", type := .scalar .native},
    {name := "same", type := .scalar .bool, span := point}
  ]}]
}
#guard errorSpan (layout defaultLimits duplicateFields (.structure "Fixture.Fields")) == some point

-- TYC-SUBTYPE: only exact nominal identity and proved structural/UInt widening pass.
example : CompositeSubtype
    (.tuple [.scalar (.uint 7), .scalar .bool])
    (.tuple [.scalar (.uint 255), .scalar .bool]) := by
  exact CompositeSubtype.tuple <| CompositeSubtypeList.cons
    (.unsigned (by omega) (by decide))
    (CompositeSubtypeList.cons .boolean .nil)

example : ¬ CompositeSubtype (.structure "Fixture.Left") (.structure "Fixture.Right") := by
  intro proof
  have ids := CompositeSubtype.structure_id_eq proof
  have differentIds : "Fixture.Left" ≠ "Fixture.Right" := by decide
  exact differentIds ids

example : ¬ CompositeSubtype (.enumeration "Fixture.Left") (.enumeration "Fixture.Right") := by
  intro proof
  have ids := CompositeSubtype.enum_id_eq proof
  have differentIds : "Fixture.Left" ≠ "Fixture.Right" := by decide
  exact differentIds ids

example : ¬ CompositeSubtype (.scalar (.uint 255)) (.scalar (.uint 7)) := by
  intro proof
  cases proof with
  | unsigned bound _ => omega

example : ¬ CompositeSubtype (.scalar (.uint (ScalarPolicy.maxUint + 1)))
    (.scalar (.uint (ScalarPolicy.maxUint + 1))) := by
  intro proof
  cases proof with
  | unsigned _ supported => omega

example : CompositeSubtype (.vector 4 (.scalar (.uint 3)))
    (.vector 4 (.scalar (.uint 9))) := by
  apply CompositeSubtype.vector
  exact .unsigned (by omega) (by decide)

