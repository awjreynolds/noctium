import Noctium.Core

namespace Noctium.Types

/-- Canonical declaration names use qualified Lean-style ASCII names. -/
abbrev DeclId := String

private def asciiAlpha (code : Nat) : Bool :=
  (65 ≤ code && code ≤ 90) || (97 ≤ code && code ≤ 122)

private def asciiDigit (code : Nat) : Bool := 48 ≤ code && code ≤ 57

private def validSegment (segment : String) : Bool := Id.run do
  let chars := segment.toList
  if chars.isEmpty then return false
  let first := chars.head!
  let firstCode := first.toNat
  if !(asciiAlpha firstCode || first == '_') then return false
  return chars.all fun char =>
    let code := char.toNat
    asciiAlpha code || asciiDigit code || char == '_'

/-- Declaration identity is a fully qualified name, not a layout fingerprint. -/
def validDeclId (id : DeclId) : Bool :=
  (id.splitOn ".").all validSegment

def validFieldName (name : String) : Bool := validSegment name

inductive CompositeType where
  | unit
  | scalar (ty : Ty)
  | tuple (items : List CompositeType)
  | structure (id : DeclId)
  | enumeration (id : DeclId)
  | vector (length : Nat) (element : CompositeType)
  | bytes (length : Nat)
  deriving Repr

mutual
  /-- Total structural comparison keeps nested type equality available to kernel proofs. -/
  def CompositeType.structuralBEq : CompositeType → CompositeType → Bool
    | .unit, .unit => true
    | .scalar a, .scalar b => decide (a = b)
    | .tuple as, .tuple bs => structuralListBEq as bs
    | .structure a, .structure b => a == b
    | .enumeration a, .enumeration b => a == b
    | .vector n a, .vector m b => n == m && structuralBEq a b
    | .bytes n, .bytes m => n == m
    | _, _ => false
  termination_by a _ => sizeOf a
  decreasing_by all_goals simp_wf <;> omega

  def CompositeType.structuralListBEq : List CompositeType → List CompositeType → Bool
    | [], [] => true
    | a :: as, b :: bs => structuralBEq a b && structuralListBEq as bs
    | _, _ => false
  termination_by as _ => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
end


mutual
  theorem CompositeType.structuralBEq_eq_true (a b : CompositeType) :
      structuralBEq a b = true ↔ a = b := by
    cases a <;> cases b <;> simp [structuralBEq]
    · rename_i as bs
      exact structuralListBEq_eq_true as bs
    · rename_i n a m b
      rw [structuralBEq_eq_true a b]
      intro _
      rfl
  termination_by sizeOf a
  decreasing_by all_goals simp_wf <;> omega

  theorem CompositeType.structuralListBEq_eq_true (as bs : List CompositeType) :
      structuralListBEq as bs = true ↔ as = bs := by
    cases as <;> cases bs <;> simp [structuralListBEq]
    rename_i a as b bs
    rw [structuralBEq_eq_true a b, structuralListBEq_eq_true as bs]
  termination_by sizeOf as
  decreasing_by all_goals simp_wf <;> omega
end

instance : BEq CompositeType := ⟨CompositeType.structuralBEq⟩

/-- Structural equality preserves constructor and nominal identity. -/
instance : LawfulBEq CompositeType where
  rfl {a} := (CompositeType.structuralBEq_eq_true a a).mpr rfl
  eq_of_beq {a b} h := (CompositeType.structuralBEq_eq_true a b).mp h

instance : DecidableEq CompositeType := fun left right =>
  if equal : left == right then
    isTrue ((CompositeType.structuralBEq_eq_true left right).mp equal)
  else
    isFalse (fun unequal => equal ((CompositeType.structuralBEq_eq_true left right).mpr unequal))

structure Field where
  name : String
  type : CompositeType
  span : SourceSpan := {}
  deriving Repr, BEq, DecidableEq

structure StructDecl where
  id : DeclId
  fields : List Field
  span : SourceSpan := {}
  deriving Repr, BEq, DecidableEq

structure VariantDecl where
  name : String
  fields : List Field := []
  span : SourceSpan := {}
  deriving Repr, BEq, DecidableEq

structure EnumDecl where
  id : DeclId
  variants : List VariantDecl
  span : SourceSpan := {}
  deriving Repr, BEq, DecidableEq

structure CompositeEnv where
  structures : List StructDecl := []
  enumerations : List EnumDecl := []
  deriving Repr, BEq, DecidableEq

/-- These are local compiler resource limits, not upstream language limits. -/
structure Limits where
  maxDeclarations : Nat := 1024
  maxVectorLength : Nat := 1024
  maxBytesLength : Nat := 1054
  maxExpandedLeaves : Nat := 4096
  maxExpandedNodes : Nat := 16384
  maxLayoutNodes : Nat := 16384
  deriving Repr, BEq

def defaultLimits : Limits := {}

structure LayoutDiagnostic where
  span : SourceSpan
  message : String
  deriving Repr, BEq

inductive ScalarLeaf where
  | nativeField
  | booleanField
  | boundedUnsignedField (maximum : Nat)
  | enumTagField (maximum : Nat)
  | byteField
  deriving Repr, BEq, DecidableEq

inductive EnumPayloadPolicy where
  | zeroPadToMaximum
  deriving Repr, BEq, DecidableEq

/-- A symbolic layout. Fixed vectors retain one element layout and a checked
length, so layout construction never allocates one node per vector element. -/
inductive Layout where
  | unit
  | scalar (leaf : ScalarLeaf)
  /-- An opaque logical value with one native Compress ABI field. This layout
  does not make the value reversible as a scalar or aggregate byte sequence. -/
  | opaque (type : Ty)
  | curve (type : Ty)
  | tuple (items : List Layout)
  | structure (id : DeclId) (fields : List (String × Layout))
  | vector (length : Nat) (element : Layout)
  | bytes (length : Nat) (leaf : ScalarLeaf)
  | enumeration (id : DeclId) (tag : ScalarLeaf) (tagMaximum payloadLeaves : Nat)
      (padding : EnumPayloadPolicy)
      (variants : List (String × List (String × Layout) × Nat))
  deriving Repr, BEq, Inhabited

abbrev LayoutField := String × Layout
abbrev LayoutVariant := String × List LayoutField × Nat

mutual
  /-- True only for layouts made entirely from native-field leaves. -/
  def Layout.nativeFieldOnly : Layout → Bool
    | .scalar .nativeField => true
    | .tuple items => LayoutList.nativeFieldOnly items
    | .structure _ fields => LayoutFields.nativeFieldOnly fields
    | .vector _ element => element.nativeFieldOnly
    | _ => false

  def LayoutList.nativeFieldOnly : List Layout → Bool
    | [] => true
    | item :: rest => item.nativeFieldOnly && LayoutList.nativeFieldOnly rest

  def LayoutFields.nativeFieldOnly : List (String × Layout) → Bool
    | [] => true
    | (_, item) :: rest => item.nativeFieldOnly && LayoutFields.nativeFieldOnly rest
end

mutual
  def Layout.leafCount : Layout → Nat
    | .unit => 0
    | .scalar _ => 1
    | .opaque _ => 1
    | .curve type => type.nativeCallFieldCount
    | .tuple items => LayoutList.leafCount items
    | .structure _ fields => LayoutFields.leafCount fields
    | .vector length element => length * element.leafCount
    | .bytes length _ => length
    | .enumeration _ _ _ payloadLeaves _ _ => 1 + payloadLeaves

  def LayoutList.leafCount : List Layout → Nat
    | [] => 0
    | item :: rest => item.leafCount + LayoutList.leafCount rest

  def LayoutFields.leafCount : List (String × Layout) → Nat
    | [] => 0
    | (_, item) :: rest => item.leafCount + LayoutFields.leafCount rest
end

mutual
  def Layout.nodeCount : Layout → Nat
    | .unit | .scalar _ | .opaque _ | .curve _ | .bytes _ _ => 1
    | .tuple items => 1 + LayoutList.nodeCount items
    | .structure _ fields => 1 + LayoutFields.nodeCount fields
    | .vector _ element => 1 + element.nodeCount
    | .enumeration _ _ _ _ _ variants => 1 + LayoutVariants.nodeCount variants

  def LayoutList.nodeCount : List Layout → Nat
    | [] => 0
    | item :: rest => item.nodeCount + LayoutList.nodeCount rest

  def LayoutFields.nodeCount : List (String × Layout) → Nat
    | [] => 0
    | (_, item) :: rest => item.nodeCount + LayoutFields.nodeCount rest

  def LayoutVariants.nodeCount : List (String × List (String × Layout) × Nat) → Nat
    | [] => 0
    | variant :: rest => 1 + LayoutFields.nodeCount variant.2.1 + LayoutVariants.nodeCount rest
end

/-- Find a fixed-byte field below a chain of named structure fields and return
its expanded logical leaf offset and byte length. -/
partial def Layout.byteRangeAtFieldPath (layout : Layout) (path : List String)
    (offset : Nat := 0) : Option (Nat × Nat) :=
  match layout, path with
  | .bytes length .byteField, [] => some (offset, length)
  | .structure _ fields, name :: rest => do
    let index := fields.findIdx? (·.1 == name)
    let index ← index
    let field := fields[index]?.map Prod.snd
    let field ← field
    let preceding := (fields.take index).foldl (fun total item => total + item.2.leafCount) 0
    field.byteRangeAtFieldPath rest (offset + preceding)
  | _, _ => none

mutual
  def Layout.expandedNodeCount : Layout → Nat
    | .unit | .scalar _ | .opaque _ => 1
    | .curve type => 1 + type.nativeCallFieldCount
    | .tuple items => 1 + LayoutList.expandedNodeCount items
    | .structure _ fields => 1 + LayoutFields.expandedNodeCount fields
    | .vector length element => 1 + length * element.expandedNodeCount
    | .bytes length _ => 1 + length
    | .enumeration _ _ _ _ _ variants => 1 + LayoutVariants.expandedNodeCount variants

  def LayoutList.expandedNodeCount : List Layout → Nat
    | [] => 0
    | item :: rest => item.expandedNodeCount + LayoutList.expandedNodeCount rest

  def LayoutFields.expandedNodeCount : List (String × Layout) → Nat
    | [] => 0
    | (_, item) :: rest => item.expandedNodeCount + LayoutFields.expandedNodeCount rest

  def LayoutVariants.expandedNodeCount : List (String × List (String × Layout) × Nat) → Nat
    | [] => 0
    | variant :: rest => 1 + LayoutFields.expandedNodeCount variant.2.1 +
        LayoutVariants.expandedNodeCount rest
end

/-- Successful preflight returns a finite inductive layout together with the
checked expanded-size facts used before construction. -/
structure CheckedLayout (limits : Limits) where
  value : Layout
  expandedLeaves : Nat
  expandedNodes : Nat
  layoutNodes : Nat
  leafCountMatches : value.leafCount = expandedLeaves
  expandedNodeCountMatches : value.expandedNodeCount = expandedNodes
  layoutNodeCountMatches : value.nodeCount = layoutNodes
  leafCountBound : expandedLeaves ≤ limits.maxExpandedLeaves
  expandedNodeBound : expandedNodes ≤ limits.maxExpandedNodes
  layoutNodeBound : layoutNodes ≤ limits.maxLayoutNodes
  deriving Repr

def scalarLeaf : Ty → Except String ScalarLeaf
  | .native => pure .nativeField
  | .bool => pure .booleanField
  | .uint maximum => pure (.boundedUnsignedField maximum)
  | .bytes _ => .error "byte strings require a composite bytes layout"
  | .opaqueBytes => .error "OpaqueBytes require a qualified ledger scalar schema"
  | .opaqueString => .error "OpaqueString requires a qualified ledger scalar schema"
  | .jubjubScalar | .jubjubPoint => .error "Jubjub values require a qualified curve schema"
  | .foreign _ => .error "foreign values require a qualified curve schema"

private def isOpaqueType : Ty → Bool
  | .opaqueBytes | .opaqueString => true
  | _ => false

private def validateScalarLayoutTy (ty : Ty) : Except String Unit := do
  if ty.isBytes then throw "byte strings require a composite bytes layout"
  if ty.isJubjub then throw "Jubjub values require a qualified curve schema"
  ScalarPolicy.validate ty.scalarKind

mutual
  inductive CompositeSubtype : CompositeType → CompositeType → Prop where
    | unit : CompositeSubtype .unit .unit
    | native : CompositeSubtype (.scalar .native) (.scalar .native)
    | boolean : CompositeSubtype (.scalar .bool) (.scalar .bool)
    | opaqueBytes : CompositeSubtype (.scalar .opaqueBytes) (.scalar .opaqueBytes)
    | opaqueString : CompositeSubtype (.scalar .opaqueString) (.scalar .opaqueString)
    | jubjubScalar : CompositeSubtype (.scalar .jubjubScalar) (.scalar .jubjubScalar)
    | jubjubPoint : CompositeSubtype (.scalar .jubjubPoint) (.scalar .jubjubPoint)
    | foreign (kind : Foreign.Kind) :
        CompositeSubtype (.scalar (.foreign kind)) (.scalar (.foreign kind))
    | unsigned {source target : Nat} (bound : source ≤ target)
        (supported : target ≤ ScalarPolicy.maxUint) :
        CompositeSubtype (.scalar (.uint source)) (.scalar (.uint target))
    | unsignedNative {source : Nat} (supported : source ≤ ScalarPolicy.maxUint) :
        CompositeSubtype (.scalar (.uint source)) (.scalar .native)
    | tuple {source target : List CompositeType}
        (items : CompositeSubtypeList source target) :
        CompositeSubtype (.tuple source) (.tuple target)
    | structure (id : DeclId) :
        CompositeSubtype (.structure id) (.structure id)
    | enumeration (id : DeclId) :
        CompositeSubtype (.enumeration id) (.enumeration id)
    | vector {length : Nat} {source target : CompositeType}
        (element : CompositeSubtype source target) :
        CompositeSubtype (.vector length source) (.vector length target)
    | bytes (length : Nat) : CompositeSubtype (.bytes length) (.bytes length)

  inductive CompositeSubtypeList : List CompositeType → List CompositeType → Prop where
    | nil : CompositeSubtypeList [] []
    | cons {source target : CompositeType} {sources targets : List CompositeType}
        (head : CompositeSubtype source target)
        (tail : CompositeSubtypeList sources targets) :
        CompositeSubtypeList (source :: sources) (target :: targets)
end

def scalarLeastUpperBound? : Ty → Ty → Option Ty
  | source, target =>
    if source == target then some source
    else match source, target with
      | .uint left, .uint right =>
        let maximum := max left right
        if maximum ≤ ScalarPolicy.maxUint then some (.uint maximum) else none
      | .uint _, .native | .native, .uint _ => some .native
      | _, _ => none

mutual
  /-- Least common type for same-shape composite values. Nominal declarations
  and byte lengths stay exact. -/
  def CompositeType.leastUpperBound? : CompositeType → CompositeType → Option CompositeType
    | .unit, .unit => some .unit
    | .scalar left, .scalar right => (.scalar ·) <$> scalarLeastUpperBound? left right
    | .tuple left, .tuple right => do
      if left.length != right.length then none
      .tuple <$> CompositeTypeList.leastUpperBound? left right
    | .structure left, .structure right => if left == right then some (.structure left) else none
    | .enumeration left, .enumeration right => if left == right then some (.enumeration left) else none
    | .vector leftLength left, .vector rightLength right =>
      if leftLength == rightLength then
        .vector leftLength <$> CompositeType.leastUpperBound? left right
      else none
    | .bytes left, .bytes right => if left == right then some (.bytes left) else none
    | _, _ => none

  def CompositeTypeList.leastUpperBound? : List CompositeType → List CompositeType → Option (List CompositeType)
    | [], [] => some []
    | left :: leftRest, right :: rightRest => do
      let item ← CompositeType.leastUpperBound? left right
      let rest ← CompositeTypeList.leastUpperBound? leftRest rightRest
      pure (item :: rest)
    | _, _ => none
end

def CompositeType.isSubtype (source target : CompositeType) : Bool :=
  CompositeType.leastUpperBound? source target == some target

theorem CompositeSubtype.structure_id_eq {left right : DeclId}
    (proof : CompositeSubtype (.structure left) (.structure right)) : left = right := by
  cases proof
  rfl

theorem CompositeSubtype.enum_id_eq {left right : DeclId}
    (proof : CompositeSubtype (.enumeration left) (.enumeration right)) : left = right := by
  cases proof
  rfl

def CompositeType.referencedIds : CompositeType → List DeclId
  | .unit | .scalar _ | .bytes _ => []
  | .tuple items => items.flatMap CompositeType.referencedIds
  | .structure id | .enumeration id => [id]
  | .vector _ element => element.referencedIds

private def Field.referencedIds (field : Field) : List DeclId := field.type.referencedIds

private def declarationIds (environment : CompositeEnv) : List DeclId :=
  environment.structures.map (·.id) ++ environment.enumerations.map (·.id)

private def findStruct (environment : CompositeEnv) (id : DeclId) : Option StructDecl :=
  environment.structures.find? (·.id == id)

private def findEnum (environment : CompositeEnv) (id : DeclId) : Option EnumDecl :=
  environment.enumerations.find? (·.id == id)

private def declarationSpan (environment : CompositeEnv) (id : DeclId) : SourceSpan :=
  match findStruct environment id, findEnum environment id with
  | some declaration, _ => declaration.span
  | none, some declaration => declaration.span
  | none, none => {}

private def fieldsOf (environment : CompositeEnv) (id : DeclId) : Option (List Field) := do
  if let some declaration := findStruct environment id then
    return declaration.fields
  let declaration ← findEnum environment id
  return declaration.variants.flatMap (·.fields)

private def typeSpanForReference (environment : CompositeEnv) (source target : DeclId) : SourceSpan :=
  match (fieldsOf environment source).bind (fun fields => fields.find? fun field =>
      field.type.referencedIds.contains target) with
  | some field => field.span
  | none => declarationSpan environment source

private def referencesOfFields (fields : List Field) : List DeclId :=
  fields.flatMap Field.referencedIds

private def declarationReferences (environment : CompositeEnv) (id : DeclId) : List DeclId :=
  match findStruct environment id, findEnum environment id with
  | some declaration, _ => referencesOfFields declaration.fields
  | none, some declaration => referencesOfFields (declaration.variants.flatMap (·.fields))
  | none, none => []

private def indexFields (start : Nat) : List Field → List (Nat × Field)
  | [] => []
  | field :: rest => (start, field) :: indexFields (start + 1) rest

private def duplicateField? (fields : List Field) : Option Field := Id.run do
  let indexed := indexFields 0 fields
  let sorted := indexed.mergeSort fun left right =>
    if left.2.name == right.2.name then left.1 < right.1
    else decide (left.2.name < right.2.name)
  let rec adjacent : List (Nat × Field) → Option Field
    | first :: second :: rest =>
      if first.2.name == second.2.name then some second.2 else adjacent (second :: rest)
    | _ => none
  return adjacent sorted

private def indexVariants (start : Nat) : List VariantDecl → List (Nat × VariantDecl)
  | [] => []
  | variant :: rest => (start, variant) :: indexVariants (start + 1) rest

private def duplicateVariant? (variants : List VariantDecl) : Option VariantDecl := Id.run do
  let sorted := (indexVariants 0 variants).mergeSort fun left right =>
    if left.2.name == right.2.name then left.1 < right.1
    else decide (left.2.name < right.2.name)
  let rec adjacent : List (Nat × VariantDecl) → Option VariantDecl
    | first :: second :: rest =>
      if first.2.name == second.2.name then some second.2 else adjacent (second :: rest)
    | _ => none
  return adjacent sorted

private def visitReachable (environment : CompositeEnv) (target : DeclId)
    (fuel : Nat) (pending visited : List DeclId) : List DeclId :=
  match fuel, pending with
  | 0, _ => visited
  | _, [] => visited
  | fuel + 1, id :: rest =>
    if id == target then
      target :: visited
    else if visited.contains id then
      visitReachable environment target fuel rest visited
    else
      visitReachable environment target fuel
        (declarationReferences environment id ++ rest) (id :: visited)

private def hasCycleFrom (environment : CompositeEnv) (start : DeclId) : Bool :=
  (declarationReferences environment start).any fun next =>
    next == start ||
      ((visitReachable environment start (declarationIds environment).length
        [next] []).contains start)

private def checkFields (fields : List Field) : Except LayoutDiagnostic Unit := do
  match duplicateField? fields with
  | some field => throw {span := field.span, message := s!"duplicate field '{field.name}'"}
  | none => pure ()
  for field in fields do
    unless validFieldName field.name do
      throw {span := field.span, message := s!"invalid field name '{field.name}'"}

private def diagnostic (span : SourceSpan) (message : String) : LayoutDiagnostic :=
  {span := span, message := message}

def Limits.validate (limits : Limits) : Except LayoutDiagnostic Limits := do
  if limits.maxDeclarations > defaultLimits.maxDeclarations ||
      limits.maxVectorLength > defaultLimits.maxVectorLength ||
      limits.maxBytesLength > defaultLimits.maxBytesLength ||
      limits.maxExpandedLeaves > defaultLimits.maxExpandedLeaves ||
      limits.maxExpandedNodes > defaultLimits.maxExpandedNodes ||
      limits.maxLayoutNodes > defaultLimits.maxLayoutNodes then
    throw {span := {}, message := "composite limits cannot exceed the compiler's published resource policy"}
  return limits

private def validateDeclarations (limits : Limits) (environment : CompositeEnv) :
    Except LayoutDiagnostic CompositeEnv := do
  let ids := declarationIds environment
  let declaredNodes := environment.structures.foldl
      (fun count declaration => count + 1 + declaration.fields.length) 0 +
    environment.enumerations.foldl (fun count declaration =>
      count + 1 + declaration.variants.length +
        declaration.variants.foldl (fun fields variant => fields + variant.fields.length) 0) 0
  if declaredNodes > limits.maxLayoutNodes then
    throw {span := {}, message := "composite declarations exceed local retained-layout-node limit"}
  if ids.length > limits.maxDeclarations then
    throw {span := {}, message := "composite declaration count exceeds local compiler limit"}
  let mut seen : List DeclId := []
  for declaration in environment.structures do
    unless validDeclId declaration.id do
      throw {span := declaration.span, message := s!"invalid declaration identity '{declaration.id}'"}
    if seen.contains declaration.id then
      throw {span := declaration.span, message := s!"duplicate declaration identity '{declaration.id}'"}
    seen := declaration.id :: seen
    checkFields declaration.fields
  for declaration in environment.enumerations do
    unless validDeclId declaration.id do
      throw {span := declaration.span, message := s!"invalid declaration identity '{declaration.id}'"}
    if seen.contains declaration.id then
      throw {span := declaration.span, message := s!"duplicate declaration identity '{declaration.id}'"}
    seen := declaration.id :: seen
    if declaration.variants.isEmpty then
      throw {span := declaration.span, message := "an enumeration must declare at least one variant"}
    match duplicateVariant? declaration.variants with
    | some variant => throw {span := variant.span, message := s!"duplicate variant '{variant.name}'"}
    | none => pure ()
    for variant in declaration.variants do
      unless validFieldName variant.name do
        throw {span := variant.span, message := s!"invalid variant name '{variant.name}'"}
      checkFields variant.fields
  for id in ids do
    for reference in declarationReferences environment id do
      unless ids.contains reference do
        throw (diagnostic (typeSpanForReference environment id reference)
          s!"unknown composite declaration '{reference}'")
    if hasCycleFrom environment id then
      throw (diagnostic (declarationSpan environment id)
        s!"recursive composite layout involving '{id}' is unsupported")
  return environment

private structure BoundedMeasure (limits : Limits) where
  leaves : Nat
  expandedNodes : Nat
  layoutNodes : Nat
  leafBound : leaves ≤ limits.maxExpandedLeaves
  expandedNodeBound : expandedNodes ≤ limits.maxExpandedNodes
  layoutNodeBound : layoutNodes ≤ limits.maxLayoutNodes

private def checkedMeasure (limits : Limits) (span : SourceSpan)
    (leaves expandedNodes layoutNodes : Nat) : Except LayoutDiagnostic (BoundedMeasure limits) := do
  if h : leaves ≤ limits.maxExpandedLeaves then
    if hn : expandedNodes ≤ limits.maxExpandedNodes then
      if hl : layoutNodes ≤ limits.maxLayoutNodes then
        return ⟨leaves, expandedNodes, layoutNodes, h, hn, hl⟩
      else
        throw {span, message := "composite layout exceeds local retained-layout-node limit"}
    else
      throw {span, message := "composite layout exceeds local expanded-node limit"}
  else
    throw {span, message := "composite layout exceeds local expanded-leaf limit"}

private def addMeasure (limits : Limits) (span : SourceSpan)
    (left right : BoundedMeasure limits) : Except LayoutDiagnostic (BoundedMeasure limits) := do
  let leaves := left.leaves + right.leaves
  let expandedNodes := left.expandedNodes + right.expandedNodes
  let layoutNodes := left.layoutNodes + right.layoutNodes
  checkedMeasure limits span leaves expandedNodes layoutNodes

private def measureType (fuel : Nat) (limits : Limits) (environment : CompositeEnv)
    (stack : List DeclId) (span : SourceSpan) (type : CompositeType) :
    Except LayoutDiagnostic (BoundedMeasure limits) := do
  match fuel with
  | 0 => throw {span, message := "composite nesting exceeds local compiler limit"}
  | fuel + 1 => match type with
    | .unit => checkedMeasure limits span 0 1 1
    | .scalar ty => do
      if ty.isJubjub || ty.isForeign then
        let width := ty.nativeCallFieldCount
        return ← checkedMeasure limits span width (1 + width) 1
      if isOpaqueType ty then
        return ← checkedMeasure limits span 1 1 1
      match validateScalarLayoutTy ty with
      | .ok _ => pure ()
      | .error message => throw {span, message}
      checkedMeasure limits span 1 1 1
    | .tuple items => do
      let mut result ← checkedMeasure limits span 0 1 1
      for item in items do
        let child ← measureType fuel limits environment stack span item
        result ← addMeasure limits span result child
      return result
    | .structure id => do
      if stack.contains id then throw {span, message := s!"recursive composite layout involving '{id}' is unsupported"}
      let some declaration := findStruct environment id
        | throw {span, message := s!"unknown structure '{id}'"}
      let mut result ← checkedMeasure limits declaration.span 0 1 1
      for field in declaration.fields do
        result ← addMeasure limits field.span result
          (← measureType fuel limits environment (id :: stack) field.span field.type)
      return result
    | .enumeration id => do
      if stack.contains id then throw {span, message := s!"recursive composite layout involving '{id}' is unsupported"}
      let some declaration := findEnum environment id
        | throw {span, message := s!"unknown enumeration '{id}'"}
      if declaration.variants.isEmpty then
        throw {span := declaration.span, message := "an enumeration must declare at least one variant"}
      let mut payloadLeaves := 0
      let mut expandedNodes := 1 + declaration.variants.length
      let mut layoutNodes := 1 + declaration.variants.length
      for variant in declaration.variants do
        let mut payload ← checkedMeasure limits variant.span 0 0 0
        for field in variant.fields do
          payload ← addMeasure limits field.span payload
            (← measureType fuel limits environment (id :: stack) field.span field.type)
        payloadLeaves := max payloadLeaves payload.leaves
        expandedNodes := expandedNodes + payload.expandedNodes
        layoutNodes := layoutNodes + payload.layoutNodes
      let leaves := payloadLeaves + 1
      checkedMeasure limits span leaves expandedNodes layoutNodes
    | .vector length element => do
      if length > limits.maxVectorLength then
        throw {span, message := "fixed-vector length exceeds local compiler limit"}
      let child ← measureType fuel limits environment stack span element
      let leaves := length * child.leaves
      let expandedNodes := 1 + length * child.expandedNodes
      let layoutNodes := 1 + child.layoutNodes
      checkedMeasure limits span leaves expandedNodes layoutNodes
    | .bytes length => do
      if length > limits.maxBytesLength then
        throw {span, message := "fixed-byte length exceeds local compiler limit"}
      let expandedNodes := length + 1
      checkedMeasure limits span length expandedNodes 1

def CompositeEnv.validate (limits : Limits) (environment : CompositeEnv) :
    Except LayoutDiagnostic CompositeEnv := do
  let limits ← limits.validate
  let environment ← validateDeclarations limits environment
  let fuel := limits.maxExpandedNodes + limits.maxVectorLength + limits.maxDeclarations + 1
  for id in declarationIds environment do
    let declarationType := if (findStruct environment id).isSome then
      CompositeType.structure id else CompositeType.enumeration id
    let _ ← measureType fuel limits environment [] (declarationSpan environment id) declarationType
  return environment

private def layoutType (fuel : Nat) (limits : Limits) (environment : CompositeEnv)
    (stack : List DeclId) (span : SourceSpan) (type : CompositeType) :
    Except LayoutDiagnostic Layout := do
  match fuel with
  | 0 => throw {span, message := "composite nesting exceeds local compiler limit"}
  | fuel + 1 => match type with
    | .unit => pure .unit
    | .scalar ty => do
      if ty.isJubjub || ty.isForeign then return .curve ty
      if isOpaqueType ty then return .opaque ty
      match validateScalarLayoutTy ty with
      | .ok _ => pure ()
      | .error message => throw {span, message}
      match scalarLeaf ty with
      | .ok leaf => return .scalar leaf
      | .error message => throw {span, message}
    | .tuple items => .tuple <$> items.mapM (layoutType fuel limits environment stack span)
    | .structure id => do
      if stack.contains id then throw {span, message := s!"recursive composite layout involving '{id}' is unsupported"}
      let some declaration := findStruct environment id
        | throw {span, message := s!"unknown structure '{id}'"}
      let fields ← declaration.fields.mapM fun field => do
        return (field.name, ← layoutType fuel limits environment (id :: stack) field.span field.type)
      return .structure id fields
    | .enumeration id => do
      if stack.contains id then throw {span, message := s!"recursive composite layout involving '{id}' is unsupported"}
      let some declaration := findEnum environment id
        | throw {span, message := s!"unknown enumeration '{id}'"}
      if declaration.variants.isEmpty then
        throw {span := declaration.span, message := "an enumeration must declare at least one variant"}
      let variants ← declaration.variants.mapM fun variant => do
        let fields ← variant.fields.mapM fun field => do
          return (field.name, ← layoutType fuel limits environment (id :: stack) field.span field.type)
        let leaves := fields.foldl (fun count field => count + field.2.leafCount) 0
        return (variant.name, fields, leaves)
      let payloadLeaves := variants.foldl (fun current variant => max current variant.2.2) 0
      let tagMaximum := declaration.variants.length - 1
      match ScalarPolicy.validate (.uint tagMaximum) with
      | .ok _ => pure ()
      | .error message => throw {span := declaration.span, message}
      return .enumeration id (.enumTagField tagMaximum) tagMaximum payloadLeaves
        .zeroPadToMaximum variants
    | .vector length element => do
      if length > limits.maxVectorLength then
        throw {span, message := "fixed-vector length exceeds local compiler limit"}
      return .vector length (← layoutType fuel limits environment stack span element)
    | .bytes length => do
      if length > limits.maxBytesLength then
        throw {span, message := "fixed-byte length exceeds local compiler limit"}
      return .bytes length .byteField

def checkedLayout (limits : Limits := defaultLimits) (environment : CompositeEnv)
    (type : CompositeType) (span : SourceSpan := {}) :
    Except LayoutDiagnostic (CheckedLayout limits) := do
  let environment ← environment.validate limits
  let fuel := limits.maxExpandedNodes + limits.maxVectorLength + limits.maxDeclarations + 1
  let measured ← measureType fuel limits environment [] span type
  let result ← layoutType fuel limits environment [] span type
  if h : result.leafCount = measured.leaves then
    if he : result.expandedNodeCount = measured.expandedNodes then
      if hn : result.nodeCount = measured.layoutNodes then
        return {
          value := result
          expandedLeaves := measured.leaves
          expandedNodes := measured.expandedNodes
          layoutNodes := measured.layoutNodes
          leafCountMatches := h
          expandedNodeCountMatches := he
          layoutNodeCountMatches := hn
          leafCountBound := measured.leafBound
          expandedNodeBound := measured.expandedNodeBound
          layoutNodeBound := measured.layoutNodeBound
        }
      else
        throw {span, message := "internal composite layout node-count mismatch"}
    else
      throw {span, message := "internal composite expanded-node-count mismatch"}
  else
    throw {span, message := "internal composite layout leaf-count mismatch"}

def layout (limits : Limits := defaultLimits) (environment : CompositeEnv)
    (type : CompositeType) (span : SourceSpan := {}) : Except LayoutDiagnostic Layout := do
  return (← checkedLayout limits environment type span).value

private def encodeNat (value : Nat) : String := s!"{value};"

private def encodeText (value : String) : String := s!"{value.length}:{value}"

private def encodeScalar : Ty → String
  | .native => "N"
  | .bool => "B"
  | .uint maximum => "U" ++ encodeNat maximum
  | .bytes length => "X" ++ encodeNat length
  | .opaqueBytes => "O"
  | .opaqueString => "S"
  | .jubjubScalar => "JS"
  | .jubjubPoint => "JP"
  | .foreign kind => "F" ++ toString kind.sourceName.length ++ ":" ++ kind.sourceName

mutual
  private def encodeType : CompositeType → String
    | .unit => "u"
    | .scalar ty => "s" ++ encodeScalar ty
    | .tuple items => "t" ++ encodeNat items.length ++ "[" ++ String.join (items.map encodeType) ++ "]"
    | .structure id => "r" ++ encodeText id
    | .enumeration id => "e" ++ encodeText id
    | .vector length element => "v" ++ encodeNat length ++ encodeType element
    | .bytes length => "b" ++ encodeNat length

  private def encodeField (field : Field) : String :=
    "f" ++ encodeText field.name ++ encodeType field.type

  private def encodeStruct (declaration : StructDecl) : String :=
    "R" ++ encodeText declaration.id ++ encodeNat declaration.fields.length ++
      String.join (declaration.fields.map encodeField)

  private def encodeVariant (variant : VariantDecl) : String :=
    "V" ++ encodeText variant.name ++ encodeNat variant.fields.length ++
      String.join (variant.fields.map encodeField)

  private def encodeEnum (declaration : EnumDecl) : String :=
    "E" ++ encodeText declaration.id ++ encodeNat declaration.variants.length ++
      String.join (declaration.variants.map encodeVariant)
end

private def stringLt (left right : String) : Bool := decide (left < right)

private def CompositeEnv.canonicalEncoding (environment : CompositeEnv) : String := Id.run do
  let structures := environment.structures.mergeSort fun left right => stringLt left.id right.id
  let enumerations := environment.enumerations.mergeSort fun left right => stringLt left.id right.id
  return "NoctiumCompositeLayoutV1;" ++
    encodeNat structures.length ++ String.join (structures.map encodeStruct) ++
    encodeNat enumerations.length ++ String.join (enumerations.map encodeEnum)

private def collectClosure (environment : CompositeEnv) (fuel : Nat)
    (pending seen : List DeclId) : List DeclId :=
  match fuel, pending with
  | 0, _ => seen
  | _, [] => seen
  | fuel + 1, id :: rest =>
    if seen.contains id then
      collectClosure environment fuel rest seen
    else
      let newReferences := (declarationReferences environment id).filter fun reference =>
        !seen.contains reference && !rest.contains reference
      collectClosure environment fuel (rest ++ newReferences) (id :: seen)

private def reachableEnvironment (environment : CompositeEnv) (type : CompositeType) : CompositeEnv := Id.run do
  let roots := type.referencedIds.eraseDups
  let edgeCount := (declarationIds environment).foldl
    (fun count id => count + (declarationReferences environment id).length) roots.length
  let reachable := collectClosure environment (edgeCount + roots.length + 1) roots []
  return {
    structures := environment.structures.filter fun declaration => reachable.contains declaration.id
    enumerations := environment.enumerations.filter fun declaration => reachable.contains declaration.id
  }

/-- Keep only the declarations reachable from one checked source-visible type.
This prevents unrelated declarations in a shared environment from crossing a
type import boundary. -/
def CompositeEnv.reachable (environment : CompositeEnv) (type : CompositeType) : CompositeEnv :=
  reachableEnvironment environment type

/-- The fingerprint is the full canonical descriptor encoding. It is injective
under the length-prefixed grammar and is deliberately not called a cryptographic hash. -/
def CompositeEnv.fingerprint (environment : CompositeEnv) : String :=
  environment.canonicalEncoding

def CompositeType.fingerprint (environment : CompositeEnv) (type : CompositeType) : String :=
  "NoctiumCompositeTypeV1;" ++ encodeType type ++
    (reachableEnvironment environment type).canonicalEncoding

theorem scalar_uint_subtype_iff (source target : Nat) :
    CompositeSubtype (.scalar (.uint source)) (.scalar (.uint target)) ↔
      source ≤ target ∧ target ≤ ScalarPolicy.maxUint := by
  constructor
  · intro proof
    cases proof with
    | unsigned bound supported => exact ⟨bound, supported⟩
  · intro bounds
    exact .unsigned bounds.1 bounds.2

theorem enum_tag_maximum_is_below_variant_count (variantCount : Nat)
    (nonempty : 0 < variantCount) : variantCount - 1 < variantCount := by omega

end Noctium.Types
