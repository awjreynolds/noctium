import Noctium.Frontend

open scoped Noctium
open Noctium
open Noctium.Helpers
open Noctium.Types

namespace NamedEnumMembers

private def recipientWire : Helpers.Wire.Codec := {
  payload := .enumeration "NamedEnumMembers.RecipientKind"
  frameBytes := 1
  composites := {enumerations := [{
    id := "NamedEnumMembers.RecipientKind"
    variants := [
      {name := "ShieldedUser"},
      {name := "UnshieldedUser"},
      {name := "Contract"}
    ]
  }]}
}

private def otherRecipientWire : Helpers.Wire.Codec := {
  payload := .enumeration "NamedEnumMembers.OtherRecipientKind"
  frameBytes := 1
  composites := {enumerations := [{
    id := "NamedEnumMembers.OtherRecipientKind"
    variants := [
      {name := "ShieldedUser"},
      {name := "UnshieldedUser"},
      {name := "Contract"}
    ]
  }]}
}

private def payloadRecipientWire : Helpers.Wire.Codec := {
  payload := .enumeration "NamedEnumMembers.PayloadRecipientKind"
  frameBytes := 33
  composites := {enumerations := [{
    id := "NamedEnumMembers.PayloadRecipientKind"
    variants := [
      {name := "ShieldedUser"},
      {name := "UnshieldedUser"},
      {name := "Contract", fields := [
        {name := "address", type := .bytes 32}
      ]}
    ]
  }]}
}

noctium_witness_circuit describe using recipientWire where
  public choice : Payload recipientWire
  output isContractValue : Bool := eq(choice, enumMember(recipientWire, Contract))
  output selectedTagValue : Native := enumTag(enumMember(recipientWire, Contract))
end

private def enumMemberEvalContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by named enum member fixture"
}

#guard match describe.run enumMemberEvalContext [("choice.$tag", .native 0)] with
  | .ok outputs => outputs == [
      ("result.isContractValue", .native 0),
      ("result.selectedTagValue", .native 2)]
  | .error _ => Bool.false

#guard match describe.run enumMemberEvalContext [("choice.$tag", .native 2)] with
  | .ok outputs => outputs == [
      ("result.isContractValue", .native 1),
      ("result.selectedTagValue", .native 2)]
  | .error _ => Bool.false

/- error: unknown enum member 'Missing' -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsMissingMember using recipientWire where
  output selectedTagValue : Native := enumTag(enumMember(recipientWire, Missing))
end

/- error: eq enum operands must have the same nominal type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsOtherNominalType using recipientWire, otherRecipientWire where
  public choice : Payload recipientWire
  output isContractValue : Bool := eq(choice, enumMember(otherRecipientWire, Contract))
end

/- error: expected a checked fieldless enum -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsPayloadVariant using payloadRecipientWire where
  output selectedTagValue : Native := enumTag(enumMember(payloadRecipientWire, Contract))
end

end NamedEnumMembers

noctium_contract NamedEnumMembers where
  entry describe uses NamedEnumMembers.describe where
    return isContract : Bool := isContractValue
    return selectedTag : Native := selectedTagValue
  end
end
