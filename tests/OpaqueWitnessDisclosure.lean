import Noctium.Frontend

open scoped Noctium

namespace OpaqueWitnessDisclosure

noctium_witness readPrivateLabel() : OpaqueString

noctium_witness_circuit discloseLabel where
  let label := witness readPrivateLabel()
  output disclosedLabel : OpaqueString := disclose(label)
end

noctium_contract OpaqueWitnessDisclosure where
  cell label : OpaqueString
  entry publish uses OpaqueWitnessDisclosure.discloseLabel where
    write label := disclosedLabel
  end
end

/-- undisclosed private provider result 'OpaqueWitnessDisclosure.readPrivateLabel' -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsUndisclosedLabel where
  let label := witness OpaqueWitnessDisclosure.readPrivateLabel()
  output undisclosedLabel : OpaqueString := label
end

noctium_circuit privateCellWrite where
  private secretLabel : OpaqueString
end

/-- undisclosed private parameter 'secretLabel' -/
#guard_msgs (substring := true) in
noctium_contract UndisclosedOpaqueWitnessWrite where
  cell label : OpaqueString
  entry publish uses privateCellWrite where
    write label := secretLabel
  end
end

end OpaqueWitnessDisclosure
