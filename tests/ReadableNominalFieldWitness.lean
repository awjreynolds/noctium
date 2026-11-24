import Noctium.Authoring

open scoped Noctium
open Noctium

namespace ReadableNominalFieldWitness

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_witness amountProvider() : Amount

noctium_witness_circuit amountWitness where
  public prior : Amount
  let received := witness amountProvider()
  let total := add(prior, received)
  output result : Amount := disclose(total)
end

noctium_contract AmountWitnessContract where
  entry accept uses amountWitness where
    return returned : Native := cast(Native, result)
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsImplicitNativeWitnessResult where
  let received := witness amountProvider()
  output total : Native := received
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsDistinctAliasWitnessResult where
  let received := witness amountProvider()
  output total : Count := received
end

end ReadableNominalFieldWitness
