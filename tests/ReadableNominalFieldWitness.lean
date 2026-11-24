import Noctium.Authoring

open scoped Noctium
open Noctium

namespace ReadableNominalFieldWitness

noctium_field_type Amount := Field
noctium_field_type Count := Field

noctium_witness amountProvider(amount : Amount) : Amount

noctium_witness_circuit amountWitness where
  public prior : Amount
  let received := witness amountProvider(prior)
  let total := add(prior, received)
  output result : Amount := disclose(total)
end

noctium_witness_circuit acceptsExplicitNativeWitnessArgument where
  private raw : Native
  let received := witness amountProvider(cast(Amount, raw))
  output result : Amount := disclose(received)
end

noctium_contract AmountWitnessContract where
  entry accept uses amountWitness where
    return returned : Native := cast(Native, result)
  end
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsImplicitNativeWitnessResult where
  private amount : Amount
  let received := witness amountProvider(amount)
  output total : Native := received
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsDistinctAliasWitnessResult where
  private amount : Amount
  let received := witness amountProvider(amount)
  output total : Count := received
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsImplicitNativeWitnessArgument where
  private raw : Native
  let received := witness amountProvider(raw)
  output result : Amount := disclose(received)
end

/- error: nominal Field values require an explicit cast and must match the target type -/
#guard_msgs (substring := true) in
noctium_witness_circuit rejectsDistinctAliasWitnessArgument where
  private count : Count
  let received := witness amountProvider(count)
  output result : Amount := disclose(received)
end

end ReadableNominalFieldWitness
