import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit jubjubListMaybeInputs where
  private scalar : JubjubScalar
  private point : JubjubPoint
end

noctium_circuit jubjubListMaybeNoInputs where
end

noctium_contract JubjubListMaybe where
  list scalars : JubjubScalar
  list points : JubjubPoint

  entry append uses jubjubListMaybeInputs where
    pushFront scalars := disclose(scalar)
    pushFront points := disclose(point)
    headOrDefault scalars as (scalarPresent, scalarHead)
    headOrDefault points as (pointPresent, pointHead)
    returnMaybe scalarMaybe as (scalarPresent, scalarHead)
    returnMaybe pointMaybe as (pointPresent, pointHead)
  end

  entry inspect uses jubjubListMaybeNoInputs where
    headOrDefault scalars as (scalarPresent, scalarHead)
    headOrDefault points as (pointPresent, pointHead)
    returnMaybe scalarMaybe as (scalarPresent, scalarHead)
    returnMaybe pointMaybe as (pointPresent, pointHead)
  end
end
