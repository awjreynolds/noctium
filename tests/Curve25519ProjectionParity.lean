import Noctium.Frontend

open scoped Noctium

noctium_circuit curve25519ProjectionInputs where
  public point : Curve25519Point
end

noctium_contract Curve25519ProjectionParity where
  entry project uses curve25519ProjectionInputs where
    return x : Curve25519Base := disclose(curveX(point))
    return y : Curve25519Base := disclose(curveY(point))
  end
end
