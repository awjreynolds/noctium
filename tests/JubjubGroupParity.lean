import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit jubjubGroupParityInputs where
  private pointX : Native
  private pointY : Native
  private rawScalar : Native
  let point : JubjubPoint := jubjubFromCoordinates(pointX, pointY)
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  let scalar : JubjubScalar := jubjubScalarFromNative(rawScalar)
  let generated : JubjubPoint := jubjubMulGenerator(scalar)
  let multiplied : JubjubPoint := jubjubMul(point, scalar)
  let sum : JubjubPoint := jubjubAdd(point, identity)
  let negated : JubjubPoint := jubjubNeg(point)
  let cancelled : JubjubPoint := jubjubAdd(point, negated)
  let identityNegated : JubjubPoint := jubjubNeg(identity)
  output checkedX : Native := disclose(jubjubX(point))
  output checkedY : Native := disclose(jubjubY(point))
  output generatorX : Native := disclose(jubjubX(generated))
  output generatorY : Native := disclose(jubjubY(generated))
  output multipliedX : Native := disclose(jubjubX(multiplied))
  output multipliedY : Native := disclose(jubjubY(multiplied))
  output sumX : Native := disclose(jubjubX(sum))
  output sumY : Native := disclose(jubjubY(sum))
  output negatedX : Native := disclose(jubjubX(negated))
  output negatedY : Native := disclose(jubjubY(negated))
  output cancelledX : Native := disclose(jubjubX(cancelled))
  output cancelledY : Native := disclose(jubjubY(cancelled))
  output identityNegatedX : Native := disclose(jubjubX(identityNegated))
  output identityNegatedY : Native := disclose(jubjubY(identityNegated))
  output scalarResult : Native := disclose(jubjubScalarToNative(scalar))
end

noctium_circuit jubjubPointProjectionInputs where
  private point : JubjubPoint
  output x : Native := disclose(jubjubX(point))
  output y : Native := disclose(jubjubY(point))
end

noctium_contract JubjubGroupParity where
  entry groupParity uses jubjubGroupParityInputs where
    return resultCheckedX : Native := checkedX
    return resultCheckedY : Native := checkedY
    return resultGeneratorX : Native := generatorX
    return resultGeneratorY : Native := generatorY
    return resultMultipliedX : Native := multipliedX
    return resultMultipliedY : Native := multipliedY
    return resultSumX : Native := sumX
    return resultSumY : Native := sumY
    return resultNegatedX : Native := negatedX
    return resultNegatedY : Native := negatedY
    return resultCancelledX : Native := cancelledX
    return resultCancelledY : Native := cancelledY
    return resultIdentityNegatedX : Native := identityNegatedX
    return resultIdentityNegatedY : Native := identityNegatedY
    return resultScalar : Native := scalarResult
  end
  entry project uses jubjubPointProjectionInputs where
    return resultX : Native := x
    return resultY : Native := y
  end
end

private def jubjubGroupParityEntry : Entrypoint :=
  match JubjubGroupParity.entrypoints with
  | entrypoint :: _ => entrypoint
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Native.expectedEntrypoint JubjubGroupParity.state jubjubGroupParityEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint JubjubGroupParity.state jubjubGroupParityEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false
