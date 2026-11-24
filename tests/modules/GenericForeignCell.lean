import Noctium.Frontend
import Noctium.Modules

open Noctium
open Noctium.Helpers.Specialization
open Noctium.Modules
open scoped Noctium

def genericForeignCellRead : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "read", result := .unit, body := [.return]}]
  exports := [{name := "read", target := ⟨0, 0⟩}]
}

def genericForeignCellUpdate : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    parameters := [⟨"T", .type⟩]
    values := [("next", .parameter "T")]
    result := .unit
    body := [.return]
  }]
  exports := [{
    name := "update"
    target := ⟨0, 0⟩
    inputs := [{name := "next", type := .parameter "T", visibility := .private}]
  }]
}

def genericForeignCellModule : Definition := {
  parameters := [⟨"T", .type⟩]
  members := [
    {id := 0, name := "value", kind := .state, visibility := .«public»,
      stateSchema? := some (.cell (.parameter "T"))},
    {id := 1, name := "readCircuit", kind := .circuit, sourceExport? := some {
      program := `genericForeignCellRead, exportName := "read"}},
    {id := 2, name := "read", kind := .entrypoint, visibility := .«public»},
    {id := 3, name := "updateCircuit", kind := .circuit, sourceExport? := some {
      program := `genericForeignCellUpdate, exportName := "update",
      arguments := [.typeParameter "T"]}},
    {id := 4, name := "update", kind := .entrypoint, visibility := .«public»}
  ]
  entrypoints := [
    {«member» := 2, name := "read", circuit := .localMember 1,
      cellReturns := [{name := "result", state := .localMember 0}]},
    {«member» := 4, name := "update", circuit := .localMember 3,
      effects := [{effect := .writeCellInput (.localMember 0) "next" (disclosed := Bool.true)}],
      cellReturns := [{name := "result", state := .localMember 0}]}
  ]
  exports := [
    {name := "value", target := .localMember 0},
    {name := "read", target := .localMember 2},
    {name := "update", target := .localMember 4}
  ]
}

noctium_module from genericForeignCellModule

def genericForeignCellRequest (kind : Foreign.Kind) : Request := {
  sourceName := `genericForeignCellModule
  arguments := [.type (.scalar (.foreign kind))]
  constructorInputs := [{state := .localMember 0, parameterName := "initial"}]
}

def k1Base := genericForeignCellRequest (.base .secp256k1)
def k1Scalar := genericForeignCellRequest (.scalar .secp256k1)
def k1Point := genericForeignCellRequest (.point .secp256k1)
def r1Base := genericForeignCellRequest (.base .secp256r1)
def r1Scalar := genericForeignCellRequest (.scalar .secp256r1)
def r1Point := genericForeignCellRequest (.point .secp256r1)
def c25519Base := genericForeignCellRequest (.base .curve25519)
def c25519Scalar := genericForeignCellRequest (.scalar .curve25519)
def c25519Point := genericForeignCellRequest (.point .curve25519)

noctium_module_contract GenericForeignCellSecp256k1Base from k1Base
noctium_module_contract GenericForeignCellSecp256k1Scalar from k1Scalar
noctium_module_contract GenericForeignCellSecp256k1Point from k1Point
noctium_module_contract GenericForeignCellSecp256r1Base from r1Base
noctium_module_contract GenericForeignCellSecp256r1Scalar from r1Scalar
noctium_module_contract GenericForeignCellSecp256r1Point from r1Point
noctium_module_contract GenericForeignCellCurve25519Base from c25519Base
noctium_module_contract GenericForeignCellCurve25519Scalar from c25519Scalar
noctium_module_contract GenericForeignCellCurve25519Point from c25519Point
