namespace Noctium.EntryPointHash

private def initial : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

private def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def rotateRight (word amount : UInt32) : UInt32 :=
  (word >>> amount) ||| (word <<< (32 - amount))

private def bigEndian (width value : Nat) : List Nat :=
  (List.range width).reverse.map fun index => (value >>> (8 * index)) &&& 255

-- FIPS 180-4 SHA-256 for compile-time public artifacts and operation names.
private def sha256 (input : Array Nat) : List Nat := Id.run do
  let zeros := (119 - input.size % 64) % 64
  let message := input.push 128 ++ (List.replicate zeros 0).toArray ++ (bigEndian 8 (input.size * 8)).toArray
  let mut state := initial
  for block in [0:message.size / 64] do
    let mut words : Array UInt32 := #[]
    for index in [0:16] do
      let offset := block * 64 + index * 4
      let mut word : UInt32 := 0
      for octet in [0:4] do
        word := (word <<< 8) ||| UInt32.ofNat message[offset + octet]!
      words := words.push word
    for index in [16:64] do
      let x := words[index - 15]!
      let y := words[index - 2]!
      let small0 := rotateRight x 7 ^^^ rotateRight x 18 ^^^ (x >>> 3)
      let small1 := rotateRight y 17 ^^^ rotateRight y 19 ^^^ (y >>> 10)
      words := words.push (words[index - 16]! + small0 + words[index - 7]! + small1)
    let mut work := state
    for index in [0:64] do
      let a := work[0]!
      let b := work[1]!
      let c := work[2]!
      let d := work[3]!
      let e := work[4]!
      let f := work[5]!
      let g := work[6]!
      let h := work[7]!
      let choose := (e &&& f) ^^^ (~~~e &&& g)
      let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let large0 := rotateRight a 2 ^^^ rotateRight a 13 ^^^ rotateRight a 22
      let large1 := rotateRight e 6 ^^^ rotateRight e 11 ^^^ rotateRight e 25
      let temp := h + large1 + choose + roundConstants[index]! + words[index]!
      work := #[temp + large0 + majority, a, b, c, d + temp, e, f, g]
    state := (state.zip work).map fun (x, y) => x + y
  return state.toList.flatMap (bigEndian 4 ·.toNat)

/-- The 32 digest bytes in SHA-256 output order. -/
def sha256Bytes (bytes : ByteArray) : List UInt8 :=
  (sha256 (bytes.data.map UInt8.toNat)).map UInt8.ofNat

def sha256Hex (bytes : ByteArray) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList <| (sha256 (bytes.data.map UInt8.toNat)).flatMap fun byte =>
    [digits[byte / 16]!, digits[byte % 16]!]

/-- Midnight hashes a 32-byte domain followed by the exact UTF-8 entrypoint bytes. -/
def hash (operation : String) : List Nat :=
  let domain := "midnight:entry-point".toUTF8.data.map UInt8.toNat
  sha256 (domain ++ (List.replicate (32 - domain.size) 0).toArray ++ operation.toUTF8.data.map UInt8.toNat)

end Noctium.EntryPointHash
