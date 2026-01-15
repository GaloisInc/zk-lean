
-- SHA3-256 Implementation in Lean4 using BitVec
-- Based on FIPS 202 specification

namespace SHA3

/-- Round constants for Keccak-f[1600] --/
def roundConstants : Array (BitVec 64) :=
  #[0x0000000000000001#64, 0x0000000000008082#64, 0x800000000000808a#64,
    0x8000000080008000#64, 0x000000000000808b#64, 0x0000000080000001#64,
    0x8000000080008081#64, 0x8000000000008009#64, 0x000000000000008a#64,
    0x0000000000000088#64, 0x0000000080008009#64, 0x000000008000000a#64,
    0x000000008000808b#64, 0x800000000000008b#64, 0x8000000000008089#64,
    0x8000000000008003#64, 0x8000000000008002#64, 0x8000000000000080#64,
    0x000000000000800a#64, 0x800000008000000a#64, 0x8000000080008081#64,
    0x8000000000008080#64, 0x0000000080000001#64, 0x8000000080008008#64]

/-- Rotation offsets for Keccak --/
def rotationOffsets : Array Nat :=
  #[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43,
    25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- State type: 5x5 array of 64-bit lanes --/
structure State where
  lanes : Vector (BitVec 64) 25

/-- Create initial state --/
def State.init : State :=
  { lanes := Vector.replicate 25 0#64 }

/-- Get lane at position (x, y) --/
def State.get (s : State) (x y : Fin 5) : BitVec 64 :=
  s.lanes[y.val * 5 + x.val]

/-- Set lane at position (x, y) --/
def State.set (s : State) (x y : Fin 5) (val : BitVec 64) : State :=
  { lanes := s.lanes.set! (y.val * 5 + x.val) val }

/-- Theta step --/
def theta (s : State) : State :=
  let c := Vector.ofFn fun (x : Fin 5) =>
    s.get x 0 ^^^ s.get x 1 ^^^ s.get x 2 ^^^ s.get x 3 ^^^ s.get x 4
  let d := Vector.ofFn fun (x : Fin 5) =>
    c[(x.val + 4) % 5]! ^^^ (c[(x.val + 1) % 5]!).rotateLeft 1
  let lanes := Vector.ofFn fun (i : Fin 25) =>
    let x := i.val % 5
    let y := i.val / 5
    s.lanes[i]! ^^^ d[x]!
  { lanes := lanes }

/-- Rho step --/
def rho (s : State) : State :=
  let lanes := Vector.ofFn fun (i : Fin 25) =>
    (s.lanes[i]!).rotateLeft (rotationOffsets[i]!)
  { lanes := lanes }

/-- Pi step --/
def pi (s : State) : State :=
  let lanes := Vector.ofFn fun (i : Fin 25) =>
    let x := i.val % 5
    let y := i.val / 5
    let newX := y
    let newY := (2 * x + 3 * y) % 5
    s.lanes[newY * 5 + newX]!
  { lanes := lanes }

/-- Chi step --/
def chi (s : State) : State :=
  let lanes := Vector.ofFn fun (i : Fin 25) =>
    let x := i.val % 5
    let y := i.val / 5
    let lane := s.get ⟨x, by omega⟩ ⟨y, by omega⟩
    let next := s.get ⟨(x + 1) % 5, by omega⟩ ⟨y, by omega⟩
    let next2 := s.get ⟨(x + 2) % 5, by omega⟩ ⟨y, by omega⟩
    lane ^^^ ((~~~next) &&& next2)
  { lanes := lanes }

/-- Iota step --/
def iota (s : State) (round : Fin 24) : State :=
  let lane0 := s.get 0 0 ^^^ roundConstants[round.val]
  s.set 0 0 lane0

/-- Single round of Keccak-f[1600] --/
def keccakRound (s : State) (round : Fin 24) : State :=
  s |> theta |> rho |> pi |> chi |> (iota · round)

/-- Full Keccak-f[1600] permutation (24 rounds) --/
def keccakF (s : State) : State :=
  (Array.finRange 24).foldl (fun acc i => keccakRound acc i) s

/-- Absorb a block into the state --/
def absorb (s : State) (block : ByteArray) (rate : Nat) : State :=
  let lanes := s.lanes.mapIdx fun i lane =>
    let byteIdx := i * 8
    if byteIdx + 8 <= rate then
      let bytes := block.extract byteIdx (byteIdx + 8)
      let value := bytes.foldl (fun (acc:UInt64) b => (acc <<< 8) ||| b.toUInt64) 0
      lane ^^^ BitVec.ofNat 64 value.toNat
    else
      lane
  keccakF { lanes := lanes }

/-- Pad message using pad10*1 rule --/
def pad101 (msg : ByteArray) (rate : Nat) : ByteArray :=
  let msgLen := msg.size
  let blockSize := rate
  let padLen := blockSize - (msgLen % blockSize)
  let padLen := if padLen == 0 then blockSize else padLen
  let padded := msg.push 0x06  -- SHA3 domain separator
  let padded := if padLen > 1 then
    (Array.range (padLen - 1)).foldl (fun acc _ => acc.push 0x00) padded
  else
    padded
  padded.push 0x80

/-- Squeeze output from state --/
def squeeze (s : State) (outLen : Nat) : ByteArray :=
  let rec aux (st : State) (remaining : Nat) (acc : ByteArray) : ByteArray :=
    if remaining == 0 then acc
    else
      let bytesToExtract := min remaining 8
      let lane := st.get 0 0
      let bytes := ByteArray.mk (Array.ofFn fun (i : Fin 8) =>
        if i.val < bytesToExtract then
          ((lane >>> (i.val * 8)).toNat &&& 0xFF).toUInt8
        else
          0)
      let acc' := acc ++ bytes.extract 0 bytesToExtract
      if remaining <= 8 then
        acc'
      else
        aux (keccakF st) (remaining - bytesToExtract) acc'
  termination_by remaining
  aux s outLen ByteArray.empty

/-- SHA3-256 hash function --/
def sha3_256 (msg : ByteArray) : ByteArray :=
  let rate := 136  -- (1600 - 2*256) / 8
  let padded := pad101 msg rate
  let blocks := (padded.size + rate - 1) / rate
  let state := (Array.range blocks).foldl (fun s i =>
    let start := i * rate
    let blockEnd := min (start + rate) padded.size
    let block := padded.extract start blockEnd
    absorb s block rate
  ) State.init
  squeeze state 32

/-- Convert ByteArray to hex string --/
def ByteArray.toHex (ba : ByteArray) : String :=
  ba.foldl (fun acc b =>
    let hi := (b.toNat >>> 4) &&& 0xF
    let lo := b.toNat &&& 0xF
    let hiChar := if hi < 10 then Char.ofNat (hi + 48) else Char.ofNat (hi + 87)
    let loChar := if lo < 10 then Char.ofNat (lo + 48) else Char.ofNat (lo + 87)
    acc.push hiChar |>.push loChar
  ) ""

end SHA3

/-- Example usage --/
def main : IO Unit := do
  let msg := "abc".toUTF8
  let hash := SHA3.sha3_256 msg
  IO.println s!"SHA3-256('abc') = {SHA3.ByteArray.toHex hash}"
  
  let msg2 := "".toUTF8
  let hash2 := SHA3.sha3_256 msg2
  IO.println s!"SHA3-256('') = {SHA3.ByteArray.toHex hash2}"

#eval main


