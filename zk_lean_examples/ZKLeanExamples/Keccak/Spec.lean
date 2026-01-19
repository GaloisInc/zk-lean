
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

/-- Pi step: A'[x, y] = A[(x + 3y) mod 5, x] --/
def pi (s : State) : State :=
  let lanes := Vector.ofFn fun (i : Fin 25) =>
    let x := i.val % 5
    let y := i.val / 5
    -- Source coordinates: srcX = (x + 3*y) mod 5, srcY = x
    let srcX := (x + 3 * y) % 5
    let srcY := x
    s.lanes[srcY * 5 + srcX]!
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

/-- Load 8 bytes in little-endian order into a UInt64 --/
def loadLittleEndian (bytes : ByteArray) (offset : Nat) : UInt64 :=
  let b0 := if offset < bytes.size then bytes.get! offset else 0
  let b1 := if offset + 1 < bytes.size then bytes.get! (offset + 1) else 0
  let b2 := if offset + 2 < bytes.size then bytes.get! (offset + 2) else 0
  let b3 := if offset + 3 < bytes.size then bytes.get! (offset + 3) else 0
  let b4 := if offset + 4 < bytes.size then bytes.get! (offset + 4) else 0
  let b5 := if offset + 5 < bytes.size then bytes.get! (offset + 5) else 0
  let b6 := if offset + 6 < bytes.size then bytes.get! (offset + 6) else 0
  let b7 := if offset + 7 < bytes.size then bytes.get! (offset + 7) else 0
  b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
  (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)

/-- Absorb a block into the state --/
def absorb (s : State) (block : ByteArray) (rate : Nat) : State :=
  let lanes := s.lanes.mapIdx fun i lane =>
    let byteIdx := i * 8
    if byteIdx + 8 <= rate then
      let value := loadLittleEndian block byteIdx
      lane ^^^ BitVec.ofNat 64 value.toNat
    else
      lane
  keccakF { lanes := lanes }

/-- Pad message using pad10*1 rule for SHA3 --/
def pad101 (msg : ByteArray) (rate : Nat) : ByteArray :=
  let msgLen := msg.size
  let blockSize := rate
  -- Calculate how many bytes we need to add to reach the next block boundary
  let padLen := blockSize - (msgLen % blockSize)
  -- If only 1 byte needed, use 0x06 | 0x80 = 0x86
  if padLen == 1 then
    msg.push 0x86
  else
    -- First byte is 0x06 (SHA3 domain separator)
    -- Last byte is 0x80
    -- Middle bytes (if any) are 0x00
    let padded := msg.push 0x06
    let padded := (Array.range (padLen - 2)).foldl (fun acc _ => acc.push 0x00) padded
    padded.push 0x80

/-- Extract bytes from a lane in little-endian order --/
def extractLaneBytes (lane : BitVec 64) (numBytes : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn fun (i : Fin 8) =>
    if i.val < numBytes then
      ((lane >>> (i.val * 8)).toNat &&& 0xFF).toUInt8
    else
      0) |>.extract 0 numBytes

/-- Squeeze output from state (rate = 136 bytes = 17 lanes for SHA3-256) --/
def squeeze (s : State) (outLen : Nat) : ByteArray :=
  let rate := 136  -- rate in bytes
  let rateLanes := rate / 8  -- 17 lanes
  let rec aux (st : State) (remaining : Nat) (acc : ByteArray) (laneIdx : Nat) : ByteArray :=
    if remaining == 0 then acc
    else if laneIdx >= rateLanes then
      -- Need more bytes but exhausted rate, apply keccakF and restart from lane 0
      aux (keccakF st) remaining acc 0
    else
      let bytesToExtract := min remaining 8
      -- Lanes are stored as y*5 + x, and we read them in order (0,0), (1,0), (2,0), ...
      let x := laneIdx % 5
      let y := laneIdx / 5
      let lane := st.get ⟨x, by omega⟩ ⟨y, by omega⟩
      let bytes := extractLaneBytes lane bytesToExtract
      let acc' := acc ++ bytes
      aux st (remaining - bytesToExtract) acc' (laneIdx + 1)
  termination_by (remaining, rateLanes - laneIdx)
  aux s outLen ByteArray.empty 0

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

-- ============================================================================
-- Unit Tests for SHA3-256
-- ============================================================================

namespace SHA3.Tests

/-- Convert a hex string to ByteArray --/
def hexToByteArray (hex : String) : ByteArray :=
  let chars := hex.toList
  let rec aux (cs : List Char) (acc : ByteArray) : ByteArray :=
    match cs with
    | [] => acc
    | c1 :: c2 :: rest =>
      let hexDigit (c : Char) : Nat :=
        if c >= '0' && c <= '9' then c.toNat - '0'.toNat
        else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
        else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
        else 0
      let byte := (hexDigit c1 * 16 + hexDigit c2).toUInt8
      aux rest (acc.push byte)
    | _ :: rest => aux rest acc
  aux chars ByteArray.empty

/-- Expected SHA3-256 hash of empty string --/
def expectedEmptyHash : String :=
  "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"

/-- Expected SHA3-256 hash of "abc" --/
def expectedAbcHash : String :=
  "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"

/-- Expected SHA3-256 hash of 200 repetitions of byte 0xa3 (from NIST test vectors) --/
def expectedA3x200Hash : String :=
  "79f38adec5c20307a98ef76e8324afbfd46cfd81b22e3973c65fa1bd9de31787"

/-- Test SHA3-256 on empty string --/
def testEmpty : IO Bool := do
  let msg := "".toUTF8
  let hash := SHA3.sha3_256 msg
  let expected := hexToByteArray expectedEmptyHash
  let result := hash == expected
  IO.println s!"Test empty string: {if result then "PASS" else "FAIL"}"
  IO.println s!"  Expected: {expectedEmptyHash}"
  IO.println s!"  Got:      {SHA3.ByteArray.toHex hash}"
  return result

/-- Test SHA3-256 on "abc" --/
def testAbc : IO Bool := do
  let msg := "abc".toUTF8
  let hash := SHA3.sha3_256 msg
  let expected := hexToByteArray expectedAbcHash
  let result := hash == expected
  IO.println s!"Test 'abc': {if result then "PASS" else "FAIL"}"
  IO.println s!"  Expected: {expectedAbcHash}"
  IO.println s!"  Got:      {SHA3.ByteArray.toHex hash}"
  return result

/-- Test SHA3-256 on 200 bytes of 0xa3 --/
def testA3x200 : IO Bool := do
  let msg := ByteArray.mk (Array.mkArray 200 0xa3)
  let hash := SHA3.sha3_256 msg
  let expected := hexToByteArray expectedA3x200Hash
  let result := hash == expected
  IO.println s!"Test 200x0xa3: {if result then "PASS" else "FAIL"}"
  IO.println s!"  Expected: {expectedA3x200Hash}"
  IO.println s!"  Got:      {SHA3.ByteArray.toHex hash}"
  return result

/-- Run all SHA3-256 tests --/
def runAllTests : IO UInt32 := do
  IO.println "Running SHA3-256 Tests..."
  IO.println "========================="
  let r1 ← testEmpty
  let r2 ← testAbc
  let r3 ← testA3x200
  IO.println "========================="
  let passed := [r1, r2, r3].filter id |>.length
  let total := 3
  IO.println s!"Results: {passed}/{total} tests passed"
  return if passed == total then 0 else 1

end SHA3.Tests

/-- Example usage --/
def main : IO UInt32 := SHA3.Tests.runAllTests

#eval main


