import LeanS7.Binary

/-!
# SHA-256 and HMAC-SHA256

A plain implementation of SHA-256 (FIPS 180-4) and HMAC (RFC 2104), for the V3
integrity tags of SessionKey sessions. It is checked against Python's `hashlib` and
`hmac` with known-answer vectors (`Tests.lean`); nothing here proves it equal to the
standard. It is not constant-time and is not meant for anything but this protocol
model.

`hashFrom` compresses padded data from any chaining state, with the message length
given separately. Real S7-1200/1500 firmware chains the HMAC tags of a fragmented
response by resuming finalized states this way (`LeanS7CommPlus.Integrity`); with the
initial state and the data's own length, it is ordinary SHA-256.
-/

namespace LeanS7CommPlus

open LeanS7

namespace Sha256

/-- A SHA-256 chaining state: eight 32-bit words. -/
structure State where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32
  h5 : UInt32
  h6 : UInt32
  h7 : UInt32
  deriving Repr, BEq, DecidableEq

def initial : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def rotr (value : UInt32) (count : UInt32) : UInt32 :=
  (value >>> count) ||| (value <<< (32 - count))

/-- The big-endian word at `offset`. -/
def word (data : ByteArray) (offset : Nat) : UInt32 :=
  (data.get! offset).toUInt32 <<< 24 ||| (data.get! (offset + 1)).toUInt32 <<< 16 |||
    (data.get! (offset + 2)).toUInt32 <<< 8 ||| (data.get! (offset + 3)).toUInt32

/-- The 64-word message schedule of the block at `offset`. -/
def schedule (data : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    w := w.push (word data (offset + 4 * i))
  for j in [16:64] do
    let a := w[j - 15]!
    let b := w[j - 2]!
    let s0 := rotr a 7 ^^^ rotr a 18 ^^^ (a >>> 3)
    let s1 := rotr b 17 ^^^ rotr b 19 ^^^ (b >>> 10)
    w := w.push (w[j - 16]! + s0 + w[j - 7]! + s1)
  return w

/-- Compress the 64-byte block at `offset` into the state. -/
def compress (state : State) (data : ByteArray) (offset : Nat) : State := Id.run do
  let w := schedule data offset
  let mut a := state.h0
  let mut b := state.h1
  let mut c := state.h2
  let mut d := state.h3
  let mut e := state.h4
  let mut f := state.h5
  let mut g := state.h6
  let mut h := state.h7
  for j in [0:64] do
    let t1 := h + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ ((~~~e) &&& g)) +
      roundConstants[j]! + w[j]!
    let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return ⟨state.h0 + a, state.h1 + b, state.h2 + c, state.h3 + d,
    state.h4 + e, state.h5 + f, state.h6 + g, state.h7 + h⟩

/-- The number of zero bytes that pad `length` data bytes, the `0x80` byte and the
    8-byte length to a whole number of blocks. -/
def zeroCount (length : Nat) : Nat := (119 - length % 64) % 64

/-- `data`, the `0x80` byte, zeros, and `total` as a 64-bit bit count. The padding
    depends on `data` only; `total` may count earlier, already compressed bytes. -/
def pad (data : ByteArray) (total : Nat) : ByteArray :=
  data ++ bytes #[0x80] ++ ByteArray.mk (Array.replicate (zeroCount data.size) 0) ++
    uint64BE (UInt64.ofNat (total * 8))

/-- Compress `pad data total` from `state`. -/
def hashFrom (state : State) (data : ByteArray) (total : Nat) : State :=
  let padded := pad data total
  (List.range (padded.size / 64)).foldl (fun state block => compress state padded (64 * block)) state

def State.digest (state : State) : ByteArray :=
  uint32BE state.h0 ++ uint32BE state.h1 ++ uint32BE state.h2 ++ uint32BE state.h3 ++
    uint32BE state.h4 ++ uint32BE state.h5 ++ uint32BE state.h6 ++ uint32BE state.h7

def hash (data : ByteArray) : ByteArray := (hashFrom initial data data.size).digest

theorem State.digest_size (state : State) : state.digest.size = 32 := by
  simp [State.digest, ByteArray.size_append, uint32BE_size]

theorem hash_size (data : ByteArray) : (hash data).size = 32 := State.digest_size _

/-- The padding fills whole blocks. -/
theorem pad_size (data : ByteArray) (total : Nat) : (pad data total).size % 64 = 0 := by
  have hz : (ByteArray.mk (Array.replicate ((119 - data.size % 64) % 64) 0)).size =
      (119 - data.size % 64) % 64 := Array.size_replicate
  simp only [pad, zeroCount, ByteArray.size_append, bytes_size, uint64BE_size, List.size_toArray,
    List.length_cons, List.length_nil]
  rw [hz]
  omega

end Sha256

/-! ## SHA-1

Only for the password hash of the SessionKey legitimation, where the protocol fixes it. -/

namespace Sha1

def rotl (value : UInt32) (count : UInt32) : UInt32 :=
  (value <<< count) ||| (value >>> (32 - count))

def compress (state : Array UInt32) (data : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 80
  for i in [0:16] do
    w := w.push (Sha256.word data (offset + 4 * i))
  for i in [16:80] do
    w := w.push (rotl (w[i - 3]! ^^^ w[i - 8]! ^^^ w[i - 14]! ^^^ w[i - 16]!) 1)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  for i in [0:80] do
    let (f, k) : UInt32 × UInt32 :=
      if i < 20 then ((b &&& c) ||| ((~~~b) &&& d), 0x5a827999)
      else if i < 40 then (b ^^^ c ^^^ d, 0x6ed9eba1)
      else if i < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8f1bbcdc)
      else (b ^^^ c ^^^ d, 0xca62c1d6)
    let t := rotl a 5 + f + e + k + w[i]!
    e := d
    d := c
    c := rotl b 30
    b := a
    a := t
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d, state[4]! + e]

def hash (data : ByteArray) : ByteArray :=
  let padded := Sha256.pad data data.size
  let state := (List.range (padded.size / 64)).foldl (fun state block => compress state padded (64 * block))
    #[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
  state.foldl (fun acc word => acc ++ uint32BE word) ByteArray.empty

end Sha1

/-! ## HMAC-SHA256 -/

namespace Hmac

open Sha256

/-- The key as one block: hashed if longer than a block, then padded with zeros. -/
def blockKey (key : ByteArray) : ByteArray :=
  let key := if key.size > 64 then Sha256.hash key else key
  key ++ ByteArray.mk (Array.replicate (64 - key.size) 0)

def xorPad (key : ByteArray) (byte : UInt8) : ByteArray :=
  ByteArray.mk ((blockKey key).data.map (· ^^^ byte))

def innerPad (key : ByteArray) : ByteArray := xorPad key 0x36
def outerPad (key : ByteArray) : ByteArray := xorPad key 0x5c

def sha256 (key message : ByteArray) : ByteArray :=
  Sha256.hash (outerPad key ++ Sha256.hash (innerPad key ++ message))

theorem blockKey_size (key : ByteArray) : (blockKey key).size = 64 := by
  unfold blockKey
  split
  · rename_i h
    have hz : (ByteArray.mk (Array.replicate (64 - (Sha256.hash key).size) (0 : UInt8))).size =
        64 - (Sha256.hash key).size := Array.size_replicate
    rw [ByteArray.size_append, hz, Sha256.hash_size]
  · rename_i h
    have hz : (ByteArray.mk (Array.replicate (64 - key.size) (0 : UInt8))).size = 64 - key.size :=
      Array.size_replicate
    rw [ByteArray.size_append, hz]
    omega

theorem xorPad_size (key : ByteArray) (byte : UInt8) : (xorPad key byte).size = 64 := by
  have h := blockKey_size key
  simp only [xorPad, ByteArray.size, Array.size_map] at h ⊢
  exact h

theorem sha256_size (key message : ByteArray) : (sha256 key message).size = 32 := hash_size _

end Hmac

end LeanS7CommPlus
