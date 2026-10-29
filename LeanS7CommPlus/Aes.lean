import LeanS7.Binary
import LeanS7CommPlus.SessionKey

/-!
# AES-128

AES-128 encryption of one block (FIPS-197), for the ECB blocks of the SessionKey blob
and the GCM-style legitimation answer. Decryption is not needed. Checked against the
FIPS-197 appendix C.1 vector and against Python's `cryptography` (`Tests.lean`). Not
constant-time; this is a protocol model, not a cryptographic library.
-/

namespace LeanS7CommPlus

namespace Aes

/-- The S-box, computed from its definition (multiplicative inverse in GF(2⁸) and the
    affine map) when this table was generated. -/
def sbox : ByteArray := (hexToBytes? "637c777bf26b6fc53001672bfed7ab76ca82c97dfa5947f0add4a2af9ca472c0b7fd9326363ff7cc34a5e5f171d8311504c723c31896059a071280e2eb27b27509832c1a1b6e5aa0523bd6b329e32f8453d100ed20fcb15b6acbbe394a4c58cfd0efaafb434d338545f9027f503c9fa851a3408f929d38f5bcb6da2110fff3d2cd0c13ec5f974417c4a77e3d645d197360814fdc222a908846eeb814de5e0bdbe0323a0a4906245cc2d3ac629195e479e7c8376d8dd54ea96c56f4ea657aae08ba78252e1ca6b4c6e8dd741f4bbd8b8a703eb5664803f60e613557b986c11d9ee1f8981169d98e949b1e87e9ce5528df8ca1890dbfe6426841992d0fb054bb16").getD ByteArray.empty

def sub (byte : UInt8) : UInt8 := sbox.get! byte.toNat

/-- Multiplication by x in GF(2⁸). -/
def xtime (byte : UInt8) : UInt8 :=
  if byte &&& 0x80 = 0 then byte <<< 1 else (byte <<< 1) ^^^ 0x1b

/-- The 176 bytes of the 11 round keys of a 16-byte key. -/
def expandKey (key : ByteArray) : ByteArray := Id.run do
  let mut w := key.extract 0 16
  let mut rcon : UInt8 := 1
  for i in [4:44] do
    let t0 := w.get! (4 * (i - 1))
    let t1 := w.get! (4 * (i - 1) + 1)
    let t2 := w.get! (4 * (i - 1) + 2)
    let t3 := w.get! (4 * (i - 1) + 3)
    let (t0, t1, t2, t3) :=
      if i % 4 = 0 then (sub t1 ^^^ rcon, sub t2, sub t3, sub t0) else (t0, t1, t2, t3)
    if i % 4 = 0 then rcon := xtime rcon
    w := w.push (w.get! (4 * (i - 4)) ^^^ t0)
    w := w.push (w.get! (4 * (i - 4) + 1) ^^^ t1)
    w := w.push (w.get! (4 * (i - 4) + 2) ^^^ t2)
    w := w.push (w.get! (4 * (i - 4) + 3) ^^^ t3)
  return w

def addRoundKey (state : Array UInt8) (keys : ByteArray) (round : Nat) : Array UInt8 :=
  (List.range 16).toArray.map fun i => state[i]! ^^^ keys.get! (16 * round + i)

/-- SubBytes and ShiftRows: byte `r + 4c` of the result is S(byte `r + 4(c + r)`). -/
def subShift (state : Array UInt8) : Array UInt8 :=
  (List.range 16).toArray.map fun i =>
    let row := i % 4
    let column := i / 4
    sub state[row + 4 * ((column + row) % 4)]!

def mixColumns (state : Array UInt8) : Array UInt8 :=
  (List.range 16).toArray.map fun i =>
    let row := i % 4
    let base := 4 * (i / 4)
    let a (k : Nat) := state[base + (row + k) % 4]!
    xtime (a 0) ^^^ (xtime (a 1) ^^^ a 1) ^^^ a 2 ^^^ a 3

/-- Encrypt one 16-byte block under a 16-byte key. -/
def encryptBlock (key block : ByteArray) : ByteArray := Id.run do
  let keys := expandKey key
  let mut state := addRoundKey ((List.range 16).toArray.map fun i => block.get! i) keys 0
  for round in [1:10] do
    state := addRoundKey (mixColumns (subShift state)) keys round
  state := addRoundKey (subShift state) keys 10
  return ByteArray.mk state

end Aes

end LeanS7CommPlus
