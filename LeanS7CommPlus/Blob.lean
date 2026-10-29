import LeanS7CommPlus.Aes
import LeanS7CommPlus.KeyDerivation

/-!
# The SessionKey blob for real controllers (families 00 and 01)

The 180-byte SecurityKeyEncryptedKey blob, ported from s7commplus
`v1_session_key/real_plc/` and `blob_metadata.py`, a port of HarpoS7's
`RealPlcAuthenticator` (MIT, see `LICENSE-HarpoS7`). s7commplus recovered HarpoS7's
transpiled transforms as known primitives:

- `Present`: PRESENT-80 (standard S-box and P-layer, 31 rounds) on byte-reversed
  blocks, with three fixed deviations in the key schedule;
- `Curve`: an x-only Montgomery ladder on `y² = x³ − x + B` over GF(2¹⁶⁰ − 47), an
  ECDH with the controller's public key;
- `Checksum`: multiplication in GF(2)[x] modulo x¹²⁸ + x³² + x¹⁵ + x² + 1;
- AES-128 in ECB for a GCM-like encryption of the challenge and key2.

The blob: a 48-byte header (magic, length, key ids and flags), the 60-byte seed
(masked pre-seed, ephemeral x, blinding bytes), the IV, the encrypted challenge and
key2 (40 bytes), and the encrypted checksum. `buildRealPlcBlob` is a pure function of
the five random draws; the client draws them with `IO.getRandomBytes`. Constants are
generated from the s7commplus modules. Everything is checked against s7commplus with
known-answer vectors (`Tests.lean`); nothing here is proved equal to HarpoS7.
-/

namespace LeanS7CommPlus

/-- A little-endian byte string as a number. -/
def leNat (data : ByteArray) : Nat :=
  data.toList.foldr (fun byte acc => acc * 256 + byte.toNat) 0

/-- A number as `count` little-endian bytes. -/
def natLe (count value : Nat) : ByteArray :=
  ((List.range count).map fun i => UInt8.ofNat (value / 256 ^ i % 256)).toByteArray

namespace Present

def sbox : Array Nat := #[0xc, 0x5, 0x6, 0xb, 0x9, 0x0, 0xa, 0xd, 0x3, 0xe, 0xf, 0x8, 0x4, 0x7, 0x1, 0x2]
def keyOffset : Nat := 0x87ca995217ba31853dce
def firstRoundKeyOffset : Nat := 0x81000000000

def pLayerBit (bit : Nat) : Nat := if bit = 63 then 63 else 16 * bit % 63

/-- The S-box on each nibble, then the P-layer. -/
def spLayer (state : Nat) : Nat :=
  let substituted := (List.range 16).foldl
    (fun acc k => acc + sbox[(state / 16 ^ k) % 16]! * 16 ^ k) 0
  (List.range 64).foldl (fun acc bit => acc + (substituted / 2 ^ bit % 2) * 2 ^ pLayerBit bit) 0

/-- The key-register update: rotate left 61, S-box the top nibble, add the counter. -/
def update (register counter : Nat) : Nat :=
  let rotated := (register * 2 ^ 61 + register / 2 ^ 19) % 2 ^ 80
  let top := sbox[rotated / 2 ^ 76]! * 2 ^ 76 + rotated % 2 ^ 76
  top ^^^ (counter * 2 ^ 15)

/-- The 32 round keys: key 0 from the key itself, the rest from `key ^ keyOffset`, and
    bit 6 flipped after the second update. -/
def roundKeys (key : Nat) : List Nat := Id.run do
  let mut keys := [(key / 2 ^ 16) ^^^ firstRoundKeyOffset]
  let mut register := update (key ^^^ keyOffset) 1
  for counter in [1:32] do
    keys := keys ++ [register / 2 ^ 16]
    register := update register (counter + 1) ^^^ (if counter = 1 then 0x40 else 0)
  return keys

def rounds (state : Nat) (keys : List Nat) : Nat :=
  (keys.dropLast.foldl (fun state key => spLayer (state ^^^ key)) state) ^^^ keys.getLast!

def byteReverse (count value : Nat) : Nat :=
  (List.range count).foldl (fun acc i => acc * 256 + value / 256 ^ i % 256) 0

/-- HarpoS7's Monolith9: PRESENT on the byte-reversed little-endian block. -/
def encrypt (block key : Nat) : Nat :=
  byteReverse 8 (rounds (byteReverse 8 block) (roundKeys key))

/-- An 80-bit little-endian value as the big-endian key register. -/
def keyRegister (half : Nat) : Nat := byteReverse 10 half

def keyHalves (value : Nat) : Nat × Nat :=
  (keyRegister (value % 2 ^ 80), keyRegister (value / 2 ^ 80))

def encryptBlocks (blocks keys : List Nat) : Nat :=
  ((blocks.zip keys).zipIdx.foldl
    (fun acc ((block, key), index) => acc + encrypt block key * 2 ^ (64 * index)) 0) % 2 ^ 160

end Present

namespace Curve

def p : Nat := 2 ^ 160 - 47
def b : Int := 0xfdec56a0f1a148a7ca6f04463a24f5f56c3f3a4f
def generatorX : Nat := 0x7d2ed8e2846e58d74a7a613285471707a39d0c8e
def scalarMask : Nat := 0xf8e62e8673b79ca477a1d36333b1c0de6c706448

def modP (value : Int) : Int := value % (p : Int)

/-- Projective doubling for `a = −1`. -/
def double (x z : Int) : Int × Int :=
  let xx := modP (x * x)
  let zz := modP (z * z)
  ((xx + zz) ^ 2 - 8 * b * x * z * zz, 4 * z * (x * xx - x * zz + b * z * zz))

/-- x(P₁ + P₂) from x(P₁), x(P₂) and the affine x(P₁ − P₂), for `a = −1`. -/
def add (x1 z1 x2 z2 difference : Int) : Int × Int :=
  let cross := x1 * z2 - x2 * z1
  (2 * (x1 * z2 + x2 * z1) * (x1 * x2 - z1 * z2) + 4 * b * (z1 * z2) ^ 2 - difference * cross * cross,
    cross * cross)

def powMod (base exponent modulus : Nat) : Nat := Id.run do
  let mut result := 1
  let mut base := base % modulus
  let mut exponent := exponent
  while exponent > 0 do
    if exponent % 2 = 1 then result := result * base % modulus
    base := base * base % modulus
    exponent := exponent / 2
  return result

/-- Affine x(scalar · Q) for the point with x-coordinate `x`, or 0 for infinity. -/
def xMultiply (scalar x : Nat) : Nat := Id.run do
  let x : Int := ((x % p : Nat) : Int)
  let mut low : Int × Int := (1, 0)
  let mut high : Int × Int := (x, 1)
  let bits := if scalar = 0 then 0 else Nat.log2 scalar + 1
  for i in [0:bits] do
    let bit := bits - 1 - i
    let total := add low.1 low.2 high.1 high.2 x
    if scalar / 2 ^ bit % 2 = 1 then
      low := total
      high := double high.1 high.2
    else
      high := total
      low := double low.1 low.2
    low := (modP low.1, modP low.2)
    high := (modP high.1, modP high.2)
  let xOut := low.1.toNat
  let zOut := low.2.toNat
  return if zOut = 0 then 0 else xOut * powMod zOut (p - 2) p % p

def ladderScalar (prng2 : ByteArray) : Nat := leNat (prng2.extract 0 20) ^^^ scalarMask

end Curve

namespace Checksum

def polynomial : Nat := 2 ^ 128 + 2 ^ 32 + 2 ^ 15 + 2 ^ 2 + 1

/-- `a · b` in GF(2)[x] modulo `polynomial`, for 128-bit `a` and `b`. -/
def multiply (a b : Nat) : Nat := Id.run do
  let mut product := 0
  let mut a := a
  let mut b := b
  for _ in [0:129] do
    if b = 0 then break
    if b % 2 = 1 then product := product ^^^ a
    b := b / 2
    a := a * 2
    if a ≥ 2 ^ 128 then a := a ^^^ polynomial
  return product

end Checksum

namespace Seed

def preSeedKey : Nat := 0xa98de7c5164ad032538f
def keyPlaintexts : List Nat := [0xeffcb975bc8864fd, 0x20b6407af0433f14, 0x610806efe0358644, 0xff78c6d5c660cedc, 0xc5e88fdb01af4ae1, 0x2ae2ba517c0d93f6]
def seedMaskPlaintexts : List Nat := [0xf5ea1e69cbdf8ef1, 0xf4c52febc1c01d1a, 0xadf3602156a724de]

/-- key1's three 64-bit blocks under `preSeedKey`, as one 160-bit value. -/
def preSeed (key1 : ByteArray) : Nat :=
  Present.encryptBlocks ((List.range 3).map fun i => leNat (key1.extract (8 * i) (8 * i + 8)))
    [preSeedKey, preSeedKey, preSeedKey]

def seedMask (sharedX : Nat) : Nat :=
  let (low, high) := Present.keyHalves sharedX
  Present.encryptBlocks seedMaskPlaintexts [low, low, high]

/-- The 60-byte seed field, or `none` when the scalar gives the point at infinity
    (s7commplus draws again then). -/
def write (publicKey : ByteArray) (preSeed : Nat) (blinding prng2 : ByteArray) : Option ByteArray :=
  let scalar := Curve.ladderScalar prng2
  let ephemeral := Curve.xMultiply scalar Curve.generatorX
  if ephemeral = 0 then none
  else
    let shared := Curve.xMultiply scalar (leNat (publicKey.extract 0 20))
    some (natLe 20 (preSeed ^^^ seedMask shared) ++ natLe 20 ephemeral ++ blinding.extract 0 20)

/-- The challenge key, the checksum key and the checksum's hash key. -/
def deriveKeys (preSeed : Nat) : ByteArray × ByteArray × Nat :=
  let (low, high) := Present.keyHalves preSeed
  let derived := (keyPlaintexts.zipIdx.map fun (block, index) =>
    natLe 8 (Present.encrypt block (if index < 3 then low else high))).foldl (· ++ ·) ByteArray.empty
  (derived.extract 0 16, derived.extract 16 32, leNat (derived.extract 32 48))

end Seed

/-- The blob's 48-byte header: magic, length, two ones, then the key id and flags of
    key2 and of the public key. -/
def blobMetadata (family : KeyFamily) (publicKey key2 : ByteArray) : ByteArray :=
  natLe 4 0xfee1dead ++ natLe 4 180 ++ natLe 4 1 ++ natLe 4 1 ++
    natLe 8 (keyId key2).toNat ++ natLe 4 family.symmetricKeyFlags.toNat ++ natLe 4 0 ++
    natLe 8 (keyId publicKey).toNat ++ natLe 4 family.publicKeyFlags.toNat ++ natLe 4 0

/-- Multiply the little-endian counter by x in GCM's bit-reflected field. -/
def advanceCounter (counter : Nat) : Nat :=
  counter / 2 ^^^ (if counter % 2 = 1 then 0xe1 * 2 ^ 120 else 0)

def xorBytes (a b : ByteArray) : ByteArray :=
  ((a.toList.zip b.toList).map fun (x, y) => x ^^^ y).toByteArray

/-- The 180-byte blob and the session key, from the controller's public key and
    challenge and the five random draws: key1 and key2 (24 bytes), the IV (16), and the
    seed's blinding bytes and ladder input (20 each). `none` in the negligible case that
    the ladder input gives the point at infinity. -/
def buildRealPlcBlob (family : KeyFamily) (publicKey challenge key1 key2 iv blinding prng2 : ByteArray) :
    Option (ByteArray × ByteArray) := do
  let preSeed := Seed.preSeed key1
  let seed ← Seed.write publicKey preSeed blinding prng2
  let (challengeKey, checksumKey, hashKey) := Seed.deriveKeys preSeed
  let aes (counter : Nat) := Aes.encryptBlock challengeKey (natLe 16 counter)
  let fold (checksum : Nat) (block : ByteArray) := Checksum.multiply (checksum ^^^ leNat block) hashKey
  let counter := leNat iv
  let checksum := Checksum.multiply counter hashKey
  let challengeBlock := xorBytes (aes counter) (challenge.extract 2 18)
  let counter := advanceCounter counter
  let checksum := fold checksum challengeBlock
  let key2Block := xorBytes (aes counter) (key2.extract 0 16)
  let counter := advanceCounter counter
  let checksum := fold checksum key2Block
  let leftover := xorBytes ((aes counter).extract 0 8) (key2.extract 16 24)
  let checksum := fold checksum (leftover ++ natLe 8 0)
  let final := Checksum.multiply (checksum ^^^ 40 * 2 ^ 96) hashKey
  let encryptedChecksum := Aes.encryptBlock checksumKey (natLe 16 final)
  let blob := blobMetadata family publicKey key2 ++ seed ++ iv.extract 0 16 ++ challengeBlock ++ key2Block ++
    leftover ++ encryptedChecksum
  pure (blob, deriveSessionKey key2 challenge)

end LeanS7CommPlus
