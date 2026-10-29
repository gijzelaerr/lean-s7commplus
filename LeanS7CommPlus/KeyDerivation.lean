import LeanS7CommPlus.Sha256
import LeanS7CommPlus.SessionKey

/-!
# SessionKey key derivation

The SHA-256 key derivations of the V1 SessionKey handshake and the challenge
fingerprint that the session key depends on, ported from s7commplus
`v1_session_key/key_derivation.py` and `real_plc/fingerprint.py`. Those port
HarpoS7's `KeyUtilities` and `HarpoFingerprint` (MIT, see `LICENSE-HarpoS7`).

- `deriveSessionKey`: `HMAC-SHA256(key2[:24], fingerprint(challenge) ‖ challenge[2:18])[:24]`.
- `deriveChallengeEncryptionKey`: the AES-128 key for the challenge blocks of the blob.
- `deriveSeedEncryptionKeyAndIv`: the AES-256 key and IV for the blob's seed.
- `deriveLegitimationChallengeKey`: `SHA-256(sessionKey[:24] ‖ "MISTRUST")[4:28]`.

The fingerprint is a 13-round substitution-permutation network on AES's inverse
S-box with fixed keys, recovered in s7commplus from HarpoS7's white-boxed gate
network. The constants below are generated from the s7commplus module. All of it is
checked against s7commplus with known-answer vectors (`Tests.lean`).
-/

namespace LeanS7CommPlus

namespace Fingerprint

def hex (text : String) : ByteArray := (hexToBytes? text).getD ByteArray.empty

def invSbox : ByteArray := hex "52096ad53036a538bf40a39e81f3d7fb7ce339829b2fff87348e4344c4dee9cb547b9432a6c2233dee4c950b42fac34e082ea16628d924b2765ba2496d8bd12572f8f66486689816d4a45ccc5d65b6926c704850fdedb9da5e154657a78d9d8490d8ab008cbcd30af7e45805b8b34506d02c1e8fca3f0f02c1afbd0301138a6b3a9111414f67dcea97f2cfcef0b4e67396ac7422e7ad3585e2f937e81c75df6e47f11a711d29c5896fb7620eaa18be1bfc563e4bc6d279209adbc0fe78cd5af41fdda8338807c731b11210592780ec5f60517fa919b54a0d2de57a9f93c99cefa0e03b4dae2af5b0c8ebbb3c83539961172b047eba77d626e169146355210c7d"

def inputKey : ByteArray := hex "84bf37e056af421191579ebc641c9fb3"

/-- Per round, the key byte of each of the 8 S-boxes. -/
def roundKeys : List ByteArray := [
    hex "3be4b25d87bcc3db",
    hex "ad4c460f7324d5cf",
    hex "643ee25f3892b80e",
    hex "d352fe09ba330dea",
    hex "2525c6a827cee55b",
    hex "71f7c262b60c0900",
    hex "54f7229eba99cbc6",
    hex "40a2f2cad7bfe29d",
    hex "bda945cd3d9beef6",
    hex "d2a3717b0ee1b5a4",
    hex "daa465fa78e749e0",
    hex "7600329783ca7cfe",
    hex "fe5240529c64dfd6"]

/-- Per round, for each new state byte: the crumb and the four source bytes, low
    crumb first. -/
def roundWiring : List (List (Nat × Nat × Nat × Nat × Nat)) := [
    [(1, 7, 6, 5, 4), (0, 3, 2, 1, 0), (0, 7, 6, 5, 4), (1, 3, 2, 1, 0), (2, 7, 6, 5, 4), (2, 3, 2, 1, 0), (3, 7, 6, 5, 4), (3, 3, 2, 1, 0)],
    [(2, 2, 1, 0, 3), (3, 2, 1, 0, 3), (1, 2, 1, 0, 3), (0, 2, 1, 0, 3), (2, 4, 5, 6, 7), (3, 4, 5, 6, 7), (1, 4, 5, 6, 7), (0, 4, 5, 6, 7)],
    [(3, 0, 4, 1, 5), (2, 0, 4, 1, 5), (0, 0, 4, 1, 5), (1, 0, 4, 1, 5), (3, 3, 7, 2, 6), (2, 3, 7, 2, 6), (0, 3, 7, 2, 6), (1, 3, 7, 2, 6)],
    [(2, 5, 1, 4, 0), (1, 5, 1, 4, 0), (0, 5, 1, 4, 0), (3, 5, 1, 4, 0), (2, 6, 2, 7, 3), (3, 6, 2, 7, 3), (1, 6, 2, 7, 3), (0, 6, 2, 7, 3)],
    [(3, 4, 0, 5, 3), (2, 4, 0, 5, 3), (1, 4, 0, 5, 3), (0, 4, 0, 5, 3), (0, 7, 2, 6, 1), (1, 7, 2, 6, 1), (3, 7, 2, 6, 1), (2, 7, 2, 6, 1)],
    [(1, 4, 3, 5, 2), (3, 4, 3, 5, 2), (0, 4, 3, 5, 2), (2, 4, 3, 5, 2), (2, 7, 1, 6, 0), (0, 7, 1, 6, 0), (1, 7, 1, 6, 0), (3, 7, 1, 6, 0)],
    [(0, 3, 4, 1, 7), (2, 2, 5, 0, 6), (3, 2, 5, 0, 6), (2, 3, 4, 1, 7), (1, 3, 4, 1, 7), (3, 3, 4, 1, 7), (1, 2, 5, 0, 6), (0, 2, 5, 0, 6)],
    [(3, 1, 3, 2, 5), (2, 1, 3, 2, 5), (0, 1, 3, 2, 5), (2, 7, 0, 6, 4), (1, 1, 3, 2, 5), (0, 7, 0, 6, 4), (1, 7, 0, 6, 4), (3, 7, 0, 6, 4)],
    [(0, 5, 2, 6, 4), (1, 3, 1, 7, 0), (1, 5, 2, 6, 4), (3, 3, 1, 7, 0), (2, 5, 2, 6, 4), (2, 3, 1, 7, 0), (3, 5, 2, 6, 4), (0, 3, 1, 7, 0)],
    [(2, 0, 7, 2, 1), (0, 4, 5, 6, 3), (3, 0, 7, 2, 1), (1, 4, 5, 6, 3), (3, 4, 5, 6, 3), (1, 0, 7, 2, 1), (2, 4, 5, 6, 3), (0, 0, 7, 2, 1)],
    [(2, 0, 6, 2, 4), (3, 0, 6, 2, 4), (0, 0, 6, 2, 4), (3, 7, 1, 5, 3), (2, 7, 1, 5, 3), (1, 7, 1, 5, 3), (1, 0, 6, 2, 4), (0, 7, 1, 5, 3)],
    [(3, 4, 0, 3, 1), (0, 4, 0, 3, 1), (2, 4, 0, 3, 1), (1, 7, 2, 5, 6), (2, 7, 2, 5, 6), (0, 7, 2, 5, 6), (3, 7, 2, 5, 6), (1, 4, 0, 3, 1)],
    [(3, 4, 2, 6, 0), (1, 4, 2, 6, 0), (2, 5, 1, 3, 7), (2, 4, 2, 6, 0), (0, 4, 2, 6, 0), (1, 5, 1, 3, 7), (3, 5, 1, 3, 7), (0, 5, 1, 3, 7)]]

/-- For each fingerprint nibble, most significant first: the crumb and the two bytes. -/
def outputCrumbs : List (Nat × Nat × Nat) := [(3, 0, 6), (3, 3, 2), (3, 1, 5), (3, 4, 7), (2, 0, 6), (2, 3, 2), (2, 1, 5), (2, 4, 7), (1, 0, 6), (1, 3, 2), (1, 1, 5), (1, 4, 7), (0, 0, 6), (0, 3, 2), (0, 1, 5), (0, 4, 7)]

/-- For each fingerprint nibble, its value for each of the 16 crumb pairs. -/
def outputEncoding : List String := [
    "39fc6a4710bed285",
    "d3e086192cb475fa",
    "4813eb0752dfa9c6",
    "8f5ac7219d406e3b",
    "16d9f3e4ab25c870",
    "687c139af052dbe4",
    "5cb2ad73680e49f1",
    "d9a42f187b65e03c",
    "1c3e92d587bfa406",
    "218bd470a3cfe659",
    "14af6dbe970c5832",
    "2085fde91ca376b4",
    "f2d5a8961be3c704",
    "814e0635d9cf7ab2",
    "3ec4715b2680fad9",
    "e87d946c2a5b03f1"]

/-- Bits `j` and `j + 4` of a byte as a 2-bit value. -/
def crumb (value : UInt8) (j : Nat) : Nat :=
  (value.toNat >>> j) % 2 + 2 * ((value.toNat >>> (j + 4)) % 2)

def round (state : Array UInt8) (keys : ByteArray) (wiring : List (Nat × Nat × Nat × Nat × Nat)) :
    Array UInt8 :=
  ((wiring.zip (List.range 8)).map fun ((j, s0, s1, s2, s3), index) =>
    let w := crumb state[s0]! j + 4 * crumb state[s1]! j + 16 * crumb state[s2]! j + 64 * crumb state[s3]! j
    invSbox.get! (w ^^^ (keys.get! index).toNat)).toArray

def nibble (state : Array UInt8) (index : Nat) : Nat :=
  let (j, a, b) := outputCrumbs[index]!
  let table := outputEncoding[index]!
  let position := crumb state[a]! j + 4 * crumb state[b]! j
  (table.toList[position]!).toNat - (if (table.toList[position]!).isDigit then '0'.toNat else 'a'.toNat - 10)

end Fingerprint

open Fingerprint in
/-- The 8-byte fingerprint of a challenge of at least 18 bytes. -/
def fingerprintChallenge (challenge : ByteArray) : ByteArray :=
  let y := (List.range 16).map fun i => invSbox.get! ((challenge.get! (i + 2) ^^^ inputKey.get! i).toNat)
  let state := ((List.range 8).map fun i => y[i]! ^^^ y[i + 8]!).toArray
  let state := (roundKeys.zip roundWiring).foldl (fun state (keys, wiring) => round state keys wiring) state
  ((List.range 8).map fun i => UInt8.ofNat (nibble state (2 * i) * 16 + nibble state (2 * i + 1))).toByteArray

/-- The 24-byte session key: HMAC-SHA256 under the first 24 bytes of key2, over the
    challenge's fingerprint and its bytes 2 to 17, cut to 24 bytes. -/
def deriveSessionKey (key2 challenge : ByteArray) : ByteArray :=
  (Hmac.sha256 (key2.extract 0 24) (fingerprintChallenge challenge ++ challenge.extract 2 18)).extract 0 24

/-- The AES-128 key for the challenge blocks: SHA-256 of the first 24 bytes of the
    random key and the bytes 01 02 … 0f 00, cut to 16 bytes. -/
def deriveChallengeEncryptionKey (randomKey : ByteArray) : ByteArray :=
  let magic := ((List.range 16).map fun i => UInt8.ofNat ((i + 1) % 16)).toByteArray
  (Sha256.hash (randomKey.extract 0 24 ++ magic)).extract 0 16

/-- The AES-256 key and IV for the seed: SHA-256 of the reversed first 32 bytes of
    `a2`, the first 64 bytes of `a3` and a counter byte, for counters 0 and 32; 32 bytes
    of the first digest and 16 of the second. -/
def deriveSeedEncryptionKeyAndIv (a2 a3 : ByteArray) : ByteArray :=
  let reversed := ((a2.extract 0 32).toList.reverse).toByteArray
  let digest (counter : UInt8) := Sha256.hash (reversed ++ a3.extract 0 64 ++ ByteArray.mk #[counter])
  digest 0 ++ (digest 32).extract 0 16

/-- The 24-byte key for the legitimation challenge. -/
def deriveLegitimationChallengeKey (sessionKey : ByteArray) : ByteArray :=
  (Sha256.hash (sessionKey.extract 0 24 ++ "MISTRUST".toUTF8)).extract 4 28

theorem fingerprintChallenge_size (challenge : ByteArray) : (fingerprintChallenge challenge).size = 8 := by
  unfold fingerprintChallenge
  simp only [List.size_toByteArray, List.length_map, List.length_range]

theorem deriveSessionKey_size (key2 challenge : ByteArray) : (deriveSessionKey key2 challenge).size = 24 := by
  simp [deriveSessionKey, Hmac.sha256_size]

end LeanS7CommPlus
