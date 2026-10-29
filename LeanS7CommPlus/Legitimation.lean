import LeanS7CommPlus.Blob
import LeanS7CommPlus.Session

/-!
# The SessionKey legitimation

After the SessionKey setup and the activation, a client with a password legitimates:
it reads a fresh 20-byte challenge from address 303 (GetVarSubstreamed) and writes a
248-byte answer to address 1846 (SetVarSubstreamed). Ported from s7commplus
`v1_session_key/legitimation.py` and `connection.py` (HarpoS7's `LegitimateScheme`,
MIT, see `LICENSE-HarpoS7`).

For real controllers (families 00 and 01) the answer is a second authenticator round:
key1 is `deriveLegitimationChallengeKey sessionKey`, key2 is `SHA-1(password)` followed
by the challenge, and the challenge block encrypts zeros. The pieces are framed by
`DEADBEEF` headers: a 64-byte seed header, the 60-byte seed, then three fragments.
Checked against s7commplus with known-answer vectors and a recorded session. The
emulator accepts any answer, so a live run checks only the messages around it.
-/

namespace LeanS7CommPlus

open LeanS7

def deadbeef : ByteArray := natLe 4 0xdeadbeef

/-- The 64-byte header before the seed. -/
def legitimationSeedHeader (family : KeyFamily) (publicKey challengeKey : ByteArray) : ByteArray :=
  deadbeef ++ natLe 4 (0x40 + 60) ++ natLe 4 1 ++ natLe 4 2 ++ natLe 5 0 ++ ByteArray.mk #[0x04] ++
    natLe 6 0 ++ natLe 8 (keyId publicKey).toNat ++ natLe 4 family.publicKeyFlags.toNat ++ natLe 4 0 ++
    natLe 8 (keyId challengeKey).toNat ++ natLe 4 1 ++ natLe 4 0 ++ natLe 4 60

def fragmentHeader (index length : Nat) : ByteArray := deadbeef ++ natLe 4 index ++ natLe 4 length

/-- The 248-byte answer to a legitimation challenge, from the session key, the password
    and three random draws: the IV (16 bytes) and the seed's blinding bytes and ladder
    input (20 each). -/
def legitimationAnswer (family : KeyFamily) (publicKey sessionKey : ByteArray) (password : String)
    (challenge iv blinding prng2 : ByteArray) : Option ByteArray := do
  let challengeKey := deriveLegitimationChallengeKey sessionKey
  let key2 := Sha1.hash password.toUTF8 ++ challenge.extract 0 20
  let preSeed := Seed.preSeed challengeKey
  let seed ← Seed.write publicKey preSeed blinding prng2
  let (encryptionKey, checksumKey, hashKey) := Seed.deriveKeys preSeed
  let (full, final) := encryptChallengeAndKey2 encryptionKey checksumKey hashKey iv (natLe 20 0) key2
  pure (legitimationSeedHeader family publicKey challengeKey ++ seed ++ fragmentHeader 0 0x40 ++ full ++
    fragmentHeader 1 (key2.size % 16 + 16) ++ final ++ fragmentHeader 2 0)

/-- The challenge in a GetVarSubstreamed reply: the return value, an optional zero
    marker, then a BLOB or a USINT array. -/
def decodeLegitimationChallenge (payload : ByteArray) : Except DecodeError ByteArray := do
  let (returnValue, cursor) ← Vlq.decodeUInt64 { data := payload }
  if returnValue ≠ 0 then
    throw (.remoteFailure 0 s!"GetVarSubstreamed failed with return value {returnValue}")
  let cursor := if payload.get! cursor.offset = 0 then { cursor with offset := cursor.offset + 1 } else cursor
  let (flags, cursor) ← cursor.readUInt8
  let (datatype, cursor) ← cursor.readUInt8
  let cursor ← if datatype = 0x14 then pure (← Vlq.decodeUInt32 cursor).2
    else if datatype = 0x02 ∧ flags &&& 0x10 ≠ 0 then pure cursor
    else throw (.invalidField cursor.offset s!"unexpected challenge value flags {flags} type {datatype}")
  let (length, cursor) ← Vlq.decodeUInt32 cursor
  let (challenge, _) ← cursor.readBytes length.toNat
  pure challenge

/-- A legitimation reply is refused when its first value, read as a signed return
    value, is negative (the first check of s7commplus `_check_v1_legitimation_response`). -/
def legitimationRefused (payload : ByteArray) : Bool :=
  match Vlq.decodeUInt64 { data := payload } with
  | .ok (value, _) => value ≥ 2 ^ 63
  | .error _ => false

end LeanS7CommPlus
