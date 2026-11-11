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

/-- A flags byte and a datatype byte that start a challenge value: a BLOB, or a USINT
    array. -/
def challengeHeader (flags datatype : UInt8) : Bool :=
  datatype == 0x14 || (datatype == 0x02 && flags &&& 0x10 != 0)

/-- Where the challenge value starts, as in s7commplus `_response_pvalue_offset`: right
    at the cursor when a challenge header is there, else after a zero marker. A BLOB's
    flags byte is itself `00`, so the header is checked before any marker is skipped. -/
def challengeStart (cursor : Cursor) : Cursor :=
  match cursor.readUInt8 with
  | .ok (flags, afterFlags) =>
    match afterFlags.readUInt8 with
    | .ok (datatype, _) =>
      if challengeHeader flags datatype then cursor
      else if flags = 0 then afterFlags
      else cursor
    | .error _ => cursor
  | .error _ => cursor

/-- The challenge in a GetVarSubstreamed reply: the return value, an optional zero
    marker, then a BLOB or a USINT array. -/
def decodeLegitimationChallenge (payload : ByteArray) : Except DecodeError ByteArray := do
  let (returnValue, cursor) ← Vlq.decodeUInt64 { data := payload }
  if returnValue ≠ 0 then
    throw (.remoteFailure 0 s!"GetVarSubstreamed failed with return value {returnValue}")
  let cursor := challengeStart cursor
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

/-! ## What the challenge decoder accepts

`decodeLegitimationChallenge` is lossy: it discards a BLOB's root id, does not check a
BLOB's flags byte, and ignores the bytes after the challenge. Its theorem characterises
the payload. -/

/-- `challengeStart` moves past a single zero marker or not at all. -/
theorem challengeStart_spec (cursor : Cursor) :
    (challengeStart cursor).data = cursor.data ∧
      ((challengeStart cursor).offset = cursor.offset ∨
        ((challengeStart cursor).offset = cursor.offset + 1 ∧
          cursor.data.extract cursor.offset (cursor.offset + 1) = bytes #[0x00])) := by
  unfold challengeStart
  split
  · rename_i flags afterFlags hflags
    obtain ⟨-, hx, hn⟩ := readUInt8_extract _ _ _ hflags
    split
    · split
      · exact ⟨rfl, Or.inl rfl⟩
      · split
        · rename_i hzero
          rw [hzero] at hx
          exact ⟨by rw [hn], Or.inr ⟨by rw [hn], hx.symm⟩⟩
        · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inl rfl⟩

/-- The length and the challenge bytes after the value header. -/
theorem challengeTail_spec (cursor afterLength rest : Cursor) (length : UInt32)
    (challenge : ByteArray) (h1 : Vlq.decodeUInt32 cursor = .ok (length, afterLength))
    (h2 : afterLength.readBytes length.toNat = .ok (challenge, rest)) :
    ∃ stop, cursor.offset ≤ stop ∧ ∃ lengthBytes,
      cursor.data.extract cursor.offset stop = lengthBytes ++ challenge ∧
      Vlq.UInt32Form (UInt32.ofNat challenge.size) lengthBytes ∧ challenge.size < 2 ^ 32 := by
  obtain ⟨hd1, hle1, hf1⟩ := Vlq.decodeUInt32_form _ _ _ h1
  have hsize := readBytes_size _ _ _ _ h2
  obtain ⟨hp, -⟩ := readBytes_extract _ _ _ _ h2
  refine ⟨afterLength.offset + length.toNat, by omega, _, ?_,
    by rw [hsize, UInt32.ofNat_toNat]; exact hf1, by rw [hsize]; exact length.toNat_lt⟩
  rw [hp, hd1, ByteArray.extract_append_extract_of_le _ hle1 (by omega)]

/-- An accepted GetVarSubstreamed challenge payload starts with a zero return value in
    any 64-bit VLQ form, an optional zero marker, a flags and a datatype byte, and then
    either a BLOB (datatype `0x14`, a root id in any 32-bit form) or a USINT array
    (datatype `0x02` with flag `0x10`), a length in any 32-bit form and exactly that
    many challenge bytes. Whatever follows (`payload` from `consumed` on) is not read. -/
theorem decodeLegitimationChallenge_canonical (payload challenge : ByteArray)
    (h : decodeLegitimationChallenge payload = .ok challenge) :
    ∃ consumed returnBytes marker flags datatype rootBytes lengthBytes,
      payload.extract 0 consumed =
        returnBytes ++ marker ++ bytes #[flags, datatype] ++ rootBytes ++ lengthBytes ++ challenge ∧
      Vlq.UInt64Form 0 returnBytes ∧ (marker = ByteArray.empty ∨ marker = bytes #[0x00]) ∧
      ((datatype = 0x14 ∧ ∃ root, Vlq.UInt32Form root rootBytes) ∨
        (datatype = 0x02 ∧ flags &&& 0x10 ≠ 0 ∧ rootBytes = ByteArray.empty)) ∧
      Vlq.UInt32Form (UInt32.ofNat challenge.size) lengthBytes ∧ challenge.size < 2 ^ 32 := by
  simp only [decodeLegitimationChallenge, bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i _ r1 h1
    obtain ⟨hd1, hle1, hf1⟩ := Vlq.decodeUInt64_form _ _ _ h1
    simp only at hd1 hle1 hf1
    rcases ite_eq_cases h with ⟨-, h⟩ | ⟨hzero, h⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · have hzero : r1.fst = 0 := by simpa using hzero
      rw [hzero] at hf1
      obtain ⟨hds, hstart⟩ := challengeStart_spec r1.snd
      rw [hd1] at hds hstart
      -- the marker: the bytes challengeStart skipped
      have hmarker : payload.extract r1.snd.offset (challengeStart r1.snd).offset =
            ByteArray.empty ∨
          payload.extract r1.snd.offset (challengeStart r1.snd).offset = bytes #[0x00] := by
        rcases hstart with hsame | ⟨hnext, hzeroByte⟩
        · exact Or.inl (by rw [hsame]; exact extract_self _ _)
        · exact Or.inr (by rw [hnext]; exact hzeroByte)
      have hstartle : r1.snd.offset ≤ (challengeStart r1.snd).offset := by
        rcases hstart with hsame | ⟨hnext, -⟩ <;> omega
      split at h
      · contradiction
      · rename_i _ r2 h2
        obtain ⟨-, hx2, hn2⟩ := readUInt8_extract _ _ _ h2
        rw [hds] at hx2
        split at h
        · contradiction
        · rename_i _ r3 h3
          rw [hn2] at h3
          obtain ⟨-, hx3, hn3⟩ := readUInt8_extract _ _ _ h3
          simp only at hx3 hn3
          rw [hds] at hx3 hn3
          have hheader : bytes #[r2.fst, r3.fst] =
              payload.extract (challengeStart r1.snd).offset ((challengeStart r1.snd).offset + 1 + 1) := by
            rw [bytes_pair, hx2, hx3,
              ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]
          rcases ite_eq_cases h with ⟨hblob, h⟩ | ⟨hnotBlob, h⟩
          · -- a BLOB: the root id, then the length and the bytes
            split at h
            · contradiction
            · rename_i _ r4 h4
              rw [hn3] at h4
              obtain ⟨hd4, hle4, hf4⟩ := Vlq.decodeUInt32_form _ _ _ h4
              simp only at hd4 hle4 hf4
              simp only [pure, Except.pure] at h
              split at h
              · contradiction
              · rename_i _ r5 h5
                split at h
                · contradiction
                · rename_i _ r6 h6
                  simp only [Except.ok.injEq] at h
                  subst h
                  obtain ⟨stop, hstop, lengthBytes, htail, hlen, hsize⟩ :=
                    challengeTail_spec _ _ _ _ _ h5 h6
                  rw [hd4] at htail
                  refine ⟨stop, _, _, r2.fst, r3.fst, _, lengthBytes, ?_, hf1, hmarker,
                    Or.inl ⟨hblob, _, hf4⟩, hlen, hsize⟩
                  rw [hheader, ByteArray.append_assoc (b := lengthBytes), ← htail,
                    ByteArray.extract_append_extract_of_le _ hle1 hstartle,
                    ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
                    ByteArray.extract_append_extract_of_le _ (by omega) hle4,
                    ByteArray.extract_append_extract_of_le _ (by omega) hstop]
          · rcases ite_eq_cases h with ⟨harray, h⟩ | ⟨-, h⟩
            · -- a USINT array: the length and the bytes right after the header
              simp only [pure, Except.pure] at h
              split at h
              · contradiction
              · rename_i _ r5 h5
                split at h
                · contradiction
                · rename_i _ r6 h6
                  simp only [Except.ok.injEq] at h
                  subst h
                  obtain ⟨stop, hstop, lengthBytes, htail, hlen, hsize⟩ :=
                    challengeTail_spec _ _ _ _ _ h5 h6
                  rw [hn3] at htail hstop
                  simp only at htail hstop
                  refine ⟨stop, _, _, r2.fst, r3.fst, ByteArray.empty, lengthBytes, ?_, hf1, hmarker,
                    Or.inr ⟨harray.1, harray.2, rfl⟩, hlen, hsize⟩
                  rw [hheader, ByteArray.append_empty, ByteArray.append_assoc (b := lengthBytes),
                    ← htail,
                    ByteArray.extract_append_extract_of_le _ hle1 hstartle,
                    ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
                    ByteArray.extract_append_extract_of_le _ (by omega) hstop]
            · simp [throw, throwThe, MonadExceptOf.throw] at h

end LeanS7CommPlus
