import LeanS7CommPlus.Session
import LeanS7CommPlus.Sha256
import LeanS7CommPlus.PublicKeys

/-!
# The V1 SessionKey handshake: wire layer

The messages around the SecurityKey of a V1 SessionKey session, byte for byte those
of s7commplus (`connection.py`; the key ids and flags from `v1_session_key/`, a port
of HarpoS7, MIT, see `LICENSE-HarpoS7`):

- the SecurityKey struct (struct 1800 with key descriptors 1825 and the encrypted
  blob), written with the ServerSessionVersion echo in the SessionKey setup;
- the session activation, a SetVariable of USINT 5 to address 323;
- the protection-level read, a GetVarSubstreamed of address 1842.

The blob itself, and the session key, come from the handshake cryptography (phase 7b
and 7c). The SecurityKey struct is a tree struct, so the proved tree codec carries
it: `decodeSecurityKey_encode`.
-/

namespace LeanS7CommPlus

open LeanS7

inductive KeyFamily where
  | s71500
  | s71200
  | plcsim
  deriving Repr, BEq, DecidableEq

def KeyFamily.ofByte? : UInt8 → Option KeyFamily
  | 0x00 => some .s71500
  | 0x01 => some .s71200
  | 0x03 => some .plcsim
  | _ => none

/-- HarpoS7's `BlobMetadataWriter` flags. -/
def KeyFamily.symmetricKeyFlags : KeyFamily → UInt32
  | .s71500 => 0x001
  | .s71200 => 0x101
  | .plcsim => 0x301

def KeyFamily.publicKeyFlags : KeyFamily → UInt32
  | .s71500 => 0x010
  | .s71200 => 0x110
  | .plcsim => 0x310

/-! ## Fingerprints and key ids -/

def hexValue? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The bytes of an even-length hex string. -/
def hexToBytes? (text : String) : Option ByteArray :=
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | high :: low :: rest => do
      let h ← hexValue? high
      let l ← hexValue? low
      let tail ← go rest
      pure (UInt8.ofNat (h * 16 + l) :: tail)
    | [_] => none
  (go text.toList).map List.toByteArray

/-- A fingerprint `FF:HHHHHHHHHHHHHHHH`: the key family and the upper-case key id. -/
def parseFingerprint (fingerprint : String) : Option (KeyFamily × String) := do
  let chars := fingerprint.toList
  if chars.length ≠ 19 ∨ chars[2]? ≠ some ':' then none
  let familyBytes ← hexToBytes? (String.ofList (chars.take 2))
  let family ← KeyFamily.ofByte? (familyBytes.get! 0)
  let keyId := String.ofList ((chars.drop 3).map Char.toUpper)
  let _ ← hexToBytes? keyId
  pure (family, keyId)

def KeyFamily.toByte : KeyFamily → UInt8
  | .s71500 => 0x00
  | .s71200 => 0x01
  | .plcsim => 0x03

/-- The bundled public key for a fingerprint. -/
def publicKey? (fingerprint : String) : Option ByteArray := do
  let (family, keyId) ← parseFingerprint fingerprint
  let familyText := s!"0{family.toByte.toNat}"
  let (_, hex) ← publicKeyTable.find? (·.1 == s!"{familyText}:{keyId}")
  hexToBytes? hex

/-- HarpoS7's `DeriveKeyId`: SHA-256 of the first 24 key bytes and `DERIVE`, the
    first 8 bytes read little-endian. -/
def keyId (key : ByteArray) : UInt64 :=
  let digest := Sha256.hash (key.extract 0 24 ++ "DERIVE".toUTF8)
  (List.range 8).foldr (fun i acc => acc <<< 8 ||| (digest.get! i).toUInt64) 0

/-! ## The SecurityKey struct -/

def StructId.securityKey : UInt32 := 1800
def StructId.securityKeyId : UInt32 := 1825

structure KeyDescriptor where
  id : UInt64
  flags : UInt32
  deriving Repr, BEq, DecidableEq

structure SecurityKey where
  publicKey : KeyDescriptor
  symmetricKey : KeyDescriptor
  blob : ByteArray
  deriving BEq

/-- A key descriptor as the members of struct 1825 under `key`. -/
def KeyDescriptor.items (key : UInt32) (descriptor : KeyDescriptor) : List Item :=
  [.memberStruct key StructId.securityKeyId,
   .member 1826 (.scalar (.ulint descriptor.id)),
   .member 1827 (.scalar (.udint descriptor.flags)),
   .member 1828 (.scalar (.udint 0)),
   .structEnd]

/-- The members of struct 1800: version, security level, the two key descriptors and
    the encrypted blob, then the struct's end. -/
def SecurityKey.items (key : SecurityKey) : List Item :=
  [.member 1801 (.scalar (.udint 0)), .member 1802 (.scalar (.usint 0))] ++
    key.publicKey.items 1803 ++ key.symmetricKey.items 1804 ++
    [.member 1805 (.scalar (.blob 0 key.blob)), .structEnd]

def SecurityKey.encode (key : SecurityKey) : ByteArray :=
  structHeader StructId.securityKey ++ encodeItems key.items

/-- The SecurityKey for a public key, a session key and the encrypted blob. -/
def SecurityKey.ofKeys (family : KeyFamily) (publicKey sessionKey blob : ByteArray) : SecurityKey :=
  { publicKey := ⟨keyId publicKey, family.publicKeyFlags⟩,
    symmetricKey := ⟨keyId sessionKey, family.symmetricKeyFlags ||| 0x10000⟩,
    blob }

/-- Read the SecurityKey back from struct 1800's members. -/
def SecurityKey.ofItems? : List Item → Option SecurityKey
  | [.member 1801 (.scalar (.udint 0)), .member 1802 (.scalar (.usint 0)),
     .memberStruct 1803 1825, .member 1826 (.scalar (.ulint publicId)),
     .member 1827 (.scalar (.udint publicFlags)), .member 1828 (.scalar (.udint 0)), .structEnd,
     .memberStruct 1804 1825, .member 1826 (.scalar (.ulint symmetricId)),
     .member 1827 (.scalar (.udint symmetricFlags)), .member 1828 (.scalar (.udint 0)), .structEnd,
     .member 1805 (.scalar (.blob 0 blob)), .structEnd] =>
    some { publicKey := ⟨publicId, publicFlags⟩, symmetricKey := ⟨symmetricId, symmetricFlags⟩, blob }
  | _ => none

def decodeSecurityKey (cursor : Cursor) : Except DecodeError (SecurityKey × Cursor) :=
  match decodeSlot cursor with
  | .error error => .error error
  | .ok (.inr _, _) => .error (.invalidField cursor.offset "SecurityKey is not a struct")
  | .ok (.inl structId, next) =>
    if structId ≠ StructId.securityKey then
      .error (.invalidField cursor.offset s!"expected struct 1800, got {structId}")
    else match decodeItems next.remaining [.struct] next with
      | .error error => .error error
      | .ok (items, after) =>
        match SecurityKey.ofItems? items with
        | some key => .ok (key, after)
        | none => .error (.invalidField next.offset "SecurityKey members out of shape")

/-! ## Round trip of the SecurityKey -/

theorem decodeSlot_structHeader (structId : UInt32) (pre suffix : ByteArray) :
    decodeSlot { data := pre ++ (structHeader structId ++ suffix), offset := pre.size } =
      .ok (.inl structId,
        { data := pre ++ (structHeader structId ++ suffix), offset := pre.size + 6 }) := by
  have hdata : pre ++ (structHeader structId ++ suffix) =
      pre ++ (bytes #[0x00] ++ (bytes #[0x17] ++ (uint32BE structId ++ suffix))) := by
    simp only [structHeader, ByteArray.append_assoc]; rfl
  rw [hdata]
  have r0 := Cursor.readUInt8_append_byte pre (bytes #[0x17] ++ (uint32BE structId ++ suffix)) 0x00
  have r1 := Cursor.readUInt8_append_byte (pre ++ bytes #[0x00]) (uint32BE structId ++ suffix) 0x17
  have r2 := Cursor.readUInt32BE_append_uint32BE (pre ++ bytes #[0x00] ++ bytes #[0x17]) suffix structId
  simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, List.size_toArray,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add] at r0 r1 r2
  unfold decodeSlot
  simp only [bind, Except.bind, pure, Except.pure]
  rw [r0]
  simp only
  rw [show pre.size + 1 = pre.size + 1 from rfl, r1]
  simp only [and_self, if_true]
  rw [show pre.size + 1 + 1 = pre.size + (1 + 1) by omega, r2]

theorem SecurityKey.closes (key : SecurityKey) : Closes [.struct] key.items := by
  simp [SecurityKey.items, KeyDescriptor.items, Closes, step]

theorem SecurityKey.fits (key : SecurityKey) (hblob : key.blob.size < 2 ^ 32) :
    ∀ item ∈ key.items, item.Fits := by
  intro item hitem
  simp only [SecurityKey.items, KeyDescriptor.items, List.cons_append, List.nil_append,
    List.mem_cons, List.mem_nil_iff, or_false] at hitem
  rcases hitem with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp_all [Item.Fits, Value.Fits, PValue.LengthsFit]

theorem SecurityKey.ofItems_items (key : SecurityKey) : SecurityKey.ofItems? key.items = some key := by
  rfl

/-- Decoding an encoded SecurityKey, inside any bytes, returns it. -/
theorem decodeSecurityKey_encode (key : SecurityKey) (hblob : key.blob.size < 2 ^ 32) (pre suffix : ByteArray) :
    decodeSecurityKey { data := pre ++ (key.encode ++ suffix), offset := pre.size } =
      .ok (key, { data := pre ++ (key.encode ++ suffix), offset := pre.size + key.encode.size }) := by
  have hdata : pre ++ (key.encode ++ suffix) =
      pre ++ (structHeader StructId.securityKey ++ (encodeItems key.items ++ suffix)) := by
    simp [SecurityKey.encode, ByteArray.append_assoc]
  rw [hdata]
  unfold decodeSecurityKey
  rw [decodeSlot_structHeader]
  simp only [ne_eq, not_true_eq_false, if_false, StructId.securityKey]
  have hitems := decodeItems_encode key.items [.struct] key.closes (key.fits hblob)
    ((pre ++ (structHeader 1800 ++ (encodeItems key.items ++ suffix))).size - (pre.size + 6))
    (by
      have := encodeItems_size_ge key.items
      simp [ByteArray.size_append, structHeader, bytes_size, uint32BE_size]
      omega)
    (pre ++ structHeader 1800) suffix
  have hsize : (pre ++ structHeader 1800).size = pre.size + 6 := by
    simp [ByteArray.size_append, structHeader, bytes_size, uint32BE_size]
  rw [ByteArray.append_assoc, hsize] at hitems
  simp only [Cursor.remaining]
  rw [hitems]
  simp only [SecurityKey.ofItems_items, Except.ok.injEq, Prod.mk.injEq, true_and]
  congr 1
  simp [SecurityKey.encode, ByteArray.size_append, structHeader, bytes_size, uint32BE_size]
  omega

end LeanS7CommPlus
