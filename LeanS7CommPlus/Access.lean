import LeanS7.Binary
import LeanS7CommPlus.Vlq
import LeanS7CommPlus.VlqSigned
import LeanS7CommPlus.Tree

/-!
# Variable access: GetMultiVariables

Layouts from the Python reference (`client._build_read_payload`,
`codec.encode_item_address`, `codec.encode_object_qualifier`,
`client._parse_read_response`) and the CPU 1214C capture.

- **Item address**: VLQ symbol CRC, VLQ access area, VLQ number of ids that follow
  (the sub-area and the LIDs), VLQ access sub-area, VLQ LIDs. A DB region is area
  `0x8A0E0000 + db`, sub-area 2550 (`DB_VALUE_ACTUAL`) and LIDs `[3, start, size]`.
- **Object qualifier**: id 1256 (big-endian), then ParentRID 1257 = RID 0,
  CompositionAID 1258 = AID 0 and KeyQualifier 1259 = UDINT. In a V1 session the
  KeyQualifier value is a fixed 4-byte word (`00 04 00 00 00 00` in the capture),
  in later versions a VLQ followed by a `0x00` byte.
- **GetMultiVariables request payload**: a zero word, the VLQ item count, the VLQ
  total field count (4 per address plus its LIDs), the addresses, the object
  qualifier, and four fill bytes. With integrity tracking the request IntegrityId
  goes just before the fill.
- **GetMultiVariables reply**: VLQ return value, the values as `[VLQ item number]
  [value]` ending with 0, the item errors as `[VLQ item number][VLQ error]` ending
  with 0. The PLC's IntegrityId and fill follow; their position depends on the
  firmware, so the decoder stops after the error list.
-/

namespace LeanS7CommPlus

open LeanS7

/-! ## VLQ lists -/

def encodeVlqList : List UInt32 → ByteArray
  | [] => ByteArray.empty
  | value :: rest => Vlq.encodeUInt32 value ++ encodeVlqList rest

def decodeVlqList : Nat → Cursor → Except DecodeError (List UInt32 × Cursor)
  | 0, cursor => .ok ([], cursor)
  | count + 1, cursor => do
    let (value, cursor) ← Vlq.decodeUInt32 cursor
    let (rest, cursor) ← decodeVlqList count cursor
    pure (value :: rest, cursor)

/-! ## Item addresses -/

structure ItemAddress where
  symbolCrc : UInt32
  accessArea : UInt32
  accessSubArea : UInt32
  lids : List UInt32
  deriving BEq, Repr

/-- The address of `size` bytes at `start` in data block `db`. -/
def ItemAddress.db (db : UInt16) (start size : UInt32) : ItemAddress :=
  { symbolCrc := 0, accessArea := 0x8A0E0000 + db.toUInt32, accessSubArea := 2550,
    lids := [3, start, size] }

/-- The fields an address contributes to the request's field count. -/
def ItemAddress.fieldCount (address : ItemAddress) : Nat :=
  4 + address.lids.length

def ItemAddress.encode (address : ItemAddress) : ByteArray :=
  Vlq.encodeUInt32 address.symbolCrc ++ Vlq.encodeUInt32 address.accessArea ++
    Vlq.encodeUInt32 (UInt32.ofNat (address.lids.length + 1)) ++
    Vlq.encodeUInt32 address.accessSubArea ++ encodeVlqList address.lids

def decodeItemAddress (cursor : Cursor) : Except DecodeError (ItemAddress × Cursor) := do
  let (symbolCrc, cursor) ← Vlq.decodeUInt32 cursor
  let (accessArea, cursor) ← Vlq.decodeUInt32 cursor
  let (ids, cursor) ← Vlq.decodeUInt32 cursor
  if ids = 0 then
    throw (.invalidField cursor.offset "item address without an access sub-area")
  let (accessSubArea, cursor) ← Vlq.decodeUInt32 cursor
  let (lids, cursor) ← decodeVlqList (ids.toNat - 1) cursor
  pure ({ symbolCrc, accessArea, accessSubArea, lids }, cursor)

def encodeAddresses : List ItemAddress → ByteArray
  | [] => ByteArray.empty
  | address :: rest => address.encode ++ encodeAddresses rest

def decodeAddresses : Nat → Cursor → Except DecodeError (List ItemAddress × Cursor)
  | 0, cursor => .ok ([], cursor)
  | count + 1, cursor => do
    let (address, cursor) ← decodeItemAddress cursor
    let (rest, cursor) ← decodeAddresses count cursor
    pure (address :: rest, cursor)

/-! ## Object qualifier -/

/-- How the KeyQualifier value is written: a fixed word (V1 sessions) or a VLQ and a
    `0x00` byte (later versions). -/
inductive QualifierForm where
  | fixed
  | vlq
  deriving BEq, DecidableEq, Repr

def encodeObjectQualifier (form : QualifierForm) (keyQualifier : UInt32) : ByteArray :=
  uint32BE 1256 ++ Vlq.encodeUInt32 1257 ++ bytes #[0x00, 0x12] ++ uint32BE 0 ++
    Vlq.encodeUInt32 1258 ++ bytes #[0x00, 0x13] ++ Vlq.encodeUInt32 0 ++
    Vlq.encodeUInt32 1259 ++ bytes #[0x00, 0x04] ++
    (match form with
     | .fixed => uint32BE keyQualifier
     | .vlq => Vlq.encodeUInt32 keyQualifier ++ bytes #[0x00])

/-- The fixed part of the object qualifier, up to the KeyQualifier value. -/
def objectQualifierPrefix : ByteArray :=
  uint32BE 1256 ++ Vlq.encodeUInt32 1257 ++ bytes #[0x00, 0x12] ++ uint32BE 0 ++
    Vlq.encodeUInt32 1258 ++ bytes #[0x00, 0x13] ++ Vlq.encodeUInt32 0 ++
    Vlq.encodeUInt32 1259 ++ bytes #[0x00, 0x04]

/-- Decode an object qualifier written in the given form. The fixed part must match
    exactly. -/
def decodeObjectQualifier (form : QualifierForm) (cursor : Cursor) :
    Except DecodeError (UInt32 × Cursor) := do
  let (fixedPart, cursor) ← cursor.readBytes objectQualifierPrefix.size
  if fixedPart != objectQualifierPrefix then
    throw (.invalidField cursor.offset "unexpected object qualifier")
  match form with
  | .fixed => cursor.readUInt32BE
  | .vlq => do
    let (keyQualifier, cursor) ← Vlq.decodeUInt32 cursor
    let (terminator, cursor) ← cursor.readUInt8
    if terminator != 0x00 then
      throw (.invalidField (cursor.offset - 1) "object qualifier terminator is not zero")
    pure (keyQualifier, cursor)

/-! ## GetMultiVariables -/

structure ReadRequest where
  addresses : List ItemAddress
  form : QualifierForm
  keyQualifier : UInt32
  deriving BEq, Repr

def ReadRequest.fieldCount (request : ReadRequest) : Nat :=
  (request.addresses.map ItemAddress.fieldCount).sum

/-- The request payload up to the fill, where the IntegrityId goes. -/
def ReadRequest.encodeBody (request : ReadRequest) : ByteArray :=
  uint32BE 0 ++ Vlq.encodeUInt32 (UInt32.ofNat request.addresses.length) ++
    Vlq.encodeUInt32 (UInt32.ofNat request.fieldCount) ++ encodeAddresses request.addresses ++
    encodeObjectQualifier request.form request.keyQualifier

/-- The request payload with an optional IntegrityId before the four fill bytes. -/
def ReadRequest.encode (request : ReadRequest) (integrityId : Option UInt32) : ByteArray :=
  request.encodeBody ++
    (match integrityId with
     | some id => Vlq.encodeUInt32 id
     | none => ByteArray.empty) ++ uint32BE 0

def decodeReadRequestBody (form : QualifierForm) (cursor : Cursor) :
    Except DecodeError (ReadRequest × Cursor) := do
  let (zero, cursor) ← cursor.readUInt32BE
  if zero != 0 then
    throw (.invalidField cursor.offset "GetMultiVariables request does not start with a zero word")
  let (count, cursor) ← Vlq.decodeUInt32 cursor
  let (fields, cursor) ← Vlq.decodeUInt32 cursor
  let (addresses, cursor) ← decodeAddresses count.toNat cursor
  let request := { addresses, form, keyQualifier := 0 : ReadRequest }
  if fields.toNat != request.fieldCount then
    throw (.invalidField cursor.offset "field count does not match the addresses")
  let (keyQualifier, cursor) ← decodeObjectQualifier form cursor
  pure ({ request with keyQualifier }, cursor)

/-- Decode a complete request payload: the body, an IntegrityId when `withIntegrity`,
    and the four zero fill bytes. -/
def decodeReadRequest (form : QualifierForm) (withIntegrity : Bool) (payload : ByteArray) :
    Except DecodeError (ReadRequest × Option UInt32) := do
  let (request, cursor) ← decodeReadRequestBody form { data := payload }
  let (integrityId, cursor) ← if withIntegrity then do
      let (id, cursor) ← Vlq.decodeUInt32 cursor
      pure (some id, cursor)
    else pure (none, cursor)
  let (fill, cursor) ← cursor.readUInt32BE
  if fill != 0 then
    throw (.invalidField cursor.offset "request fill bytes are not zero")
  cursor.finish
  pure (request, integrityId)

structure ReadReply where
  returnValue : UInt64
  values : List (UInt32 × Value)
  errors : List (UInt32 × UInt64)
  deriving BEq

def encodeValueList : List (UInt32 × Value) → ByteArray
  | [] => bytes #[0x00]
  | (item, value) :: rest => Vlq.encodeUInt32 item ++ value.encode ++ encodeValueList rest

def encodeErrorList : List (UInt32 × UInt64) → ByteArray
  | [] => bytes #[0x00]
  | (item, error) :: rest => Vlq.encodeUInt32 item ++ Vlq.encodeUInt64 error ++ encodeErrorList rest

def ReadReply.encode (reply : ReadReply) : ByteArray :=
  Vlq.encodeUInt64 reply.returnValue ++ encodeValueList reply.values ++ encodeErrorList reply.errors

def decodeValueList : Nat → Cursor → Except DecodeError (List (UInt32 × Value) × Cursor)
  | 0, cursor => .error (.invalidField cursor.offset "value list is too long")
  | fuel + 1, cursor => do
    let (item, cursor) ← Vlq.decodeUInt32 cursor
    if item = 0 then pure ([], cursor)
    else
      let (value, cursor) ← decodeValue cursor
      let (rest, cursor) ← decodeValueList fuel cursor
      pure ((item, value) :: rest, cursor)

def decodeErrorList : Nat → Cursor → Except DecodeError (List (UInt32 × UInt64) × Cursor)
  | 0, cursor => .error (.invalidField cursor.offset "error list is too long")
  | fuel + 1, cursor => do
    let (item, cursor) ← Vlq.decodeUInt32 cursor
    if item = 0 then pure ([], cursor)
    else
      let (error, cursor) ← Vlq.decodeUInt64 cursor
      let (rest, cursor) ← decodeErrorList fuel cursor
      pure ((item, error) :: rest, cursor)

/-- Decode a GetMultiVariables reply up to the end of its error list. -/
def decodeReadReply (cursor : Cursor) : Except DecodeError (ReadReply × Cursor) := do
  let (returnValue, cursor) ← Vlq.decodeUInt64 cursor
  let (values, cursor) ← decodeValueList cursor.remaining cursor
  let (errors, cursor) ← decodeErrorList cursor.remaining cursor
  pure ({ returnValue, values, errors }, cursor)

/-! ## Round trips -/

theorem decodeVlqList_encode (values : List UInt32) (pre suffix : ByteArray) :
    decodeVlqList values.length { data := pre ++ (encodeVlqList values ++ suffix), offset := pre.size } =
      .ok (values,
        { data := pre ++ (encodeVlqList values ++ suffix),
          offset := pre.size + (encodeVlqList values).size }) := by
  induction values generalizing pre with
  | nil => simp [decodeVlqList, encodeVlqList]
  | cons value rest ih =>
    have h := ih (pre ++ Vlq.encodeUInt32 value)
    simp only [ByteArray.size_append] at h
    simp only [ByteArray.append_assoc] at h
    simp only [List.length_cons, encodeVlqList, ByteArray.append_assoc]
    rw [decodeVlqList, Vlq.decodeUInt32_encodeUInt32]
    simp only [bind, Except.bind]
    rw [h]
    simp only [pure, Except.pure, ByteArray.size_append, Nat.add_assoc]

/-- An address whose LID count fits its VLQ field. -/
def ItemAddress.Fits (address : ItemAddress) : Prop :=
  address.lids.length + 1 < 2 ^ 32

theorem decodeItemAddress_encode (address : ItemAddress) (hfit : address.Fits)
    (pre suffix : ByteArray) :
    decodeItemAddress { data := pre ++ (address.encode ++ suffix), offset := pre.size } =
      .ok (address,
        { data := pre ++ (address.encode ++ suffix),
          offset := pre.size + address.encode.size }) := by
  have hids : (UInt32.ofNat (address.lids.length + 1)).toNat = address.lids.length + 1 := by
    rw [UInt32.toNat_ofNat']; unfold ItemAddress.Fits at hfit; omega
  have hne : ¬ UInt32.ofNat (address.lids.length + 1) = 0 := by
    intro h; have := congrArg UInt32.toNat h; rw [hids] at this; simp at this
  have r1 := Vlq.decodeUInt32_encodeUInt32 address.accessArea (pre ++ Vlq.encodeUInt32 address.symbolCrc)
    (Vlq.encodeUInt32 (UInt32.ofNat (address.lids.length + 1)) ++
      (Vlq.encodeUInt32 address.accessSubArea ++ (encodeVlqList address.lids ++ suffix)))
  have r2 := Vlq.decodeUInt32_encodeUInt32 (UInt32.ofNat (address.lids.length + 1))
    (pre ++ Vlq.encodeUInt32 address.symbolCrc ++ Vlq.encodeUInt32 address.accessArea)
    (Vlq.encodeUInt32 address.accessSubArea ++ (encodeVlqList address.lids ++ suffix))
  have r3 := Vlq.decodeUInt32_encodeUInt32 address.accessSubArea
    (pre ++ Vlq.encodeUInt32 address.symbolCrc ++ Vlq.encodeUInt32 address.accessArea ++
      Vlq.encodeUInt32 (UInt32.ofNat (address.lids.length + 1)))
    (encodeVlqList address.lids ++ suffix)
  have r4 := decodeVlqList_encode address.lids
    (pre ++ Vlq.encodeUInt32 address.symbolCrc ++ Vlq.encodeUInt32 address.accessArea ++
      Vlq.encodeUInt32 (UInt32.ofNat (address.lids.length + 1)) ++
      Vlq.encodeUInt32 address.accessSubArea) suffix
  simp only [ByteArray.size_append] at r1 r2 r3 r4
  simp only [ByteArray.append_assoc] at r1 r2 r3 r4
  simp only [ItemAddress.encode, ByteArray.append_assoc]
  unfold decodeItemAddress
  rw [Vlq.decodeUInt32_encodeUInt32]
  simp only [bind, Except.bind]
  rw [r1]
  simp only
  rw [r2]
  simp only [hne, if_false]
  rw [r3]
  simp only [hids, Nat.add_sub_cancel]
  rw [r4]
  simp only [pure, Except.pure, ByteArray.size_append, Nat.add_assoc]

theorem decodeAddresses_encode (addresses : List ItemAddress) (hfit : ∀ a ∈ addresses, a.Fits)
    (pre suffix : ByteArray) :
    decodeAddresses addresses.length
        { data := pre ++ (encodeAddresses addresses ++ suffix), offset := pre.size } =
      .ok (addresses,
        { data := pre ++ (encodeAddresses addresses ++ suffix),
          offset := pre.size + (encodeAddresses addresses).size }) := by
  induction addresses generalizing pre with
  | nil => simp [decodeAddresses, encodeAddresses]
  | cons address rest ih =>
    have h := ih (fun a ha => hfit a (by simp [ha])) (pre ++ address.encode)
    simp only [ByteArray.size_append] at h
    simp only [ByteArray.append_assoc] at h
    simp only [List.length_cons, encodeAddresses, ByteArray.append_assoc]
    rw [decodeAddresses, decodeItemAddress_encode address (hfit address (by simp))]
    simp only [bind, Except.bind]
    rw [h]
    simp only [pure, Except.pure, ByteArray.size_append, Nat.add_assoc]

theorem byteArray_bne_self (data : ByteArray) : (data != data) = false := by
  simp only [bne, BEq.beq, ByteArray.beq, Bool.not_eq_false']
  exact Array.isEqv_self _

/-- The KeyQualifier value bytes of a form. -/
def qualifierTail (form : QualifierForm) (keyQualifier : UInt32) : ByteArray :=
  match form with
  | .fixed => uint32BE keyQualifier
  | .vlq => Vlq.encodeUInt32 keyQualifier ++ bytes #[0x00]

theorem encodeObjectQualifier_split (form : QualifierForm) (keyQualifier : UInt32) :
    encodeObjectQualifier form keyQualifier = objectQualifierPrefix ++ qualifierTail form keyQualifier := by
  cases form <;> rfl

theorem decodeObjectQualifier_encode (form : QualifierForm) (keyQualifier : UInt32)
    (pre suffix : ByteArray) :
    decodeObjectQualifier form
        { data := pre ++ (encodeObjectQualifier form keyQualifier ++ suffix), offset := pre.size } =
      .ok (keyQualifier,
        { data := pre ++ (encodeObjectQualifier form keyQualifier ++ suffix),
          offset := pre.size + (encodeObjectQualifier form keyQualifier).size }) := by
  rw [encodeObjectQualifier_split, ByteArray.append_assoc]
  have r0 := Cursor.readBytes_append pre objectQualifierPrefix (qualifierTail form keyQualifier ++ suffix)
  unfold decodeObjectQualifier
  rw [r0]
  simp only [bind, Except.bind, byteArray_bne_self, Bool.false_eq_true, if_false]
  cases form with
  | fixed =>
    have r1 := Cursor.readUInt32BE_append_uint32BE (pre ++ objectQualifierPrefix) suffix keyQualifier
    simp only [ByteArray.size_append] at r1
    simp only [ByteArray.append_assoc] at r1
    simp only [qualifierTail] at r1 ⊢
    rw [r1]
    simp only [ByteArray.size_append, uint32BE_size, Nat.add_assoc]
  | vlq =>
    have r1 := Vlq.decodeUInt32_encodeUInt32 keyQualifier (pre ++ objectQualifierPrefix)
      (bytes #[0x00] ++ suffix)
    have r2 := Cursor.readUInt8_append_byte
      (pre ++ objectQualifierPrefix ++ Vlq.encodeUInt32 keyQualifier) suffix 0x00
    simp only [ByteArray.size_append] at r1 r2
    simp only [ByteArray.append_assoc] at r1 r2
    simp only [qualifierTail, ByteArray.append_assoc] at ⊢
    rw [r1]
    simp only
    rw [r2]
    simp only [bne_self_eq_false, Bool.false_eq_true, if_false, pure, Except.pure,
      ByteArray.size_append, bytes_size, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.add_assoc]

/-- A request whose counts fit their VLQ fields. -/
def ReadRequest.Fits (request : ReadRequest) : Prop :=
  (∀ address ∈ request.addresses, address.Fits) ∧ request.addresses.length < 2 ^ 32 ∧
    request.fieldCount < 2 ^ 32

theorem decodeReadRequestBody_encode (request : ReadRequest) (hfit : request.Fits)
    (pre suffix : ByteArray) :
    decodeReadRequestBody request.form
        { data := pre ++ (request.encodeBody ++ suffix), offset := pre.size } =
      .ok (request,
        { data := pre ++ (request.encodeBody ++ suffix),
          offset := pre.size + request.encodeBody.size }) := by
  obtain ⟨haddr, hcount, hfields⟩ := hfit
  have hcountNat : (UInt32.ofNat request.addresses.length).toNat = request.addresses.length := by
    rw [UInt32.toNat_ofNat']; omega
  have hfieldsNat : (UInt32.ofNat request.fieldCount).toNat = request.fieldCount := by
    rw [UInt32.toNat_ofNat']; omega
  have r1 := Vlq.decodeUInt32_encodeUInt32 (UInt32.ofNat request.addresses.length) (pre ++ uint32BE 0)
    (Vlq.encodeUInt32 (UInt32.ofNat request.fieldCount) ++ (encodeAddresses request.addresses ++
      (encodeObjectQualifier request.form request.keyQualifier ++ suffix)))
  have r2 := Vlq.decodeUInt32_encodeUInt32 (UInt32.ofNat request.fieldCount)
    (pre ++ uint32BE 0 ++ Vlq.encodeUInt32 (UInt32.ofNat request.addresses.length))
    (encodeAddresses request.addresses ++ (encodeObjectQualifier request.form request.keyQualifier ++ suffix))
  have r3 := decodeAddresses_encode request.addresses haddr
    (pre ++ uint32BE 0 ++ Vlq.encodeUInt32 (UInt32.ofNat request.addresses.length) ++
      Vlq.encodeUInt32 (UInt32.ofNat request.fieldCount))
    (encodeObjectQualifier request.form request.keyQualifier ++ suffix)
  have r4 := decodeObjectQualifier_encode request.form request.keyQualifier
    (pre ++ uint32BE 0 ++ Vlq.encodeUInt32 (UInt32.ofNat request.addresses.length) ++
      Vlq.encodeUInt32 (UInt32.ofNat request.fieldCount) ++ encodeAddresses request.addresses) suffix
  simp only [ByteArray.size_append, uint32BE_size] at r1 r2 r3 r4
  simp only [ByteArray.append_assoc, ReadRequest.fieldCount] at r1 r2 r3 r4
  simp only [ReadRequest.encodeBody, ByteArray.append_assoc, ReadRequest.fieldCount]
  unfold decodeReadRequestBody
  rw [Cursor.readUInt32BE_append_uint32BE]
  simp only [bind, Except.bind, bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [r1]
  simp only
  rw [r2]
  simp only [hcountNat]
  rw [r3]
  simp only [ReadRequest.fieldCount] at hfieldsNat
  simp only [hfieldsNat, ReadRequest.fieldCount, bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [r4]
  simp only [pure, Except.pure, ByteArray.size_append, uint32BE_size, Nat.add_assoc]

/-- Decoding a complete request payload built by `ReadRequest.encode` returns the
    request and its IntegrityId. -/
theorem decodeReadRequest_encode (request : ReadRequest) (hfit : request.Fits)
    (integrityId : Option UInt32) :
    decodeReadRequest request.form integrityId.isSome (request.encode integrityId) =
      .ok (request, integrityId) := by
  cases integrityId with
  | none =>
    have hbody := decodeReadRequestBody_encode request hfit ByteArray.empty (uint32BE 0)
    have hfill := Cursor.readUInt32BE_append_uint32BE request.encodeBody ByteArray.empty 0
    simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at hbody
    simp only [ByteArray.append_empty] at hfill
    have hpayload : request.encode none = request.encodeBody ++ uint32BE 0 := by
      simp [ReadRequest.encode]
    rw [hpayload]
    unfold decodeReadRequest
    rw [show ({ data := request.encodeBody ++ uint32BE 0 } : Cursor) =
      { data := request.encodeBody ++ uint32BE 0, offset := 0 } from rfl, hbody]
    simp only [bind, Except.bind, Option.isSome_none, Bool.false_eq_true, if_false, pure,
      Except.pure]
    rw [hfill]
    simp [Cursor.finish, ByteArray.size_append]
  | some id =>
    have hbody := decodeReadRequestBody_encode request hfit ByteArray.empty
      (Vlq.encodeUInt32 id ++ uint32BE 0)
    have hid := Vlq.decodeUInt32_encodeUInt32 id request.encodeBody (uint32BE 0)
    have hfill := Cursor.readUInt32BE_append_uint32BE (request.encodeBody ++ Vlq.encodeUInt32 id)
      ByteArray.empty 0
    simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at hbody
    simp only [ByteArray.size_append] at hfill
    simp only [ByteArray.append_empty, ByteArray.append_assoc] at hfill
    have hpayload : request.encode (some id) = request.encodeBody ++ (Vlq.encodeUInt32 id ++ uint32BE 0) := by
      simp [ReadRequest.encode, ByteArray.append_assoc]
    rw [hpayload]
    unfold decodeReadRequest
    rw [show ({ data := request.encodeBody ++ (Vlq.encodeUInt32 id ++ uint32BE 0) } : Cursor) =
      { data := request.encodeBody ++ (Vlq.encodeUInt32 id ++ uint32BE 0), offset := 0 } from rfl, hbody]
    simp only [bind, Except.bind, Option.isSome_some, if_true]
    rw [hid]
    simp only [pure, Except.pure]
    rw [hfill]
    simp only [Cursor.finish, ByteArray.size_append, uint32BE_size, bne_self_eq_false,
      Bool.false_eq_true, if_false, Nat.add_assoc, if_true]

theorem encodeUInt32_zero : Vlq.encodeUInt32 0 = bytes #[0x00] := by
  simp only [Vlq.encodeUInt32, Vlq.encodeNat, UInt32.toNat_zero]
  rw [Vlq.groups, if_pos (by decide)]
  rfl

def ReadReply.Fits (reply : ReadReply) : Prop :=
  (∀ entry ∈ reply.values, entry.1 ≠ 0 ∧ entry.2.Fits) ∧ (∀ entry ∈ reply.errors, entry.1 ≠ 0)

theorem encodeValueList_size (values : List (UInt32 × Value)) :
    values.length + 1 ≤ (encodeValueList values).size := by
  induction values with
  | nil => simp [encodeValueList]
  | cons entry rest ih =>
    have := (Vlq.encodeUInt32_size entry.1).1
    simp only [encodeValueList, ByteArray.size_append, List.length_cons]
    omega

theorem encodeErrorList_size (errors : List (UInt32 × UInt64)) :
    errors.length + 1 ≤ (encodeErrorList errors).size := by
  induction errors with
  | nil => simp [encodeErrorList]
  | cons entry rest ih =>
    have := (Vlq.encodeUInt32_size entry.1).1
    simp only [encodeErrorList, ByteArray.size_append, List.length_cons]
    omega

theorem decodeValueList_encode (values : List (UInt32 × Value))
    (hfit : ∀ entry ∈ values, entry.1 ≠ 0 ∧ entry.2.Fits) (fuel : Nat)
    (hfuel : values.length + 1 ≤ fuel) (pre suffix : ByteArray) :
    decodeValueList fuel { data := pre ++ (encodeValueList values ++ suffix), offset := pre.size } =
      .ok (values,
        { data := pre ++ (encodeValueList values ++ suffix),
          offset := pre.size + (encodeValueList values).size }) := by
  induction values generalizing fuel pre with
  | nil =>
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have h := Vlq.decodeUInt32_encodeUInt32 0 pre suffix
    rw [encodeUInt32_zero] at h
    simp only [encodeValueList]
    rw [decodeValueList, h]
    simp [bind, Except.bind, pure, Except.pure]
  | cons entry rest ih =>
    obtain ⟨item, value⟩ := entry
    obtain ⟨hitem, hvalue⟩ := hfit (item, value) (by simp)
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have r1 := decodeValue_encode value hvalue (pre ++ Vlq.encodeUInt32 item)
      (encodeValueList rest ++ suffix)
    have r2 := ih (fun e he => hfit e (by simp [he])) fuel (by simp at hfuel; omega)
      (pre ++ Vlq.encodeUInt32 item ++ value.encode)
    simp only [ByteArray.size_append] at r1 r2
    simp only [ByteArray.append_assoc] at r1 r2
    simp only [encodeValueList, ByteArray.append_assoc]
    rw [decodeValueList, Vlq.decodeUInt32_encodeUInt32]
    simp only [bind, Except.bind, show ¬ item = 0 from hitem, if_false]
    rw [r1]
    simp only
    rw [r2]
    simp only [pure, Except.pure, ByteArray.size_append, Nat.add_assoc]

theorem decodeErrorList_encode (errors : List (UInt32 × UInt64))
    (hfit : ∀ entry ∈ errors, entry.1 ≠ 0) (fuel : Nat)
    (hfuel : errors.length + 1 ≤ fuel) (pre suffix : ByteArray) :
    decodeErrorList fuel { data := pre ++ (encodeErrorList errors ++ suffix), offset := pre.size } =
      .ok (errors,
        { data := pre ++ (encodeErrorList errors ++ suffix),
          offset := pre.size + (encodeErrorList errors).size }) := by
  induction errors generalizing fuel pre with
  | nil =>
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have h := Vlq.decodeUInt32_encodeUInt32 0 pre suffix
    rw [encodeUInt32_zero] at h
    simp only [encodeErrorList]
    rw [decodeErrorList, h]
    simp [bind, Except.bind, pure, Except.pure]
  | cons entry rest ih =>
    obtain ⟨item, error⟩ := entry
    have hitem := hfit (item, error) (by simp)
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have r1 := Vlq.decodeUInt64_encodeUInt64 error (pre ++ Vlq.encodeUInt32 item)
      (encodeErrorList rest ++ suffix)
    have r2 := ih (fun e he => hfit e (by simp [he])) fuel (by simp at hfuel; omega)
      (pre ++ Vlq.encodeUInt32 item ++ Vlq.encodeUInt64 error)
    simp only [ByteArray.size_append] at r1 r2
    simp only [ByteArray.append_assoc] at r1 r2
    simp only [encodeErrorList, ByteArray.append_assoc]
    rw [decodeErrorList, Vlq.decodeUInt32_encodeUInt32]
    simp only [bind, Except.bind, show ¬ item = 0 from hitem, if_false]
    rw [r1]
    simp only
    rw [r2]
    simp only [pure, Except.pure, ByteArray.size_append, Nat.add_assoc]

/-- Decoding the encoding of any reply, inside arbitrary surrounding bytes, returns the
    reply and consumes exactly its encoding. -/
theorem decodeReadReply_encode (reply : ReadReply) (hfit : reply.Fits) (pre suffix : ByteArray) :
    decodeReadReply { data := pre ++ (reply.encode ++ suffix), offset := pre.size } =
      .ok (reply,
        { data := pre ++ (reply.encode ++ suffix), offset := pre.size + reply.encode.size }) := by
  obtain ⟨hvalues, herrors⟩ := hfit
  have hv := encodeValueList_size reply.values
  have he := encodeErrorList_size reply.errors
  have r1 := decodeValueList_encode reply.values hvalues
    ((pre ++ (Vlq.encodeUInt64 reply.returnValue ++ (encodeValueList reply.values ++
      (encodeErrorList reply.errors ++ suffix)))).size - (pre.size +
        (Vlq.encodeUInt64 reply.returnValue).size)) (by simp only [ByteArray.size_append]; omega)
    (pre ++ Vlq.encodeUInt64 reply.returnValue) (encodeErrorList reply.errors ++ suffix)
  have r2 := decodeErrorList_encode reply.errors herrors
    ((pre ++ (Vlq.encodeUInt64 reply.returnValue ++ (encodeValueList reply.values ++
      (encodeErrorList reply.errors ++ suffix)))).size - (pre.size +
        (Vlq.encodeUInt64 reply.returnValue).size + (encodeValueList reply.values).size))
    (by simp only [ByteArray.size_append]; omega)
    (pre ++ Vlq.encodeUInt64 reply.returnValue ++ encodeValueList reply.values) suffix
  simp only [ByteArray.size_append] at r1 r2
  simp only [ByteArray.append_assoc] at r1 r2
  simp only [ReadReply.encode, ByteArray.append_assoc]
  unfold decodeReadReply
  rw [Vlq.decodeUInt64_encodeUInt64]
  simp only [bind, Except.bind, Cursor.remaining, ByteArray.size_append]
  rw [r1]
  simp only [ByteArray.size_append]
  rw [r2]
  simp only [pure, Except.pure, Nat.add_assoc]

/-! ## Canonical form -/

/-- A list of 32-bit VLQs, each in an accepted form, back to back. -/
def VlqListForm : List UInt32 → ByteArray → Prop
  | [], input => input = ByteArray.empty
  | value :: rest, input => ∃ first others, input = first ++ others ∧
      Vlq.UInt32Form value first ∧ VlqListForm rest others

theorem decodeVlqList_canonical (count : Nat) (cursor next : Cursor) (values : List UInt32)
    (h : decodeVlqList count cursor = .ok (values, next)) :
    next.data = cursor.data ∧ cursor.offset ≤ next.offset ∧ values.length = count ∧
      VlqListForm values (cursor.data.extract cursor.offset next.offset) := by
  induction count generalizing cursor next values with
  | zero =>
    simp only [decodeVlqList, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, Nat.le_refl _, rfl, extract_self _ _⟩
  | succ count ih =>
    simp only [decodeVlqList, bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i _ r1 h1
      obtain ⟨hd1, hle1, hf1⟩ := Vlq.decodeUInt32_form _ _ _ h1
      split at h
      · contradiction
      · rename_i _ r2 h2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hd2, hle2, hlen, hf2⟩ := ih _ _ _ h2
        rw [hd1] at hf2
        exact ⟨by rw [hd2, hd1], by omega, by simp [hlen], _, _,
          (ByteArray.extract_append_extract_of_le _ hle1 hle2).symm, hf1, hf2⟩

/-- Elements back to back, each in its accepted form. -/
def JoinForm {α : Type} (form : α → ByteArray → Prop) : List α → ByteArray → Prop
  | [], input => input = ByteArray.empty
  | element :: rest, input => ∃ first others, input = first ++ others ∧ form element first ∧
      JoinForm form rest others

/-- The bytes `decodeItemAddress` accepts: five VLQ fields, the third being the number
    of LIDs plus one. -/
def ItemAddress.Form (address : ItemAddress) (input : ByteArray) : Prop :=
  ∃ crcBytes areaBytes countBytes subAreaBytes lidsBytes,
    input = crcBytes ++ areaBytes ++ countBytes ++ subAreaBytes ++ lidsBytes ∧
    Vlq.UInt32Form address.symbolCrc crcBytes ∧ Vlq.UInt32Form address.accessArea areaBytes ∧
    Vlq.UInt32Form (UInt32.ofNat (address.lids.length + 1)) countBytes ∧
    address.lids.length + 1 < 2 ^ 32 ∧
    Vlq.UInt32Form address.accessSubArea subAreaBytes ∧ VlqListForm address.lids lidsBytes

theorem decodeItemAddress_canonical (cursor next : Cursor) (address : ItemAddress)
    (h : decodeItemAddress cursor = .ok (address, next)) :
    next.data = cursor.data ∧ cursor.offset ≤ next.offset ∧
      address.Form (cursor.data.extract cursor.offset next.offset) := by
  simp only [decodeItemAddress, bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i _ r1 h1
    obtain ⟨hd1, hle1, hf1⟩ := Vlq.decodeUInt32_form _ _ _ h1
    split at h
    · contradiction
    · rename_i _ r2 h2
      obtain ⟨hd2, hle2, hf2⟩ := Vlq.decodeUInt32_form _ _ _ h2
      split at h
      · contradiction
      · rename_i _ r3 h3
        obtain ⟨hd3, hle3, hf3⟩ := Vlq.decodeUInt32_form _ _ _ h3
        rcases ite_eq_cases h with ⟨-, h⟩ | ⟨hids, h⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · contradiction
          · rename_i _ r4 h4
            obtain ⟨hd4, hle4, hf4⟩ := Vlq.decodeUInt32_form _ _ _ h4
            split at h
            · contradiction
            · rename_i _ r5 h5
              obtain ⟨hd5, hle5, hlen5, hf5⟩ := decodeVlqList_canonical _ _ _ _ h5
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hpos : 1 ≤ r3.fst.toNat := by
                have : r3.fst.toNat ≠ 0 := fun hz => hids (UInt32.toNat_inj.mp (by simpa using hz))
                omega
              have hcount : UInt32.ofNat (r5.fst.length + 1) = r3.fst := by
                rw [hlen5, show r3.fst.toNat - 1 + 1 = r3.fst.toNat by omega, UInt32.ofNat_toNat]
              rw [hd1] at hf2
              rw [hd2, hd1] at hf3
              rw [hd3, hd2, hd1] at hf4
              rw [hd4, hd3, hd2, hd1] at hf5
              refine ⟨by rw [hd5, hd4, hd3, hd2, hd1], by omega, _, _, _, _, _, ?_, hf1, hf2,
                by rw [hcount]; exact hf3, by rw [hlen5]; have := r3.fst.toNat_lt; omega,
                hf4, hf5⟩
              rw [ByteArray.extract_append_extract_of_le _ hle1 hle2,
                ByteArray.extract_append_extract_of_le _ (by omega) hle3,
                ByteArray.extract_append_extract_of_le _ (by omega) hle4,
                ByteArray.extract_append_extract_of_le _ (by omega) hle5]

theorem decodeAddresses_canonical (count : Nat) (cursor next : Cursor)
    (addresses : List ItemAddress) (h : decodeAddresses count cursor = .ok (addresses, next)) :
    next.data = cursor.data ∧ cursor.offset ≤ next.offset ∧ addresses.length = count ∧
      JoinForm ItemAddress.Form addresses (cursor.data.extract cursor.offset next.offset) := by
  induction count generalizing cursor next addresses with
  | zero =>
    simp only [decodeAddresses, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, Nat.le_refl _, rfl, extract_self _ _⟩
  | succ count ih =>
    simp only [decodeAddresses, bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i _ r1 h1
      obtain ⟨hd1, hle1, hf1⟩ := decodeItemAddress_canonical _ _ _ h1
      split at h
      · contradiction
      · rename_i _ r2 h2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hd2, hle2, hlen, hf2⟩ := ih _ _ _ h2
        rw [hd1] at hf2
        exact ⟨by rw [hd2, hd1], by omega, by simp [hlen], _, _,
          (ByteArray.extract_append_extract_of_le _ hle1 hle2).symm, hf1, hf2⟩

/-- The bytes `decodeObjectQualifier` accepts: the fixed prefix exactly, then the
    KeyQualifier as a big-endian word, or as a VLQ in any form and a zero byte. -/
def ObjectQualifierForm : QualifierForm → UInt32 → ByteArray → Prop
  | .fixed, keyQualifier, input => input = objectQualifierPrefix ++ uint32BE keyQualifier
  | .vlq, keyQualifier, input => ∃ keyBytes,
      input = objectQualifierPrefix ++ keyBytes ++ bytes #[0x00] ∧
      Vlq.UInt32Form keyQualifier keyBytes

theorem decodeObjectQualifier_canonical (form : QualifierForm) (cursor next : Cursor)
    (keyQualifier : UInt32) (h : decodeObjectQualifier form cursor = .ok (keyQualifier, next)) :
    next.data = cursor.data ∧ cursor.offset ≤ next.offset ∧
      ObjectQualifierForm form keyQualifier (cursor.data.extract cursor.offset next.offset) := by
  simp only [decodeObjectQualifier, bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i _ r1 h1
    obtain ⟨hp1, hn1⟩ := readBytes_extract _ _ _ _ h1
    rcases ite_eq_cases h with ⟨-, h⟩ | ⟨hprefix, h⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · have hprefix : r1.fst = objectQualifierPrefix :=
        ByteArray.eq_of_bne_false (by simpa using hprefix)
      rw [hprefix] at hp1
      cases form with
      | fixed =>
        simp only at h
        rw [hn1] at h
        obtain ⟨-, hx, hn⟩ := readUInt32BE_value _ _ _ h
        refine ⟨by rw [hn], by rw [hn]; dsimp only; omega, ?_⟩
        show _ = _ ++ _
        rw [hn]
        dsimp only
        rw [← ByteArray.extract_append_extract_of_le _ (Nat.le_add_right _ objectQualifierPrefix.size)
          (Nat.le_add_right _ 4), ← hp1, ← hx]
      | vlq =>
        simp only at h
        split at h
        · contradiction
        · rename_i _ r2 h2
          rw [hn1] at h2
          obtain ⟨hd2, hle2, hf2⟩ := Vlq.decodeUInt32_form _ _ _ h2
          simp only at hd2 hle2 hf2
          split at h
          · contradiction
          · rename_i _ r3 h3
            obtain ⟨-, hx3, hn3⟩ := readUInt8_extract _ _ _ h3
            rw [hd2] at hx3
            rcases ite_eq_cases h with ⟨-, h⟩ | ⟨hterm, h⟩
            · simp [throw, throwThe, MonadExceptOf.throw] at h
            · have hterm : r3.fst = 0x00 := by simpa using hterm
              rw [hterm] at hx3
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨by rw [hn3, hd2], by rw [hn3]; dsimp only; omega, _, ?_, hf2⟩
              rw [hn3]
              dsimp only
              have hsplit : cursor.data.extract cursor.offset (r2.snd.offset + 1) =
                  cursor.data.extract cursor.offset (cursor.offset + objectQualifierPrefix.size) ++
                    cursor.data.extract (cursor.offset + objectQualifierPrefix.size) r2.snd.offset ++
                    cursor.data.extract r2.snd.offset (r2.snd.offset + 1) := by
                rw [ByteArray.extract_append_extract_of_le _ (by omega) hle2,
                  ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]
              rw [hsplit, ← hp1, ← hx3]

/-- The bytes `decodeReadRequestBody` accepts for a request. -/
def ReadRequest.BodyForm (request : ReadRequest) (input : ByteArray) : Prop :=
  ∃ countBytes fieldsBytes addressBytes qualifierBytes,
    input = uint32BE 0 ++ countBytes ++ fieldsBytes ++ addressBytes ++ qualifierBytes ∧
    Vlq.UInt32Form (UInt32.ofNat request.addresses.length) countBytes ∧
    request.addresses.length < 2 ^ 32 ∧
    Vlq.UInt32Form (UInt32.ofNat request.fieldCount) fieldsBytes ∧ request.fieldCount < 2 ^ 32 ∧
    JoinForm ItemAddress.Form request.addresses addressBytes ∧
    ObjectQualifierForm request.form request.keyQualifier qualifierBytes

theorem decodeReadRequestBody_canonical (form : QualifierForm) (cursor next : Cursor)
    (request : ReadRequest) (h : decodeReadRequestBody form cursor = .ok (request, next)) :
    next.data = cursor.data ∧ cursor.offset ≤ next.offset ∧ request.form = form ∧
      request.BodyForm (cursor.data.extract cursor.offset next.offset) := by
  simp only [decodeReadRequestBody, bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i _ r1 h1
    obtain ⟨-, hx1, hn1⟩ := readUInt32BE_value _ _ _ h1
    rcases ite_eq_cases h with ⟨-, h⟩ | ⟨hzero, h⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · have hzero : r1.fst = 0 := by simpa using hzero
      rw [hzero] at hx1
      split at h
      · contradiction
      · rename_i _ r2 h2
        rw [hn1] at h2
        obtain ⟨hd2, hle2, hf2⟩ := Vlq.decodeUInt32_form _ _ _ h2
        simp only at hd2 hle2 hf2
        split at h
        · contradiction
        · rename_i _ r3 h3
          obtain ⟨hd3, hle3, hf3⟩ := Vlq.decodeUInt32_form _ _ _ h3
          rw [hd2] at hf3
          split at h
          · contradiction
          · rename_i _ r4 h4
            obtain ⟨hd4, hle4, hlen4, hf4⟩ := decodeAddresses_canonical _ _ _ _ h4
            rw [hd3, hd2] at hf4
            rcases ite_eq_cases h with ⟨-, h⟩ | ⟨hfields, h⟩
            · simp [throw, throwThe, MonadExceptOf.throw] at h
            · have hfields : r3.fst.toNat = ReadRequest.fieldCount
                  { addresses := r4.fst, form := form, keyQualifier := 0 } := by
                simpa using hfields
              split at h
              · contradiction
              · rename_i _ r5 h5
                obtain ⟨hd5, hle5, hf5⟩ := decodeObjectQualifier_canonical _ _ _ _ h5
                rw [hd4, hd3, hd2] at hf5
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have hcount : UInt32.ofNat r4.fst.length = r2.fst := by
                  rw [hlen4, UInt32.ofNat_toNat]
                have hfc : ReadRequest.fieldCount
                    { addresses := r4.fst, form := form, keyQualifier := r5.fst } = r3.fst.toNat := by
                  rw [hfields]; rfl
                refine ⟨by rw [hd5, hd4, hd3, hd2], by omega, rfl, _, _, _, _, ?_,
                  by simp only; rw [hcount]; exact hf2,
                  by simp only; rw [hlen4]; exact r2.fst.toNat_lt,
                  by rw [hfc, UInt32.ofNat_toNat]; exact hf3,
                  by rw [hfc]; exact r3.fst.toNat_lt, hf4, hf5⟩
                rw [hx1, ByteArray.extract_append_extract_of_le _ (by omega) hle2,
                  ByteArray.extract_append_extract_of_le _ (by omega) hle3,
                  ByteArray.extract_append_extract_of_le _ (by omega) hle4,
                  ByteArray.extract_append_extract_of_le _ (by omega) hle5]

/-- Canonical form of a GetMultiVariables request payload: the whole payload is an
    accepted body, the IntegrityId in any 32-bit form when one is expected, and four
    zero fill bytes. -/
theorem decodeReadRequest_canonical (form : QualifierForm) (withIntegrity : Bool)
    (payload : ByteArray) (request : ReadRequest) (integrityId : Option UInt32)
    (h : decodeReadRequest form withIntegrity payload = .ok (request, integrityId)) :
    request.form = form ∧ ∃ body idBytes, payload = body ++ idBytes ++ uint32BE 0 ∧
      request.BodyForm body ∧
      (match integrityId with
       | none => withIntegrity = false ∧ idBytes = ByteArray.empty
       | some id => withIntegrity = true ∧ Vlq.UInt32Form id idBytes) := by
  -- the fill and the end of the payload, after the body and the IntegrityId
  have tail : ∀ (cursor : Cursor) (fill : UInt32) (afterFill : Cursor),
      cursor.data = payload → cursor.readUInt32BE = .ok (fill, afterFill) → fill = 0 →
      afterFill.finish = .ok () →
      payload.extract cursor.offset payload.size = uint32BE 0 := by
    intro cursor fill afterFill hdata hread hfill hfinish
    obtain ⟨-, hx, hn⟩ := readUInt32BE_value _ _ _ hread
    have hend := Cursor.finish_ok _ hfinish
    rw [hn] at hend
    simp only at hend
    rw [hdata] at hx hend
    rw [← hend, ← hx, hfill]
  cases withIntegrity with
  | false =>
    simp only [decodeReadRequest, bind, Except.bind, Bool.false_eq_true, if_false, pure,
      Except.pure] at h
    split at h
    · contradiction
    · rename_i _ r1 h1
      obtain ⟨hd1, hle1, hform, hf1⟩ := decodeReadRequestBody_canonical _ _ _ _ h1
      simp only at hd1 hle1 hf1
      split at h
      · contradiction
      · rename_i _ r3 h3
        rcases ite_eq_cases h with ⟨-, h⟩ | ⟨hfill, h⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · have hfill : r3.fst = 0 := by simpa using hfill
          split at h
          · contradiction
          · rename_i _ r4 h4
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have htail := tail _ _ _ hd1 h3 hfill h4
            have hsz := congrArg ByteArray.size htail
            simp only [ByteArray.size_extract, uint32BE_size, Nat.min_self] at hsz
            refine ⟨hform, _, ByteArray.empty, ?_, hf1, rfl, rfl⟩
            rw [ByteArray.append_empty, ← htail,
              ByteArray.extract_append_extract_of_le _ (Nat.zero_le _) (by omega)]
            exact ByteArray.extract_zero_size.symm
  | true =>
    simp only [decodeReadRequest, bind, Except.bind, if_true, pure, Except.pure] at h
    split at h
    · contradiction
    · rename_i _ r1 h1
      obtain ⟨hd1, hle1, hform, hf1⟩ := decodeReadRequestBody_canonical _ _ _ _ h1
      simp only at hd1 hle1 hf1
      split at h
      · contradiction
      · rename_i _ r2 h2
        obtain ⟨hd2, hle2, hf2⟩ := Vlq.decodeUInt32_form _ _ _ h2
        rw [hd1] at hd2 hf2
        split at h
        · contradiction
        · rename_i _ r3 h3
          rcases ite_eq_cases h with ⟨-, h⟩ | ⟨hfill, h⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · have hfill : r3.fst = 0 := by simpa using hfill
            split at h
            · contradiction
            · rename_i _ r4 h4
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have htail := tail _ _ _ hd2 h3 hfill h4
              have hsz := congrArg ByteArray.size htail
              simp only [ByteArray.size_extract, uint32BE_size, Nat.min_self] at hsz
              refine ⟨hform, _, _, ?_, hf1, rfl, hf2⟩
              rw [← htail, ByteArray.extract_append_extract_of_le _ (Nat.zero_le _) hle2,
                ByteArray.extract_append_extract_of_le _ (Nat.zero_le _) (by omega)]
              exact ByteArray.extract_zero_size.symm

/-- A value-list entry: a nonzero item number in any 32-bit form and a value. -/
def ValueEntryForm (entry : UInt32 × Value) (input : ByteArray) : Prop :=
  ∃ itemBytes valueBytes, input = itemBytes ++ valueBytes ∧ Vlq.UInt32Form entry.1 itemBytes ∧
    entry.1 ≠ 0 ∧ entry.2.Form valueBytes

/-- An error-list entry: a nonzero item number and a 64-bit error, each in any form. -/
def ErrorEntryForm (entry : UInt32 × UInt64) (input : ByteArray) : Prop :=
  ∃ itemBytes errorBytes, input = itemBytes ++ errorBytes ∧ Vlq.UInt32Form entry.1 itemBytes ∧
    entry.1 ≠ 0 ∧ Vlq.UInt64Form entry.2 errorBytes

/-- A list ended by item number 0, which may itself take any 32-bit form (`80 00`). -/
def TerminatedForm {α : Type} (form : α → ByteArray → Prop) (entries : List α)
    (input : ByteArray) : Prop :=
  ∃ body terminator, input = body ++ terminator ∧ JoinForm form entries body ∧
    Vlq.UInt32Form 0 terminator

theorem decodeValueList_canonical (fuel : Nat) (cursor next : Cursor)
    (values : List (UInt32 × Value)) (h : decodeValueList fuel cursor = .ok (values, next)) :
    next.data = cursor.data ∧ cursor.offset ≤ next.offset ∧
      TerminatedForm ValueEntryForm values (cursor.data.extract cursor.offset next.offset) := by
  induction fuel generalizing cursor next values with
  | zero => simp [decodeValueList] at h
  | succ fuel ih =>
    simp only [decodeValueList, bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i _ r1 h1
      obtain ⟨hd1, hle1, hf1⟩ := Vlq.decodeUInt32_form _ _ _ h1
      rcases ite_eq_cases h with ⟨hzero, h⟩ | ⟨hitem, h⟩
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [hzero] at hf1
        exact ⟨hd1, hle1, ByteArray.empty, _, by simp, rfl, hf1⟩
      · split at h
        · contradiction
        · rename_i _ r2 h2
          obtain ⟨hd2, hle2, hf2⟩ := decodeValue_canonical _ _ _ h2
          split at h
          · contradiction
          · rename_i _ r3 h3
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hd3, hle3, body, terminator, hsplit, hbody, hterm⟩ := ih _ _ _ h3
            rw [hd1] at hf2
            rw [hd2, hd1] at hsplit
            refine ⟨by rw [hd3, hd2, hd1], by omega,
              cursor.data.extract cursor.offset r2.snd.offset ++ body, terminator, ?_,
              ⟨_, body, rfl, ⟨_, _, (ByteArray.extract_append_extract_of_le _ hle1 hle2).symm,
                hf1, hitem, hf2⟩, hbody⟩, hterm⟩
            rw [ByteArray.append_assoc, ← hsplit,
              ByteArray.extract_append_extract_of_le _ (by omega) hle3]

theorem decodeErrorList_canonical (fuel : Nat) (cursor next : Cursor)
    (errors : List (UInt32 × UInt64)) (h : decodeErrorList fuel cursor = .ok (errors, next)) :
    next.data = cursor.data ∧ cursor.offset ≤ next.offset ∧
      TerminatedForm ErrorEntryForm errors (cursor.data.extract cursor.offset next.offset) := by
  induction fuel generalizing cursor next errors with
  | zero => simp [decodeErrorList] at h
  | succ fuel ih =>
    simp only [decodeErrorList, bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i _ r1 h1
      obtain ⟨hd1, hle1, hf1⟩ := Vlq.decodeUInt32_form _ _ _ h1
      rcases ite_eq_cases h with ⟨hzero, h⟩ | ⟨hitem, h⟩
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [hzero] at hf1
        exact ⟨hd1, hle1, ByteArray.empty, _, by simp, rfl, hf1⟩
      · split at h
        · contradiction
        · rename_i _ r2 h2
          obtain ⟨hd2, hle2, hf2⟩ := Vlq.decodeUInt64_form _ _ _ h2
          split at h
          · contradiction
          · rename_i _ r3 h3
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hd3, hle3, body, terminator, hsplit, hbody, hterm⟩ := ih _ _ _ h3
            rw [hd1] at hf2
            rw [hd2, hd1] at hsplit
            refine ⟨by rw [hd3, hd2, hd1], by omega,
              cursor.data.extract cursor.offset r2.snd.offset ++ body, terminator, ?_,
              ⟨_, body, rfl, ⟨_, _, (ByteArray.extract_append_extract_of_le _ hle1 hle2).symm,
                hf1, hitem, hf2⟩, hbody⟩, hterm⟩
            rw [ByteArray.append_assoc, ← hsplit,
              ByteArray.extract_append_extract_of_le _ (by omega) hle3]

/-- The bytes `decodeReadReply` accepts: a return value, a value list and an error
    list, each in an accepted form. -/
def ReadReply.Form (reply : ReadReply) (input : ByteArray) : Prop :=
  ∃ returnBytes valueBytes errorBytes, input = returnBytes ++ valueBytes ++ errorBytes ∧
    Vlq.UInt64Form reply.returnValue returnBytes ∧
    TerminatedForm ValueEntryForm reply.values valueBytes ∧
    TerminatedForm ErrorEntryForm reply.errors errorBytes

theorem decodeReadReply_canonical (cursor next : Cursor) (reply : ReadReply)
    (h : decodeReadReply cursor = .ok (reply, next)) :
    next.data = cursor.data ∧ cursor.offset ≤ next.offset ∧
      reply.Form (cursor.data.extract cursor.offset next.offset) := by
  simp only [decodeReadReply, bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i _ r1 h1
    obtain ⟨hd1, hle1, hf1⟩ := Vlq.decodeUInt64_form _ _ _ h1
    split at h
    · contradiction
    · rename_i _ r2 h2
      obtain ⟨hd2, hle2, hf2⟩ := decodeValueList_canonical _ _ _ _ h2
      split at h
      · contradiction
      · rename_i _ r3 h3
        obtain ⟨hd3, hle3, hf3⟩ := decodeErrorList_canonical _ _ _ _ h3
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [hd1] at hf2
        rw [hd2, hd1] at hf3
        refine ⟨by rw [hd3, hd2, hd1], by omega, _, _, _, ?_, hf1, hf2, hf3⟩
        rw [ByteArray.extract_append_extract_of_le _ hle1 hle2,
          ByteArray.extract_append_extract_of_le _ (by omega) hle3]

end LeanS7CommPlus
