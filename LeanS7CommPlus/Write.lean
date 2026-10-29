import LeanS7.Binary
import LeanS7CommPlus.Access

/-!
# SetMultiVariables, and per-item read results

Layouts from the Python reference (`client._build_write_payload`,
`client._parse_write_response_errors`) and the CPU 1214C capture.

- **SetMultiVariables request payload**: a zero word, the VLQ item count, the VLQ
  field count, the addresses, then the values numbered from 1 (`[VLQ number]
  [value]`, ending with `0x00`), the object qualifier and four fill bytes. With
  integrity tracking the request IntegrityId goes just before the fill.
- **SetMultiVariables reply**: VLQ return value and the item errors as `[VLQ item
  number][VLQ error]`, ending with 0.

A GetMultiVariables reply lists values and item errors separately. `ReadReply.results`
gives one result per requested item: its value, or its error. A PLC answers an item
for a missing DB with a NULL value *and* an error (gijzelaerr/s7commplus#130), so a
NULL value next to an error counts as that error. Any other reply that names an item
twice, names an item outside the request, leaves an item unanswered or carries both
a value and an error for an item is refused. The overall return value is not
consulted: an S7-1500 sets it when some items fail and still sends the good values
(gijzelaerr/s7commplus#129).
-/

namespace LeanS7CommPlus

open LeanS7

/-! ## SetMultiVariables -/

structure WriteRequest where
  addresses : List ItemAddress
  values : List Value
  form : QualifierForm
  keyQualifier : UInt32
  deriving BEq

def WriteRequest.fieldCount (request : WriteRequest) : Nat :=
  (request.addresses.map ItemAddress.fieldCount).sum

/-- Values numbered from `first`, ending with `0x00`. -/
def encodeNumberedValues (first : Nat) : List Value → ByteArray
  | [] => bytes #[0x00]
  | value :: rest =>
    Vlq.encodeUInt32 (UInt32.ofNat first) ++ value.encode ++ encodeNumberedValues (first + 1) rest

def WriteRequest.encodeBody (request : WriteRequest) : ByteArray :=
  uint32BE 0 ++ Vlq.encodeUInt32 (UInt32.ofNat request.addresses.length) ++
    Vlq.encodeUInt32 (UInt32.ofNat request.fieldCount) ++ encodeAddresses request.addresses ++
    encodeNumberedValues 1 request.values ++ encodeObjectQualifier request.form request.keyQualifier

def WriteRequest.encode (request : WriteRequest) (integrityId : Option UInt32) : ByteArray :=
  request.encodeBody ++
    (match integrityId with
     | some id => Vlq.encodeUInt32 id
     | none => ByteArray.empty) ++ uint32BE 0

/-- Read `count` values numbered from `first`, then the `0x00` terminator. -/
def decodeNumberedValues : Nat → Nat → Cursor → Except DecodeError (List Value × Cursor)
  | _, 0, cursor => do
    let (terminator, cursor) ← cursor.readUInt8
    if terminator != 0x00 then
      throw (.invalidField (cursor.offset - 1) "write values do not end after the last item")
    pure ([], cursor)
  | first, count + 1, cursor => do
    let (number, cursor) ← Vlq.decodeUInt32 cursor
    if number.toNat != first then
      throw (.invalidField cursor.offset s!"expected write value {first}, got {number}")
    let (value, cursor) ← decodeValue cursor
    let (rest, cursor) ← decodeNumberedValues (first + 1) count cursor
    pure (value :: rest, cursor)

def decodeWriteRequestBody (form : QualifierForm) (cursor : Cursor) :
    Except DecodeError (WriteRequest × Cursor) := do
  let (zero, cursor) ← cursor.readUInt32BE
  if zero != 0 then
    throw (.invalidField cursor.offset "SetMultiVariables request does not start with a zero word")
  let (count, cursor) ← Vlq.decodeUInt32 cursor
  let (fields, cursor) ← Vlq.decodeUInt32 cursor
  let (addresses, cursor) ← decodeAddresses count.toNat cursor
  if fields.toNat != (addresses.map ItemAddress.fieldCount).sum then
    throw (.invalidField cursor.offset "field count does not match the addresses")
  let (values, cursor) ← decodeNumberedValues 1 count.toNat cursor
  let (keyQualifier, cursor) ← decodeObjectQualifier form cursor
  pure ({ addresses, values, form, keyQualifier }, cursor)

def decodeWriteRequest (form : QualifierForm) (withIntegrity : Bool) (payload : ByteArray) :
    Except DecodeError (WriteRequest × Option UInt32) := do
  let (request, cursor) ← decodeWriteRequestBody form { data := payload }
  let (integrityId, cursor) ← if withIntegrity then do
      let (id, cursor) ← Vlq.decodeUInt32 cursor
      pure (some id, cursor)
    else pure (none, cursor)
  let (fill, cursor) ← cursor.readUInt32BE
  if fill != 0 then
    throw (.invalidField cursor.offset "request fill bytes are not zero")
  cursor.finish
  pure (request, integrityId)

structure WriteReply where
  returnValue : UInt64
  errors : List (UInt32 × UInt64)
  deriving BEq

def WriteReply.encode (reply : WriteReply) : ByteArray :=
  Vlq.encodeUInt64 reply.returnValue ++ encodeErrorList reply.errors

/-- Decode a SetMultiVariables reply up to the end of its error list. -/
def decodeWriteReply (cursor : Cursor) : Except DecodeError (WriteReply × Cursor) := do
  let (returnValue, cursor) ← Vlq.decodeUInt64 cursor
  let (errors, cursor) ← decodeErrorList cursor.remaining cursor
  pure ({ returnValue, errors }, cursor)

/-! ## Per-item read results -/

/-- The result of one requested item: its value, or its PLC error. -/
abbrev ItemResult := Except UInt64 Value

/-- The result of item `item` (numbered from 1), or `none` when the reply leaves it
    unanswered or carries both a non-NULL value and an error for it. -/
def ReadReply.result (reply : ReadReply) (item : UInt32) : Option ItemResult :=
  match reply.errors.find? (·.1 == item), reply.values.find? (·.1 == item) with
  | some (_, error), none => some (.error error)
  | some (_, error), some (_, .scalar .null) => some (.error error)
  | some _, some _ => none
  | none, some (_, value) => some (.ok value)
  | none, none => none

/-- Item numbers are distinct within each list and all within `1..count`. -/
def ReadReply.WellNumbered (reply : ReadReply) (count : Nat) : Prop :=
  (reply.values.map (·.1)).Nodup ∧ (reply.errors.map (·.1)).Nodup ∧
    (∀ entry ∈ reply.values, 1 ≤ entry.1.toNat ∧ entry.1.toNat ≤ count) ∧
    (∀ entry ∈ reply.errors, 1 ≤ entry.1.toNat ∧ entry.1.toNat ≤ count)

instance (reply : ReadReply) (count : Nat) : Decidable (reply.WellNumbered count) := by
  unfold ReadReply.WellNumbered; infer_instance

/-- The results of the items numbered `index + 1` for each `index` in the list. -/
def ReadReply.collect (reply : ReadReply) : List Nat → Except DecodeError (List ItemResult)
  | [] => .ok []
  | index :: rest =>
    match reply.result (UInt32.ofNat (index + 1)) with
    | some result => (reply.collect rest).map (result :: ·)
    | none => .error (.invalidField 0 s!"read item {index + 1} is unanswered or answered twice")

/-- One result per requested item, in request order, or an error when the reply does
    not account for every item exactly once. -/
def ReadReply.results (reply : ReadReply) (count : Nat) : Except DecodeError (List ItemResult) :=
  if reply.WellNumbered count then reply.collect (List.range count)
  else .error (.invalidField 0 "read reply names an item twice or outside the request")

/-- A value result comes from the value list, with no error for the same item. -/
theorem ReadReply.result_ok (reply : ReadReply) (item : UInt32) (value : Value)
    (h : reply.result item = some (.ok value)) :
    (item, value) ∈ reply.values ∧ ∀ entry ∈ reply.errors, entry.1 ≠ item := by
  unfold ReadReply.result at h
  split at h <;> simp_all
  rename_i hnone hsome
  refine ⟨?_, ?_⟩
  · have := List.mem_of_find?_eq_some hsome
    have heq := List.find?_some hsome
    simp at heq
    rw [heq] at this
    exact this
  · intro first second hentry
    exact hnone first second hentry

/-- An error result comes from the error list. -/
theorem ReadReply.result_error (reply : ReadReply) (item : UInt32) (error : UInt64)
    (h : reply.result item = some (.error error)) : (item, error) ∈ reply.errors := by
  unfold ReadReply.result at h
  split at h <;> simp_all
  all_goals
    rename_i herror _
    have := List.mem_of_find?_eq_some herror
    have heq := List.find?_some herror
    simp at heq
    rw [heq] at this
    exact this

theorem ReadReply.collect_spec (reply : ReadReply) (indices : List Nat) (results : List ItemResult)
    (h : reply.collect indices = .ok results) :
    results.length = indices.length ∧
      ∀ i (hi : i < results.length) (hj : i < indices.length),
        reply.result (UInt32.ofNat (indices[i] + 1)) = some results[i] := by
  induction indices generalizing results with
  | nil =>
    simp [ReadReply.collect] at h
    subst h
    simp
  | cons index rest ih =>
    simp only [ReadReply.collect] at h
    split at h
    · rename_i result hresult
      cases hrest : reply.collect rest with
      | error e => simp [hrest, Except.map] at h
      | ok tail =>
        simp [hrest, Except.map] at h
        subst h
        obtain ⟨hlen, hall⟩ := ih tail hrest
        refine ⟨by simp [hlen], ?_⟩
        intro i hi hj
        cases i with
        | zero => simpa using hresult
        | succ i =>
          simp only [List.length_cons] at hi hj
          simpa using hall i (by omega) (by omega)
    · simp at h

/-- Per-item results are sound: there is one per requested item, a value result for
    item `i` is that item's value with no error for it, and an error result is that
    item's error. -/
theorem ReadReply.results_spec (reply : ReadReply) (count : Nat) (results : List ItemResult)
    (h : reply.results count = .ok results) :
    results.length = count ∧ ∀ i (hi : i < results.length),
      (∀ value, results[i] = .ok value →
        (UInt32.ofNat (i + 1), value) ∈ reply.values ∧
          ∀ entry ∈ reply.errors, entry.1 ≠ UInt32.ofNat (i + 1)) ∧
      (∀ error, results[i] = .error error → (UInt32.ofNat (i + 1), error) ∈ reply.errors) := by
  unfold ReadReply.results at h
  split at h
  · obtain ⟨hlen, hall⟩ := reply.collect_spec _ _ h
    simp only [List.length_range] at hlen
    refine ⟨hlen, fun i hi => ⟨fun value hv => ?_, fun error he => ?_⟩⟩
    · have hr := hall i hi (by simp; omega)
      simp only [List.getElem_range] at hr
      rw [hv] at hr
      exact reply.result_ok _ _ hr
    · have hr := hall i hi (by simp; omega)
      simp only [List.getElem_range] at hr
      rw [he] at hr
      exact reply.result_error _ _ hr
  · simp at h

/-! ## Round trips -/

theorem decodeNumberedValues_encode (values : List Value) (hfit : ∀ value ∈ values, value.Fits)
    (first : Nat) (hfirst : first + values.length ≤ 2 ^ 32) (pre suffix : ByteArray) :
    decodeNumberedValues first values.length
        { data := pre ++ (encodeNumberedValues first values ++ suffix), offset := pre.size } =
      .ok (values,
        { data := pre ++ (encodeNumberedValues first values ++ suffix),
          offset := pre.size + (encodeNumberedValues first values).size }) := by
  induction values generalizing first pre with
  | nil =>
    simp only [List.length_nil, encodeNumberedValues]
    rw [decodeNumberedValues, Cursor.readUInt8_append_byte]
    simp [bind, Except.bind, pure, Except.pure]
  | cons value rest ih =>
    have hnum : (UInt32.ofNat first).toNat = first := by
      rw [UInt32.toNat_ofNat']; simp at hfirst; omega
    have r1 := decodeValue_encode value (hfit value (by simp)) (pre ++ Vlq.encodeUInt32 (UInt32.ofNat first))
      (encodeNumberedValues (first + 1) rest ++ suffix)
    have r2 := ih (fun v hv => hfit v (by simp [hv])) (first + 1) (by simp at hfirst; omega)
      (pre ++ Vlq.encodeUInt32 (UInt32.ofNat first) ++ value.encode)
    simp only [ByteArray.size_append] at r1 r2
    simp only [ByteArray.append_assoc] at r1 r2
    simp only [List.length_cons, encodeNumberedValues, ByteArray.append_assoc]
    rw [decodeNumberedValues, Vlq.decodeUInt32_encodeUInt32]
    simp only [bind, Except.bind, hnum, bne_self_eq_false, Bool.false_eq_true, if_false]
    rw [r1]
    simp only
    rw [r2]
    simp only [pure, Except.pure, ByteArray.size_append, Nat.add_assoc]

def WriteRequest.Fits (request : WriteRequest) : Prop :=
  (∀ address ∈ request.addresses, address.Fits) ∧ (∀ value ∈ request.values, value.Fits) ∧
    request.values.length = request.addresses.length ∧ request.addresses.length < 2 ^ 32 ∧
    request.fieldCount < 2 ^ 32

theorem decodeWriteRequestBody_encode (request : WriteRequest) (hfit : request.Fits)
    (pre suffix : ByteArray) :
    decodeWriteRequestBody request.form
        { data := pre ++ (request.encodeBody ++ suffix), offset := pre.size } =
      .ok (request,
        { data := pre ++ (request.encodeBody ++ suffix),
          offset := pre.size + request.encodeBody.size }) := by
  obtain ⟨haddr, hvalues, hlen, hcount, hfields⟩ := hfit
  have hcountNat : (UInt32.ofNat request.addresses.length).toNat = request.addresses.length := by
    rw [UInt32.toNat_ofNat']; omega
  have hfieldsNat : (UInt32.ofNat request.fieldCount).toNat = request.fieldCount := by
    rw [UInt32.toNat_ofNat']; omega
  simp only [WriteRequest.fieldCount] at hfieldsNat
  have r1 := Vlq.decodeUInt32_encodeUInt32 (UInt32.ofNat request.addresses.length) (pre ++ uint32BE 0)
    (Vlq.encodeUInt32 (UInt32.ofNat request.fieldCount) ++ (encodeAddresses request.addresses ++
      (encodeNumberedValues 1 request.values ++
        (encodeObjectQualifier request.form request.keyQualifier ++ suffix))))
  have r2 := Vlq.decodeUInt32_encodeUInt32 (UInt32.ofNat request.fieldCount)
    (pre ++ uint32BE 0 ++ Vlq.encodeUInt32 (UInt32.ofNat request.addresses.length))
    (encodeAddresses request.addresses ++ (encodeNumberedValues 1 request.values ++
      (encodeObjectQualifier request.form request.keyQualifier ++ suffix)))
  have r3 := decodeAddresses_encode request.addresses haddr
    (pre ++ uint32BE 0 ++ Vlq.encodeUInt32 (UInt32.ofNat request.addresses.length) ++
      Vlq.encodeUInt32 (UInt32.ofNat request.fieldCount))
    (encodeNumberedValues 1 request.values ++
      (encodeObjectQualifier request.form request.keyQualifier ++ suffix))
  have r4 := decodeNumberedValues_encode request.values hvalues 1 (by omega)
    (pre ++ uint32BE 0 ++ Vlq.encodeUInt32 (UInt32.ofNat request.addresses.length) ++
      Vlq.encodeUInt32 (UInt32.ofNat request.fieldCount) ++ encodeAddresses request.addresses)
    (encodeObjectQualifier request.form request.keyQualifier ++ suffix)
  have r5 := decodeObjectQualifier_encode request.form request.keyQualifier
    (pre ++ uint32BE 0 ++ Vlq.encodeUInt32 (UInt32.ofNat request.addresses.length) ++
      Vlq.encodeUInt32 (UInt32.ofNat request.fieldCount) ++ encodeAddresses request.addresses ++
      encodeNumberedValues 1 request.values) suffix
  simp only [ByteArray.size_append, uint32BE_size] at r1 r2 r3 r4 r5
  simp only [ByteArray.append_assoc, WriteRequest.fieldCount] at r1 r2 r3 r4 r5
  simp only [WriteRequest.encodeBody, ByteArray.append_assoc, WriteRequest.fieldCount]
  unfold decodeWriteRequestBody
  rw [Cursor.readUInt32BE_append_uint32BE]
  simp only [bind, Except.bind, bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [r1]
  simp only
  rw [r2]
  simp only [hcountNat]
  rw [r3]
  simp only [hfieldsNat, bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [hlen] at r4
  rw [r4]
  simp only
  rw [r5]
  simp only [pure, Except.pure, ByteArray.size_append, uint32BE_size, Nat.add_assoc]

theorem decodeWriteReply_encode (reply : WriteReply) (hfit : ∀ entry ∈ reply.errors, entry.1 ≠ 0)
    (pre suffix : ByteArray) :
    decodeWriteReply { data := pre ++ (reply.encode ++ suffix), offset := pre.size } =
      .ok (reply,
        { data := pre ++ (reply.encode ++ suffix), offset := pre.size + reply.encode.size }) := by
  have he := encodeErrorList_size reply.errors
  have r1 := decodeErrorList_encode reply.errors hfit
    ((pre ++ (Vlq.encodeUInt64 reply.returnValue ++ (encodeErrorList reply.errors ++ suffix))).size -
      (pre.size + (Vlq.encodeUInt64 reply.returnValue).size))
    (by simp only [ByteArray.size_append]; omega)
    (pre ++ Vlq.encodeUInt64 reply.returnValue) suffix
  simp only [ByteArray.size_append] at r1
  simp only [ByteArray.append_assoc] at r1
  simp only [WriteReply.encode, ByteArray.append_assoc]
  unfold decodeWriteReply
  rw [Vlq.decodeUInt64_encodeUInt64]
  simp only [bind, Except.bind, Cursor.remaining, ByteArray.size_append]
  rw [r1]
  simp only [pure, Except.pure, Nat.add_assoc]

/-- Decoding a complete request payload built by `WriteRequest.encode` returns the
    request and its IntegrityId. -/
theorem decodeWriteRequest_encode (request : WriteRequest) (hfit : request.Fits)
    (integrityId : Option UInt32) :
    decodeWriteRequest request.form integrityId.isSome (request.encode integrityId) =
      .ok (request, integrityId) := by
  cases integrityId with
  | none =>
    have hbody := decodeWriteRequestBody_encode request hfit ByteArray.empty (uint32BE 0)
    have hfill := Cursor.readUInt32BE_append_uint32BE request.encodeBody ByteArray.empty 0
    simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at hbody
    simp only [ByteArray.append_empty] at hfill
    have hpayload : request.encode none = request.encodeBody ++ uint32BE 0 := by
      simp [WriteRequest.encode]
    rw [hpayload]
    unfold decodeWriteRequest
    rw [show ({ data := request.encodeBody ++ uint32BE 0 } : Cursor) =
      { data := request.encodeBody ++ uint32BE 0, offset := 0 } from rfl, hbody]
    simp only [bind, Except.bind, Option.isSome_none, Bool.false_eq_true, if_false, pure,
      Except.pure]
    rw [hfill]
    simp [Cursor.finish, ByteArray.size_append]
  | some id =>
    have hbody := decodeWriteRequestBody_encode request hfit ByteArray.empty
      (Vlq.encodeUInt32 id ++ uint32BE 0)
    have hid := Vlq.decodeUInt32_encodeUInt32 id request.encodeBody (uint32BE 0)
    have hfill := Cursor.readUInt32BE_append_uint32BE (request.encodeBody ++ Vlq.encodeUInt32 id)
      ByteArray.empty 0
    simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at hbody
    simp only [ByteArray.size_append] at hfill
    simp only [ByteArray.append_empty, ByteArray.append_assoc] at hfill
    have hpayload : request.encode (some id) =
        request.encodeBody ++ (Vlq.encodeUInt32 id ++ uint32BE 0) := by
      simp [WriteRequest.encode, ByteArray.append_assoc]
    rw [hpayload]
    unfold decodeWriteRequest
    rw [show ({ data := request.encodeBody ++ (Vlq.encodeUInt32 id ++ uint32BE 0) } : Cursor) =
      { data := request.encodeBody ++ (Vlq.encodeUInt32 id ++ uint32BE 0), offset := 0 } from rfl,
      hbody]
    simp only [bind, Except.bind, Option.isSome_some, if_true]
    rw [hid]
    simp only [pure, Except.pure]
    rw [hfill]
    simp only [Cursor.finish, ByteArray.size_append, uint32BE_size, bne_self_eq_false,
      Bool.false_eq_true, if_false, Nat.add_assoc, if_true]

end LeanS7CommPlus
