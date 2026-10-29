import LeanS7.Binary
import LeanS7CommPlus.Protocol

/-!
# Message headers and the integrity envelope

The data of a frame is a message, possibly inside an integrity envelope.

- **Request header** (14 bytes): opcode `0x31`, a reserved word, the function code,
  a reserved word, the sequence number, the session id (big-endian) and the
  transport flags.
- **Response header** (10 bytes): opcode `0x32` (or `0x02`, seen on some older
  firmware), a reserved word, the function code, a reserved word, the sequence
  number and the transport flags. There is no session id. The Python helper
  `codec.decode_response_header` reads a 14-byte layout with a session id; the
  client itself does not use it and slices responses at 10 bytes, as every
  response in the CPU 1214C capture requires.
- **Integrity envelope** (V3 frames after a SessionKey setup): a length byte `0x20`,
  the 32-byte HMAC-SHA256 digest, then the message. The digest is kept as bytes;
  computing and checking it is out of scope (decision 3).

The decoders ignore the reserved words, as the Python client does; the encoders
write zero.
-/

namespace LeanS7CommPlus

open LeanS7

structure RequestHeader where
  function : UInt16
  sequence : UInt16
  session : UInt32
  transportFlags : UInt8
  deriving BEq, Repr

structure ResponseHeader where
  opcode : UInt8
  function : UInt16
  sequence : UInt16
  transportFlags : UInt8
  deriving BEq, Repr

/-- A request header with the given reserved words. -/
def encodeRequestHeaderWith (reserved1 reserved2 : UInt16) (header : RequestHeader) : ByteArray :=
  bytes #[requestOpcode] ++ uint16BE reserved1 ++ uint16BE header.function ++
    uint16BE reserved2 ++ uint16BE header.sequence ++ uint32BE header.session ++
    bytes #[header.transportFlags]

def encodeRequestHeader (header : RequestHeader) : ByteArray :=
  encodeRequestHeaderWith 0 0 header

def decodeRequestHeader (cursor : Cursor) : Except DecodeError (RequestHeader × Cursor) := do
  let (opcode, cursor) ← cursor.readUInt8
  if opcode != requestOpcode then
    throw (.invalidField (cursor.offset - 1) s!"expected request opcode 0x31, got {opcode}")
  let (_, cursor) ← cursor.readUInt16BE
  let (function, cursor) ← cursor.readUInt16BE
  let (_, cursor) ← cursor.readUInt16BE
  let (sequence, cursor) ← cursor.readUInt16BE
  let (session, cursor) ← cursor.readUInt32BE
  let (transportFlags, cursor) ← cursor.readUInt8
  pure ({ function, sequence, session, transportFlags }, cursor)

/-- The response opcodes: `0x32`, and `0x02` from some older firmware. -/
def isResponseOpcode (opcode : UInt8) : Bool :=
  opcode == responseOpcode || opcode == 0x02

def encodeResponseHeaderWith (reserved1 reserved2 : UInt16) (header : ResponseHeader) :
    ByteArray :=
  bytes #[header.opcode] ++ uint16BE reserved1 ++ uint16BE header.function ++
    uint16BE reserved2 ++ uint16BE header.sequence ++ bytes #[header.transportFlags]

def encodeResponseHeader (header : ResponseHeader) : ByteArray :=
  encodeResponseHeaderWith 0 0 header

def decodeResponseHeader (cursor : Cursor) : Except DecodeError (ResponseHeader × Cursor) := do
  let (opcode, cursor) ← cursor.readUInt8
  if !isResponseOpcode opcode then
    throw (.invalidField (cursor.offset - 1) s!"expected response opcode 0x32, got {opcode}")
  let (_, cursor) ← cursor.readUInt16BE
  let (function, cursor) ← cursor.readUInt16BE
  let (_, cursor) ← cursor.readUInt16BE
  let (sequence, cursor) ← cursor.readUInt16BE
  let (transportFlags, cursor) ← cursor.readUInt8
  pure ({ opcode, function, sequence, transportFlags }, cursor)

/-- The integrity envelope around a message: `0x20`, the 32-byte digest, the message. -/
def encodeIntegrityEnvelope (digest message : ByteArray) : ByteArray :=
  bytes #[0x20] ++ digest ++ message

/-- Split frame data into the digest and the message. -/
def decodeIntegrityEnvelope (data : ByteArray) : Except DecodeError (ByteArray × ByteArray) := do
  let cursor : Cursor := { data }
  let (length, cursor) ← cursor.readUInt8
  if length != 0x20 then
    throw (.invalidField 0 s!"expected a 32-byte integrity digest, got length {length}")
  let (digest, cursor) ← cursor.readBytes 32
  let (message, cursor) ← cursor.readBytes cursor.remaining
  cursor.finish
  pure (digest, message)

/-! ## Reading a big-endian word pair back -/

theorem uint32BE_halves (high low : UInt16) :
    uint32BE (UInt32.ofNat (high.toNat * 65536 + low.toNat)) = uint16BE high ++ uint16BE low := by
  have hh := high.toNat_lt
  have hl := low.toNat_lt
  have hn : (UInt32.ofNat (high.toNat * 65536 + low.toNat)).toNat = high.toNat * 65536 + low.toNat := by
    rw [UInt32.toNat_ofNat']; omega
  have key : ∀ a b c d e f g h : UInt8, a = e → b = f → c = g → d = h →
      ByteArray.mk #[a, b, c, d] = ByteArray.mk #[e, f] ++ ByteArray.mk #[g, h] := by
    intros; subst_vars; rfl
  unfold uint32BE uint16BE
  apply key <;> (apply UInt8.toNat_inj.mp; simp only [UInt8.toNat_ofNat', hn]; omega)

theorem readUInt32BE_value (cursor next : Cursor) (value : UInt32)
    (h : cursor.readUInt32BE = .ok (value, next)) :
    cursor.offset + 4 ≤ cursor.data.size ∧
      uint32BE value = cursor.data.extract cursor.offset (cursor.offset + 4) ∧
      next = { cursor with offset := cursor.offset + 4 } := by
  simp only [Cursor.readUInt32BE, bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · rename_i first rest e1
    split at h
    · contradiction
    · rename_i second rest' e2
      injection h with h
      injection h with hv hn
      obtain ⟨l1, d1, n1⟩ := Cursor.readUInt16BE_value _ _ _ e1
      rw [n1] at e2
      obtain ⟨l2, d2, n2⟩ := Cursor.readUInt16BE_value _ _ _ e2
      simp only at l2 d2 n2
      refine ⟨by omega, ?_, by rw [← hn, n2]⟩
      rw [← hv, uint32BE_halves, d1, d2, ← ByteArray.extract_two_uint16BE _ _ (by omega),
        ← ByteArray.extract_two_uint16BE _ _ (by omega),
        ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]

/-! ## Canonical forms -/

/-- Canonical form of a request header: the fourteen bytes the decoder reads are the
    encoding of the decoded header with the two reserved words it skipped. -/
theorem decodeRequestHeader_canonical (cursor next : Cursor) (header : RequestHeader)
    (h : decodeRequestHeader cursor = .ok (header, next)) :
    next.data = cursor.data ∧ next.offset = cursor.offset + 14 ∧
      ∃ reserved1 reserved2, cursor.data.extract cursor.offset next.offset =
        encodeRequestHeaderWith reserved1 reserved2 header := by
  simp only [decodeRequestHeader, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i x0 v0 e0 hop x1 v1 e1 x2 v2 e2 x3 v3 e3 x4 v4 e4 x5 v5 e5 x6 v6 e6
  obtain ⟨l0, d0, n0⟩ := Cursor.readUInt8_value _ _ _ e0
  rw [n0] at e1
  obtain ⟨l1, d1, n1⟩ := Cursor.readUInt16BE_value _ _ _ e1
  rw [n1] at e2
  obtain ⟨l2, d2, n2⟩ := Cursor.readUInt16BE_value _ _ _ e2
  rw [n2] at e3
  obtain ⟨l3, d3, n3⟩ := Cursor.readUInt16BE_value _ _ _ e3
  rw [n3] at e4
  obtain ⟨l4, d4, n4⟩ := Cursor.readUInt16BE_value _ _ _ e4
  rw [n4] at e5
  obtain ⟨l5, d5, n5⟩ := readUInt32BE_value _ _ _ e5
  rw [n5] at e6
  obtain ⟨l6, d6, n6⟩ := Cursor.readUInt8_value _ _ _ e6
  injection h with h
  injection h with hh hn
  subst hh hn
  rw [n6]
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hop
  simp only at l0 l1 l2 l3 l4 l5 l6 d0 d1 d2 d3 d4 d5 d6
  refine ⟨rfl, by (simp only; try omega), v1.fst, v3.fst, ?_⟩
  simp only [encodeRequestHeaderWith]
  rw [d1, d2, d3, d4, d5, ← hop, ← d0, ← d6,
    ← ByteArray.extract_two_uint16BE _ _ (by omega), ← ByteArray.extract_two_uint16BE _ _ (by omega),
    ← ByteArray.extract_two_uint16BE _ _ (by omega), ← ByteArray.extract_two_uint16BE _ _ (by omega),
    show bytes #[cursor.data[cursor.offset]] = cursor.data.extract cursor.offset (cursor.offset + 1)
      from (ByteArray.extract_one _ _ l0).symm,
    show bytes #[cursor.data[cursor.offset + 1 + 2 + 2 + 2 + 2 + 4]] =
      cursor.data.extract (cursor.offset + 1 + 2 + 2 + 2 + 2 + 4) (cursor.offset + 1 + 2 + 2 + 2 + 2 + 4 + 1)
      from (ByteArray.extract_one _ _ l6).symm]
  rw [ByteArray.extract_append_extract_of_le _ (by omega) (by omega), ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega), ByteArray.extract_append_extract_of_le _ (by omega) (by omega), ByteArray.extract_append_extract_of_le _ (by omega) (by omega), ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]

/-- Canonical form of a response header, as for the request header. -/
theorem decodeResponseHeader_canonical (cursor next : Cursor) (header : ResponseHeader)
    (h : decodeResponseHeader cursor = .ok (header, next)) :
    next.data = cursor.data ∧ next.offset = cursor.offset + 10 ∧ isResponseOpcode header.opcode ∧
      ∃ reserved1 reserved2, cursor.data.extract cursor.offset next.offset =
        encodeResponseHeaderWith reserved1 reserved2 header := by
  simp only [decodeResponseHeader, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i x0 v0 e0 hop x1 v1 e1 x2 v2 e2 x3 v3 e3 x4 v4 e4 x5 v5 e5
  obtain ⟨l0, d0, n0⟩ := Cursor.readUInt8_value _ _ _ e0
  rw [n0] at e1
  obtain ⟨l1, d1, n1⟩ := Cursor.readUInt16BE_value _ _ _ e1
  rw [n1] at e2
  obtain ⟨l2, d2, n2⟩ := Cursor.readUInt16BE_value _ _ _ e2
  rw [n2] at e3
  obtain ⟨l3, d3, n3⟩ := Cursor.readUInt16BE_value _ _ _ e3
  rw [n3] at e4
  obtain ⟨l4, d4, n4⟩ := Cursor.readUInt16BE_value _ _ _ e4
  rw [n4] at e5
  obtain ⟨l5, d5, n5⟩ := Cursor.readUInt8_value _ _ _ e5
  injection h with h
  injection h with hh hn
  subst hh hn
  rw [n5]
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hop
  simp only at l0 l1 l2 l3 l4 l5 d0 d1 d2 d3 d4 d5
  refine ⟨rfl, by (simp only; try omega), by simpa using hop, v1.fst, v3.fst, ?_⟩
  simp only [encodeResponseHeaderWith]
  rw [d1, d2, d3, d4, ← d0, ← d5,
    ← ByteArray.extract_two_uint16BE _ _ (by omega), ← ByteArray.extract_two_uint16BE _ _ (by omega),
    ← ByteArray.extract_two_uint16BE _ _ (by omega), ← ByteArray.extract_two_uint16BE _ _ (by omega),
    show bytes #[cursor.data[cursor.offset]] = cursor.data.extract cursor.offset (cursor.offset + 1)
      from (ByteArray.extract_one _ _ l0).symm,
    show bytes #[cursor.data[cursor.offset + 1 + 2 + 2 + 2 + 2]] =
      cursor.data.extract (cursor.offset + 1 + 2 + 2 + 2 + 2) (cursor.offset + 1 + 2 + 2 + 2 + 2 + 1)
      from (ByteArray.extract_one _ _ l5).symm]
  rw [ByteArray.extract_append_extract_of_le _ (by omega) (by omega), ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega), ByteArray.extract_append_extract_of_le _ (by omega) (by omega), ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]

/-- Canonical form of the integrity envelope: every accepted envelope is exactly the
    encoding of its digest and message, and the digest has 32 bytes. -/
theorem decodeIntegrityEnvelope_canonical (data digest message : ByteArray)
    (h : decodeIntegrityEnvelope data = .ok (digest, message)) :
    digest.size = 32 ∧ encodeIntegrityEnvelope digest message = data := by
  simp only [decodeIntegrityEnvelope, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i x0 v0 e0 hlen x1 v1 e1 x2 v2 e2 x3 v3 e3
  obtain ⟨l0, d0, n0⟩ := Cursor.readUInt8_value _ _ _ e0
  rw [n0] at e1
  have s1 := Cursor.readBytes_size _ _ _ _ e1
  obtain ⟨p1, n1⟩ := Cursor.readBytes_value _ _ _ _ e1
  rw [n1] at e2
  obtain ⟨p2, n2⟩ := Cursor.readBytes_value _ _ _ _ e2
  rw [n2] at e3
  have hfin := Cursor.finish_ok _ e3
  injection h with h
  injection h with hd hm
  subst hd hm
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
  simp only [Cursor.remaining] at p2 hfin
  simp only at l0 d0 p1 p2 hfin s1
  have hext := s1
  rw [p1, ByteArray.size_extract] at hext
  refine ⟨s1, ?_⟩
  simp only [encodeIntegrityEnvelope]
  rw [← hlen, ← d0, show bytes #[data[0]] = data.extract 0 1 from
    (ByteArray.extract_one _ _ l0).symm, p1, p2,
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]
  rw [show 0 + 1 + 32 + (data.size - (0 + 1 + 32)) = data.size by omega, ByteArray.extract_zero_size]

/-! ## Round trips -/

private theorem cursor_offset_eq {data : ByteArray} {offset offset' : Nat} (h : offset = offset') :
    ({ data, offset } : Cursor) = { data, offset := offset' } := by
  rw [h]

theorem decodeRequestHeader_encode (header : RequestHeader) (pre suffix : ByteArray) :
    decodeRequestHeader { data := pre ++ (encodeRequestHeader header ++ suffix), offset := pre.size } =
      .ok (header,
        { data := pre ++ (encodeRequestHeader header ++ suffix), offset := pre.size + 14 }) := by
  have hshape : encodeRequestHeader header ++ suffix =
      bytes #[requestOpcode] ++ (uint16BE 0 ++ (uint16BE header.function ++ (uint16BE 0 ++
        (uint16BE header.sequence ++ (uint32BE header.session ++
          (bytes #[header.transportFlags] ++ suffix)))))) := by
    simp only [encodeRequestHeader, encodeRequestHeaderWith, ByteArray.append_assoc]
  rw [hshape]
  have r1 := Cursor.readUInt16BE_append_uint16BE (pre ++ bytes #[requestOpcode])
    (uint16BE header.function ++ (uint16BE 0 ++ (uint16BE header.sequence ++
      (uint32BE header.session ++ (bytes #[header.transportFlags] ++ suffix))))) 0
  have r2 := Cursor.readUInt16BE_append_uint16BE (pre ++ bytes #[requestOpcode] ++ uint16BE 0)
    (uint16BE 0 ++ (uint16BE header.sequence ++
      (uint32BE header.session ++ (bytes #[header.transportFlags] ++ suffix)))) header.function
  have r3 := Cursor.readUInt16BE_append_uint16BE
    (pre ++ bytes #[requestOpcode] ++ uint16BE 0 ++ uint16BE header.function)
    (uint16BE header.sequence ++ (uint32BE header.session ++ (bytes #[header.transportFlags] ++ suffix))) 0
  have r4 := Cursor.readUInt16BE_append_uint16BE
    (pre ++ bytes #[requestOpcode] ++ uint16BE 0 ++ uint16BE header.function ++ uint16BE 0)
    (uint32BE header.session ++ (bytes #[header.transportFlags] ++ suffix)) header.sequence
  have r5 := Cursor.readUInt32BE_append_uint32BE
    (pre ++ bytes #[requestOpcode] ++ uint16BE 0 ++ uint16BE header.function ++ uint16BE 0 ++
      uint16BE header.sequence) (bytes #[header.transportFlags] ++ suffix) header.session
  have r6 := Cursor.readUInt8_append_byte
    (pre ++ bytes #[requestOpcode] ++ uint16BE 0 ++ uint16BE header.function ++ uint16BE 0 ++
      uint16BE header.sequence ++ uint32BE header.session) suffix header.transportFlags
  simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, List.size_toArray,
    List.length_cons, List.length_nil, uint16BE_size, uint32BE_size] at r1 r2 r3 r4 r5 r6
  unfold decodeRequestHeader
  rw [Cursor.readUInt8_append_byte]
  simp only [bind, Except.bind, bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [cursor_offset_eq (show pre.size + 1 = pre.size + (0 + 1) by omega), r1]
  simp only
  rw [cursor_offset_eq (show pre.size + (0 + 1) + 2 = pre.size + (0 + 1 + 2) by omega), r2]
  simp only
  rw [cursor_offset_eq (show pre.size + (0 + 1 + 2) + 2 = pre.size + (0 + 1 + (2 + 2)) by omega), r3]
  simp only
  rw [cursor_offset_eq (show pre.size + (0 + 1 + (2 + 2)) + 2 = pre.size + (0 + 1 + (2 + (2 + 2))) by omega), r4]
  simp only
  rw [cursor_offset_eq (show pre.size + (0 + 1 + (2 + (2 + 2))) + 2 =
    pre.size + (0 + 1 + (2 + (2 + (2 + 2)))) by omega), r5]
  simp only
  rw [cursor_offset_eq (show pre.size + (0 + 1 + (2 + (2 + (2 + 2)))) + 4 =
    pre.size + (0 + 1 + (2 + (2 + (2 + (2 + 4))))) by omega), r6]
  simp only [pure, Except.pure]

theorem decodeResponseHeader_encode (header : ResponseHeader) (hopcode : isResponseOpcode header.opcode)
    (pre suffix : ByteArray) :
    decodeResponseHeader { data := pre ++ (encodeResponseHeader header ++ suffix), offset := pre.size } =
      .ok (header,
        { data := pre ++ (encodeResponseHeader header ++ suffix), offset := pre.size + 10 }) := by
  have hshape : encodeResponseHeader header ++ suffix =
      bytes #[header.opcode] ++ (uint16BE 0 ++ (uint16BE header.function ++ (uint16BE 0 ++
        (uint16BE header.sequence ++ (bytes #[header.transportFlags] ++ suffix))))) := by
    simp only [encodeResponseHeader, encodeResponseHeaderWith, ByteArray.append_assoc]
  rw [hshape]
  have r1 := Cursor.readUInt16BE_append_uint16BE (pre ++ bytes #[header.opcode])
    (uint16BE header.function ++ (uint16BE 0 ++ (uint16BE header.sequence ++
      (bytes #[header.transportFlags] ++ suffix)))) 0
  have r2 := Cursor.readUInt16BE_append_uint16BE (pre ++ bytes #[header.opcode] ++ uint16BE 0)
    (uint16BE 0 ++ (uint16BE header.sequence ++ (bytes #[header.transportFlags] ++ suffix)))
    header.function
  have r3 := Cursor.readUInt16BE_append_uint16BE
    (pre ++ bytes #[header.opcode] ++ uint16BE 0 ++ uint16BE header.function)
    (uint16BE header.sequence ++ (bytes #[header.transportFlags] ++ suffix)) 0
  have r4 := Cursor.readUInt16BE_append_uint16BE
    (pre ++ bytes #[header.opcode] ++ uint16BE 0 ++ uint16BE header.function ++ uint16BE 0)
    (bytes #[header.transportFlags] ++ suffix) header.sequence
  have r5 := Cursor.readUInt8_append_byte
    (pre ++ bytes #[header.opcode] ++ uint16BE 0 ++ uint16BE header.function ++ uint16BE 0 ++
      uint16BE header.sequence) suffix header.transportFlags
  simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, List.size_toArray,
    List.length_cons, List.length_nil, uint16BE_size] at r1 r2 r3 r4 r5
  unfold decodeResponseHeader
  rw [Cursor.readUInt8_append_byte]
  simp only [bind, Except.bind, hopcode, Bool.not_true, Bool.false_eq_true, if_false]
  rw [cursor_offset_eq (show pre.size + 1 = pre.size + (0 + 1) by omega), r1]
  simp only
  rw [cursor_offset_eq (show pre.size + (0 + 1) + 2 = pre.size + (0 + 1 + 2) by omega), r2]
  simp only
  rw [cursor_offset_eq (show pre.size + (0 + 1 + 2) + 2 = pre.size + (0 + 1 + (2 + 2)) by omega), r3]
  simp only
  rw [cursor_offset_eq (show pre.size + (0 + 1 + (2 + 2)) + 2 = pre.size + (0 + 1 + (2 + (2 + 2))) by omega), r4]
  simp only
  rw [cursor_offset_eq (show pre.size + (0 + 1 + (2 + (2 + 2))) + 2 =
    pre.size + (0 + 1 + (2 + (2 + (2 + 2)))) by omega), r5]
  simp only [pure, Except.pure]

theorem decodeIntegrityEnvelope_encode (digest message : ByteArray) (hdigest : digest.size = 32) :
    decodeIntegrityEnvelope (encodeIntegrityEnvelope digest message) = .ok (digest, message) := by
  have r0 := Cursor.readUInt8_append_byte ByteArray.empty (digest ++ message) 0x20
  have r1 := Cursor.readBytes_append (bytes #[0x20]) digest message
  have r2 := Cursor.readBytes_append (bytes #[0x20] ++ digest) message ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.append_assoc,
    ByteArray.size_append, bytes_size, List.size_toArray, List.length_cons, List.length_nil,
    ByteArray.size_empty, hdigest] at r0 r1 r2
  simp only [encodeIntegrityEnvelope, ByteArray.append_assoc]
  simp only [decodeIntegrityEnvelope, bind, Except.bind]
  rw [show ({ data := bytes #[0x20] ++ (digest ++ message) } : Cursor) =
    { data := bytes #[0x20] ++ (digest ++ message), offset := 0 } from rfl, r0]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false, Nat.zero_add]
  rw [r1]
  simp only [Cursor.remaining, ByteArray.size_append, bytes_size, List.size_toArray,
    List.length_cons, List.length_nil, hdigest]
  rw [show 1 + (32 + message.size) - (1 + 32) = message.size by omega, r2]
  simp [Cursor.finish, pure, Except.pure, ByteArray.size_append, hdigest]
  rw [if_pos (by omega)]

end LeanS7CommPlus
