import LeanS7CommPlus.Frame

/-!
# Fragment reassembly

A controller splits a response that is larger than its PDU size over several
fragments. Each fragment is a frame header and its data, without a trailer; only the
last fragment is followed by the trailer `72 vv 00 00`:

```
72 vv len₁ data₁   72 vv len₂ data₂   …   72 vv lenₙ dataₙ   72 vv 00 00
```

The reassembled message is the data of the fragments in order. A complete frame is
the case `n = 1`. This follows `_recv_reassembled_payload` of the Python client:
after each fragment, four bytes equal to the trailer end the message, anything else
must be the next fragment's header, and all fragments carry the version of the first.
The client caps a message at 4096 fragments; so does `maxFragments` here.

Not covered: SystemEvent frames that a PLC interleaves between fragments. V3
fragments carry a chained HMAC on top of this layout (`LeanS7CommPlus.Integrity`).
-/

namespace LeanS7CommPlus

open LeanS7

/-- The most fragments one message may have, as in the Python client. -/
def maxFragments : Nat := 4096

/-- One fragment: a frame header and the data, without a trailer. -/
def encodeFragment (version : FrameVersion) (data : ByteArray) : ByteArray :=
  encodeFrameHeader version (UInt16.ofNat data.size) ++ data

/-- Fragments in order, with the trailer after the last. -/
def encodeFragments (version : FrameVersion) : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | [data] => encodeFragment version data ++ frameTrailer version
  | data :: next :: rest => encodeFragment version data ++ encodeFragments version (next :: rest)

/-- The data of the fragments, joined in order. -/
def joinFragments : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | data :: rest => data ++ joinFragments rest

/-- A list of fragment data that `encodeFragments` encodes faithfully: at least one
    fragment and each shorter than 65536 bytes. A message of several fragments has no
    empty fragment, since an empty fragment's header `72 vv 00 00` is the trailer. -/
inductive Fragmented : List ByteArray → Prop
  | single (data : ByteArray) (hsize : data.size < 65536) : Fragmented [data]
  | cons (data next : ByteArray) (rest : List ByteArray) (hsize : data.size < 65536)
      (hnonempty : 0 < data.size) (hnext : 0 < next.size) (tail : Fragmented (next :: rest)) :
      Fragmented (data :: next :: rest)

/-- Split data into pieces of `size` bytes, the last one possibly shorter, as the
    Python emulator does with `max_response_pdu`. Empty data is one empty piece, and a
    size of zero keeps the data whole. -/
def splitData (size : Nat) (data : ByteArray) : List ByteArray :=
  if _ : size = 0 ∨ data.size ≤ size then [data]
  else data.extract 0 size :: splitData size (data.extract size data.size)
termination_by data.size
decreasing_by simp only [ByteArray.size_extract]; omega

/-- Read one fragment header with the given version, and its data. -/
def readFragment (version : FrameVersion) (cursor : Cursor) :
    Except DecodeError (ByteArray × Cursor) :=
  match cursor.readUInt8 with
  | .error error => .error error
  | .ok (id, cursor) =>
    if id != protocolId then
      .error (.invalidField (cursor.offset - 1) s!"expected S7CommPlus protocol id 0x72, got {id}")
    else match cursor.readUInt8 with
    | .error error => .error error
    | .ok (versionByte, cursor) =>
      if versionByte != version.toByte then
        .error (.invalidField (cursor.offset - 1) "fragment version differs from the first fragment")
      else match cursor.readUInt16BE with
      | .error error => .error error
      | .ok (length, cursor) => cursor.readBytes length.toNat

/-- Decode the fragments from `cursor` to the end of the data, reading at most `fuel`
    fragments. -/
def decodeFragmentsFrom (version : FrameVersion) : Nat → Cursor → Except DecodeError (List ByteArray)
  | 0, cursor => .error (.invalidField cursor.offset s!"more than {maxFragments} fragments")
  | fuel + 1, cursor =>
    match readFragment version cursor with
    | .error error => .error error
    | .ok (data, cursor) =>
      if cursor.data.extract cursor.offset (cursor.offset + 4) = frameTrailer version then
        if cursor.offset + 4 = cursor.data.size then .ok [data]
        else .error (.trailingBytes (cursor.offset + 4) (cursor.data.size - (cursor.offset + 4)))
      else if data.size = 0 then
        .error (.invalidField cursor.offset "empty fragment before the last")
      else match decodeFragmentsFrom version fuel cursor with
        | .error error => .error error
        | .ok rest => .ok (data :: rest)

/-- Strictly decode a fragmented message: its version and the data of each fragment. -/
def decodeFragments (message : ByteArray) : Except DecodeError (FrameVersion × List ByteArray) :=
  if h : 1 < message.size then
    match decodeFrameVersion 1 message[1] with
    | .error error => .error error
    | .ok version =>
      match decodeFragmentsFrom version maxFragments { data := message } with
      | .error error => .error error
      | .ok pieces => .ok (version, pieces)
  else .error (.unexpectedEnd 0 2 message.size)

/-- Reassemble a fragmented message into its version and data. -/
def reassemble (message : ByteArray) : Except DecodeError (FrameVersion × ByteArray) :=
  match decodeFragments message with
  | .error error => .error error
  | .ok (version, pieces) => .ok (version, joinFragments pieces)

/-- Whether `buffer` holds a whole fragmented message: walking the fragment headers
    from the start reaches a trailer. A receiver reads more data until this holds; the
    decoder then checks the message. A buffer that does not start with a fragment
    header counts as whole, so the decoder rejects it instead of waiting. -/
def fragmentsComplete (buffer : ByteArray) : Bool :=
  go maxFragments 0
where
  go : Nat → Nat → Bool
    | 0, _ => true
    | fuel + 1, offset =>
      if h : offset + 4 ≤ buffer.size then
        if buffer[offset] != protocolId then true
        else
          let next := offset + 4 + (buffer[offset + 2].toNat * 256 + buffer[offset + 3].toNat)
          if h' : next + 4 ≤ buffer.size then
            if buffer[next] == protocolId && buffer[next + 2] == 0 && buffer[next + 3] == 0 then true
            else go fuel next
          else false
      else false

/-! ## Facts about the encoders -/

theorem joinFragments_splitData (size : Nat) (data : ByteArray) :
    joinFragments (splitData size data) = data := by
  induction data using WellFounded.induction (InvImage.wf ByteArray.size Nat.lt_wfRel.wf) with
  | _ data ih =>
    rw [splitData]
    split
    · simp [joinFragments]
    · rename_i h
      simp only [joinFragments]
      rw [ih _ (by simp only [InvImage, ByteArray.size_extract]; show _ < _; omega),
        ByteArray.extract_append_extract_of_le _ (by omega) (by omega), ByteArray.extract_zero_size]

theorem splitData_head_size (size : Nat) (data : ByteArray) (hdata : 0 < data.size) :
    ∃ first rest, splitData size data = first :: rest ∧ 0 < first.size := by
  rw [splitData]
  split
  · exact ⟨data, [], rfl, hdata⟩
  · rename_i h
    exact ⟨_, _, rfl, by simp only [ByteArray.size_extract]; omega⟩

theorem fragmented_splitData (size : Nat) (data : ByteArray) (hsize : 0 < size) (hmax : size < 65536) :
    Fragmented (splitData size data) := by
  induction data using WellFounded.induction (InvImage.wf ByteArray.size Nat.lt_wfRel.wf) with
  | _ data ih =>
    rw [splitData]
    split
    · rename_i h
      exact .single data (by omega)
    · rename_i h
      have hrest := ih (data.extract size data.size)
        (by simp only [InvImage, ByteArray.size_extract]; show _ < _; omega)
      obtain ⟨first, rest, heq, hfirst⟩ :=
        splitData_head_size size (data.extract size data.size) (by simp only [ByteArray.size_extract]; omega)
      rw [heq] at hrest ⊢
      exact .cons _ _ _ (by simp only [ByteArray.size_extract]; omega)
        (by simp only [ByteArray.size_extract]; omega) hfirst hrest

theorem Fragmented.size_lt {pieces : List ByteArray} (h : Fragmented pieces) :
    ∀ data ∈ pieces, data.size < 65536 := by
  induction h with
  | single data hsize => simpa using hsize
  | cons data next rest hsize _ _ _ ih =>
    intro piece hpiece
    rcases List.mem_cons.mp hpiece with rfl | hpiece
    · exact hsize
    · exact ih piece hpiece

/-- The reassembled size is at most 65535 bytes per fragment. -/
theorem joinFragments_size_le (pieces : List ByteArray) (h : ∀ data ∈ pieces, data.size < 65536) :
    (joinFragments pieces).size ≤ 65535 * pieces.length := by
  induction pieces with
  | nil => simp [joinFragments]
  | cons data rest ih =>
    simp only [joinFragments, ByteArray.size_append, List.length_cons]
    have hd := h data (by simp)
    have hr := ih (fun piece hpiece => h piece (by simp [hpiece]))
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem encodeFrameHeader_size (version : FrameVersion) (length : UInt16) :
    (encodeFrameHeader version length).size = 4 := by
  simp [encodeFrameHeader, ByteArray.size_append, bytes_size, uint16BE_size]

theorem frameTrailer_size (version : FrameVersion) : (frameTrailer version).size = 4 := by
  simp [frameTrailer, bytes_size]

theorem frameTrailer_eq_header (version : FrameVersion) :
    frameTrailer version = encodeFrameHeader version 0 := by
  rfl

/-- A header with a nonzero length is not the trailer. -/
theorem encodeFrameHeader_ne_trailer (version : FrameVersion) (length : UInt16) (hlength : length ≠ 0) :
    encodeFrameHeader version length ≠ frameTrailer version := by
  intro h
  rw [frameTrailer_eq_header] at h
  have r := Cursor.readUInt16BE_append_uint16BE (bytes #[protocolId, version.toByte]) ByteArray.empty length
  have r0 := Cursor.readUInt16BE_append_uint16BE (bytes #[protocolId, version.toByte]) ByteArray.empty 0
  simp only [ByteArray.append_empty] at r r0
  simp only [encodeFrameHeader] at h
  rw [h, r0] at r
  injection r with r
  injection r with r
  exact hlength r.symm

theorem ofNat_size_ne_zero (data : ByteArray) (hpos : 0 < data.size) (hsize : data.size < 65536) :
    UInt16.ofNat data.size ≠ 0 := by
  intro h0
  have := congrArg UInt16.toNat h0
  rw [UInt16.toNat_ofNat'] at this
  simp at this
  omega

/-- The first four bytes of encoded fragments are the first fragment's header. -/
theorem encodeFragments_header (version : FrameVersion) (data : ByteArray) (rest : List ByteArray) :
    (encodeFragments version (data :: rest)).extract 0 4 =
      encodeFrameHeader version (UInt16.ofNat data.size) := by
  cases rest <;>
    simp only [encodeFragments, encodeFragment, ByteArray.append_assoc] <;>
    exact ByteArray.extract_append_eq_left (encodeFrameHeader_size _ _).symm

/-- `encodeFragments` of one fragment is a complete frame. -/
theorem encodeFragments_single (version : FrameVersion) (data : ByteArray) :
    encodeFragments version [data] = encodeFrame version data := by
  simp [encodeFragments, encodeFragment, encodeFrame]

/-! ## Canonical decoding -/

theorem readFragment_canonical (version : FrameVersion) (cursor next : Cursor) (data : ByteArray)
    (h : readFragment version cursor = .ok (data, next)) :
    next = { cursor with offset := cursor.offset + 4 + data.size } ∧
      cursor.offset + 4 + data.size ≤ cursor.data.size ∧ data.size < 65536 ∧
      cursor.data.extract cursor.offset (cursor.offset + 4 + data.size) = encodeFragment version data := by
  unfold readFragment at h
  split at h
  · contradiction
  rename_i id c0 e0
  split at h
  · contradiction
  rename_i hid
  split at h
  · contradiction
  rename_i versionByte c1 e1
  split at h
  · contradiction
  rename_i hversion
  split at h
  · contradiction
  rename_i length c2 e2
  obtain ⟨l0, d0, n0⟩ := Cursor.readUInt8_value _ _ _ e0
  subst n0
  obtain ⟨l1, d1, n1⟩ := Cursor.readUInt8_value _ _ _ e1
  subst n1
  obtain ⟨l2, d2, n2⟩ := Cursor.readUInt16BE_value _ _ _ e2
  subst n2
  have s3 := Cursor.readBytes_size _ _ _ _ h
  obtain ⟨p3, n3⟩ := Cursor.readBytes_value _ _ _ _ h
  simp only at l0 l1 l2 d0 d1 d2 p3 n3 s3
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hid hversion
  have hl3 : cursor.offset + 1 + 1 + 2 + length.toNat ≤ cursor.data.size := by
    have h1 := congrArg ByteArray.size p3
    simp only [ByteArray.size_extract] at h1
    omega
  have hsize : data.size < 65536 := by rw [s3]; exact length.toNat_lt
  refine ⟨by rw [n3, s3], by omega, hsize, ?_⟩
  have hlength : UInt16.ofNat data.size = length := by rw [s3, UInt16.ofNat_toNat]
  simp only [encodeFragment, encodeFrameHeader]
  rw [hlength, d2, ← ByteArray.extract_two_uint16BE _ _ (by omega), ← hversion, ← d1, ← hid, ← d0,
    show bytes #[cursor.data[cursor.offset], cursor.data[cursor.offset + 1]] =
      cursor.data.extract cursor.offset (cursor.offset + 2) from
      (ByteArray.extract_two cursor.data cursor.offset (by omega)).symm, p3,
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]
  congr 1
  simp only [ByteArray.size_extract]
  omega

theorem decodeFragmentsFrom_canonical (version : FrameVersion) (fuel : Nat) (cursor : Cursor)
    (pieces : List ByteArray) (h : decodeFragmentsFrom version fuel cursor = .ok pieces) :
    cursor.offset ≤ cursor.data.size ∧
      cursor.data.extract cursor.offset cursor.data.size = encodeFragments version pieces ∧
      Fragmented pieces ∧ pieces.length ≤ fuel := by
  induction fuel generalizing cursor pieces with
  | zero => simp [decodeFragmentsFrom] at h
  | succ fuel ih =>
    unfold decodeFragmentsFrom at h
    split at h
    · contradiction
    rename_i data next e
    obtain ⟨hn, hle, hsize, hbytes⟩ := readFragment_canonical _ _ _ _ e
    subst hn
    simp only at h
    split at h
    · rename_i htrailer
      split at h
      · rename_i hend
        injection h with h
        subst h
        refine ⟨by omega, ?_, .single data hsize, by simp⟩
        rw [← ByteArray.extract_append_extract_of_le cursor.data (j := cursor.offset + 4 + data.size)
          (by omega) (by omega), hbytes, ← hend, htrailer]
        rfl
      · contradiction
    · rename_i hnot
      split at h
      · contradiction
      rename_i hnonempty
      split at h
      · contradiction
      rename_i rest erest
      injection h with h
      subst h
      obtain ⟨hle', hrest, hfrag, hlen⟩ := ih _ _ erest
      simp only at hle' hrest hnot
      -- The next fragment is nonempty, since its header is not the trailer.
      have hfirst : ∀ first others, rest = first :: others → 0 < first.size := by
        intro first others heq
        subst heq
        apply Nat.pos_of_ne_zero
        intro hzero
        apply hnot
        have hlen4 : cursor.offset + 4 + data.size + 4 ≤ cursor.data.size := by
          have h1 := congrArg ByteArray.size hrest
          have h2 := congrArg ByteArray.size (encodeFragments_header version first others)
          simp only [ByteArray.size_extract, encodeFrameHeader_size] at h1 h2
          omega
        have hx : cursor.data.extract (cursor.offset + 4 + data.size) (cursor.offset + 4 + data.size + 4) =
            (cursor.data.extract (cursor.offset + 4 + data.size) cursor.data.size).extract 0 4 := by
          rw [ByteArray.extract_extract]
          congr 1 <;> omega
        rw [hx, hrest, encodeFragments_header, hzero, frameTrailer_eq_header]
        rfl
      refine ⟨by omega, ?_, ?_, by simp; omega⟩
      · rw [← ByteArray.extract_append_extract_of_le cursor.data (j := cursor.offset + 4 + data.size)
          (by omega) (by omega), hbytes, hrest]
        cases hfrag with
        | single next _ => rfl
        | cons next _ _ _ _ _ _ => rfl
      · cases hfrag with
        | single next hs => exact .cons _ _ _ hsize (by omega) (hfirst next [] rfl) (.single next hs)
        | cons next next' rest' hs hne hn t =>
          exact .cons _ _ _ hsize (by omega) hne (.cons _ _ _ hs hne hn t)

/-- Canonical decoding: every message the decoder accepts is exactly the encoding of
    its version and fragments, which are `Fragmented` and at most `maxFragments`. -/
theorem decodeFragments_canonical (message : ByteArray) (version : FrameVersion) (pieces : List ByteArray)
    (h : decodeFragments message = .ok (version, pieces)) :
    encodeFragments version pieces = message ∧ Fragmented pieces ∧ pieces.length ≤ maxFragments := by
  unfold decodeFragments at h
  split at h
  · split at h
    · contradiction
    rename_i v _
    split at h
    · contradiction
    rename_i ps e
    injection h with h
    injection h with hv hp
    subst hv hp
    obtain ⟨_, hbytes, hfrag, hlen⟩ := decodeFragmentsFrom_canonical _ _ _ _ e
    simp only [ByteArray.extract_zero_size] at hbytes
    exact ⟨hbytes.symm, hfrag, hlen⟩
  · contradiction

/-- The size bound: an accepted message has at most `maxFragments` fragments and
    reassembles to at most 65535 bytes per fragment. -/
theorem reassemble_bound (message : ByteArray) (version : FrameVersion) (data : ByteArray)
    (h : reassemble message = .ok (version, data)) :
    ∃ pieces, decodeFragments message = .ok (version, pieces) ∧ data = joinFragments pieces ∧
      pieces.length ≤ maxFragments ∧ data.size ≤ 65535 * pieces.length := by
  unfold reassemble at h
  split at h
  · contradiction
  rename_i v pieces e
  injection h with h
  injection h with hv hd
  subst hv hd
  obtain ⟨_, hfrag, hlen⟩ := decodeFragments_canonical _ _ _ e
  exact ⟨pieces, e, rfl, hlen, joinFragments_size_le pieces hfrag.size_lt⟩

/-! ## Round trips -/

private theorem cursor_offset_eq {data : ByteArray} {offset offset' : Nat} (h : offset = offset') :
    ({ data, offset } : Cursor) = { data, offset := offset' } := by
  rw [h]

theorem readFragment_append (version : FrameVersion) (pre data suffix : ByteArray)
    (hsize : data.size < 65536) :
    readFragment version { data := pre ++ (encodeFragment version data ++ suffix), offset := pre.size } =
      .ok (data,
        { data := pre ++ (encodeFragment version data ++ suffix), offset := pre.size + 4 + data.size }) := by
  have hlength : (UInt16.ofNat data.size).toNat = data.size := by
    rw [UInt16.toNat_ofNat']; omega
  have hframe : pre ++ (encodeFragment version data ++ suffix) =
      pre ++ (bytes #[protocolId] ++ (bytes #[version.toByte] ++ (uint16BE (UInt16.ofNat data.size) ++
        (data ++ suffix)))) := by
    simp only [encodeFragment, encodeFrameHeader, ByteArray.append_assoc]
    rfl
  rw [hframe]
  have r0 := Cursor.readUInt8_append_byte pre
    (bytes #[version.toByte] ++ (uint16BE (UInt16.ofNat data.size) ++ (data ++ suffix))) protocolId
  have r1 := Cursor.readUInt8_append_byte (pre ++ bytes #[protocolId])
    (uint16BE (UInt16.ofNat data.size) ++ (data ++ suffix)) version.toByte
  have r2 := Cursor.readUInt16BE_append_uint16BE (pre ++ bytes #[protocolId] ++ bytes #[version.toByte])
    (data ++ suffix) (UInt16.ofNat data.size)
  have r3 := Cursor.readBytes_append
    (pre ++ bytes #[protocolId] ++ bytes #[version.toByte] ++ uint16BE (UInt16.ofNat data.size)) data suffix
  simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, uint16BE_size,
    List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add] at r0 r1 r2 r3
  unfold readFragment
  rw [r0]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [r1]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [cursor_offset_eq (show pre.size + 1 + 1 = pre.size + 2 by omega), r2]
  simp only [hlength]
  rw [cursor_offset_eq (show pre.size + 2 + 2 = pre.size + 4 by omega)]
  rw [r3]

theorem decodeFragmentsFrom_encode (version : FrameVersion) (pre : ByteArray) (pieces : List ByteArray)
    (hpieces : Fragmented pieces) (fuel : Nat) (hfuel : pieces.length ≤ fuel) :
    decodeFragmentsFrom version fuel
      { data := pre ++ encodeFragments version pieces, offset := pre.size } = .ok pieces := by
  induction hpieces generalizing pre fuel with
  | single data hsize =>
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have r := readFragment_append version pre data (frameTrailer version) hsize
    simp only [encodeFragments]
    unfold decodeFragmentsFrom
    rw [r]
    simp only
    have hsplit : pre ++ (encodeFragment version data ++ frameTrailer version) =
        (pre ++ encodeFragment version data) ++ frameTrailer version := by
      simp [ByteArray.append_assoc]
    have hoff : pre.size + 4 + data.size = (pre ++ encodeFragment version data).size := by
      simp [ByteArray.size_append, encodeFragment, encodeFrameHeader_size]; omega
    rw [if_pos, if_pos]
    · rw [hsplit, ByteArray.size_append, hoff, ByteArray.size_append, frameTrailer_size]
    · rw [hsplit, hoff]
      exact ByteArray.extract_append_eq_right rfl (by rw [frameTrailer_size])
  | cons data next rest hsize hnonempty hnext tail ih =>
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have r := readFragment_append version pre data (encodeFragments version (next :: rest)) hsize
    have henc : encodeFragments version (data :: next :: rest) =
        encodeFragment version data ++ encodeFragments version (next :: rest) := rfl
    rw [henc]
    unfold decodeFragmentsFrom
    rw [r]
    simp only
    have hsplit : pre ++ (encodeFragment version data ++ encodeFragments version (next :: rest)) =
        (pre ++ encodeFragment version data) ++ encodeFragments version (next :: rest) := by
      simp [ByteArray.append_assoc]
    have hoff : pre.size + 4 + data.size = (pre ++ encodeFragment version data).size := by
      simp [ByteArray.size_append, encodeFragment, encodeFrameHeader_size]; omega
    have hnext_size := tail.size_lt next (by simp)
    rw [if_neg, if_neg (by omega), hsplit, hoff,
      ih (pre ++ encodeFragment version data) fuel (by simp at hfuel; omega)]
    -- The four bytes after the fragment are the next fragment's header, not the trailer.
    rw [hsplit, hoff]
    have hextract := ByteArray.extract_append_size_add (a := pre ++ encodeFragment version data)
      (b := encodeFragments version (next :: rest)) (i := 0) (j := 4)
    rw [Nat.add_zero] at hextract
    rw [hextract, encodeFragments_header]
    exact encodeFrameHeader_ne_trailer _ _ (ofNat_size_ne_zero next hnext hnext_size)

theorem encodeFragments_byte_one (version : FrameVersion) (pieces : List ByteArray)
    (h : 1 < (encodeFragments version pieces).size) (hpieces : pieces ≠ []) :
    (encodeFragments version pieces)[1] = version.toByte := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hpieces
  have hheader := encodeFragments_header version first rest
  have hsize : 4 ≤ (encodeFragments version (first :: rest)).size := by
    have := congrArg ByteArray.size hheader
    simp only [ByteArray.size_extract, encodeFrameHeader_size] at this
    omega
  have hget : (encodeFragments version (first :: rest))[1] =
      ((encodeFragments version (first :: rest)).extract 0 4)[1]'(by simp; omega) := by
    simp [ByteArray.getElem_extract]
  rw [hget]
  simp only [hheader, encodeFrameHeader]
  rfl

/-- Decoding encoded fragments returns their version and data. -/
theorem decodeFragments_encode (version : FrameVersion) (pieces : List ByteArray)
    (hpieces : Fragmented pieces) (hcount : pieces.length ≤ maxFragments) :
    decodeFragments (encodeFragments version pieces) = .ok (version, pieces) := by
  have hne : pieces ≠ [] := by cases hpieces <;> simp
  have hsize : 1 < (encodeFragments version pieces).size := by
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    have := congrArg ByteArray.size (encodeFragments_header version first rest)
    simp only [ByteArray.size_extract, encodeFrameHeader_size] at this
    omega
  unfold decodeFragments
  rw [dif_pos hsize, encodeFragments_byte_one _ _ hsize hne, decodeFrameVersion_toByte]
  simp only
  have r := decodeFragmentsFrom_encode version ByteArray.empty pieces hpieces maxFragments hcount
  simp only [ByteArray.empty_append, ByteArray.size_empty] at r
  rw [show ({ data := encodeFragments version pieces } : Cursor) =
    { data := encodeFragments version pieces, offset := 0 } from rfl, r]

/-- Reassembly order: the reassembled data is the fragments' data joined in order. -/
theorem reassemble_encodeFragments (version : FrameVersion) (pieces : List ByteArray)
    (hpieces : Fragmented pieces) (hcount : pieces.length ≤ maxFragments) :
    reassemble (encodeFragments version pieces) = .ok (version, joinFragments pieces) := by
  simp [reassemble, decodeFragments_encode version pieces hpieces hcount]

/-- Reassembly undoes the emulator's split into pieces of `size` bytes. -/
theorem reassemble_splitData (version : FrameVersion) (size : Nat) (data : ByteArray)
    (hsize : 0 < size) (hmax : size < 65536)
    (hcount : (splitData size data).length ≤ maxFragments) :
    reassemble (encodeFragments version (splitData size data)) = .ok (version, data) := by
  rw [reassemble_encodeFragments _ _ (fragmented_splitData size data hsize hmax) hcount,
    joinFragments_splitData]

/-- A complete frame is a message of one fragment. -/
theorem reassemble_encodeFrame (version : FrameVersion) (data : ByteArray) (hsize : data.size < 65536) :
    reassemble (encodeFrame version data) = .ok (version, data) := by
  rw [← encodeFragments_single,
    reassemble_encodeFragments _ _ (.single data hsize) (by simp [maxFragments])]
  simp [joinFragments]

end LeanS7CommPlus
