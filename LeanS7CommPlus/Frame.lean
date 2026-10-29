import LeanS7.Binary
import LeanS7CommPlus.Protocol

/-!
# Frames

A complete S7CommPlus PDU is a frame: the protocol id `0x72`, a version byte, the
big-endian length of the data, the data, and a trailer of the protocol id, the same
version byte and a zero word.

This module covers complete single-fragment frames, as in every frame of the
s7commplus#136 capture. PDUs that a controller splits over several fragments are
reassembled in `LeanS7CommPlus.Fragments`.
-/

namespace LeanS7CommPlus

open LeanS7

def encodeFrameHeader (version : FrameVersion) (length : UInt16) : ByteArray :=
  bytes #[protocolId, version.toByte] ++ uint16BE length

def frameTrailer (version : FrameVersion) : ByteArray :=
  bytes #[protocolId, version.toByte, 0, 0]

/-- A frame around `data`. The length field is exact for data of up to 65535 bytes,
    which covers everything `decodeFrame` accepts. -/
def encodeFrame (version : FrameVersion) (data : ByteArray) : ByteArray :=
  encodeFrameHeader version (UInt16.ofNat data.size) ++ data ++ frameTrailer version

def decodeFrameVersion (offset : Nat) (byte : UInt8) : Except DecodeError FrameVersion :=
  match FrameVersion.ofByte? byte with
  | some version => .ok version
  | none => .error (.invalidField offset s!"unknown S7CommPlus frame version {byte}")

/-- Strictly decode one complete frame: header, exactly `length` data bytes, and a
    trailer with the same version and a zero word, with nothing after it. -/
def decodeFrame (frame : ByteArray) : Except DecodeError (FrameVersion × ByteArray) := do
  let cursor : Cursor := { data := frame }
  let (id, cursor) ← cursor.readUInt8
  if id != protocolId then
    throw (.invalidField 0 s!"expected S7CommPlus protocol id 0x72, got {id}")
  let (versionByte, cursor) ← cursor.readUInt8
  let version ← decodeFrameVersion 1 versionByte
  let (length, cursor) ← cursor.readUInt16BE
  let (data, cursor) ← cursor.readBytes length.toNat
  let (trailerId, cursor) ← cursor.readUInt8
  if trailerId != protocolId then
    throw (.invalidField (4 + length.toNat) s!"expected trailer protocol id 0x72, got {trailerId}")
  let (trailerVersion, cursor) ← cursor.readUInt8
  if trailerVersion != versionByte then
    throw (.invalidField (5 + length.toNat) "trailer version differs from the header version")
  let (trailerWord, cursor) ← cursor.readUInt16BE
  if trailerWord != 0 then
    throw (.invalidField (6 + length.toNat) "trailer word is not zero")
  cursor.finish
  return (version, data)

theorem decodeFrameVersion_ok (offset : Nat) (byte : UInt8) (version : FrameVersion)
    (h : decodeFrameVersion offset byte = .ok version) : version.toByte = byte := by
  unfold decodeFrameVersion at h
  split at h
  · rename_i hv
    injection h with h
    subst h
    unfold FrameVersion.ofByte? at hv
    split at hv <;> cases hv <;> rfl
  · contradiction

/-- Canonical decoding: every frame the decoder accepts is exactly the encoding of the
    decoded version and data, so the decoder ignores no input byte. -/
theorem decodeFrame_canonical (frame : ByteArray) (version : FrameVersion) (data : ByteArray)
    (h : decodeFrame frame = .ok (version, data)) :
    encodeFrame version data = frame := by
  simp only [decodeFrame, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i x0 v0 e0 hid x1 v1 e1 x2 vrs e2 x3 v3 e3 x4 v4 e4 x5 v5 e5 htid x6 v6 e6 htver
    x7 v7 e7 htword x8 v8 e8
  obtain ⟨l0, d0, n0⟩ := Cursor.readUInt8_value _ _ _ e0
  rw [n0] at e1
  obtain ⟨l1, d1, n1⟩ := Cursor.readUInt8_value _ _ _ e1
  rw [n1] at e3
  obtain ⟨l3, d3, n3⟩ := Cursor.readUInt16BE_value _ _ _ e3
  rw [n3] at e4
  have s4 := Cursor.readBytes_size _ _ _ _ e4
  obtain ⟨p4, n4⟩ := Cursor.readBytes_value _ _ _ _ e4
  rw [n4] at e5
  obtain ⟨l5, d5, n5⟩ := Cursor.readUInt8_value _ _ _ e5
  rw [n5] at e6
  obtain ⟨l6, d6, n6⟩ := Cursor.readUInt8_value _ _ _ e6
  rw [n6] at e7
  obtain ⟨l7, d7, n7⟩ := Cursor.readUInt16BE_value _ _ _ e7
  rw [n7] at e8
  have hfin := Cursor.finish_ok _ e8
  injection h with h
  injection h with hver hdata
  subst hver hdata
  have hv := decodeFrameVersion_ok _ _ _ e2
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hid htid htver htword
  simp only at l0 l1 l3 l5 l6 l7 d0 d1 d3 d5 d6 d7 hfin p4 s4
  have hlength : UInt16.ofNat v4.fst.size = v3.fst := by
    rw [s4, UInt16.ofNat_toNat]
  simp only [encodeFrame, encodeFrameHeader, frameTrailer]
  rw [hlength, d3, ← ByteArray.extract_two_uint16BE _ _ (by omega), hv, ← d1, ← hid, ← d0,
    show bytes #[frame[0], frame[0 + 1]] = frame.extract 0 2 from
      (ByteArray.extract_two frame 0 (by omega)).symm, p4]
  have htrailer : bytes #[frame[0], frame[0 + 1], 0, 0] =
      frame.extract (0 + 1 + 1 + 2 + v3.fst.toNat) frame.size := by
    have hsize : frame.size = 0 + 1 + 1 + 2 + v3.fst.toNat + 1 + 1 + 2 := by omega
    have hid' : frame[0 + 1 + 1 + 2 + v3.fst.toNat] = frame[0] :=
      d5.trans (htid.trans (hid.symm.trans d0.symm))
    have hver' : frame[0 + 1 + 1 + 2 + v3.fst.toNat + 1] = frame[0 + 1] :=
      d6.trans (htver.trans d1.symm)
    have hzero := htword
    rw [d7] at hzero
    have hword := congrArg UInt16.toNat hzero
    rw [UInt16.toNat_ofNat'] at hword
    have hb6 := (frame[0 + 1 + 1 + 2 + v3.fst.toNat + 1 + 1]).toNat_lt
    have hb7 := (frame[0 + 1 + 1 + 2 + v3.fst.toNat + 1 + 1 + 1]).toNat_lt
    have hhigh : frame[0 + 1 + 1 + 2 + v3.fst.toNat + 1 + 1] = 0 := by
      apply UInt8.toNat_inj.mp
      simp only [UInt16.toNat_zero] at hword
      simp only [UInt8.toNat_zero]
      omega
    have hlow : frame[0 + 1 + 1 + 2 + v3.fst.toNat + 1 + 1 + 1] = 0 := by
      apply UInt8.toNat_inj.mp
      simp only [UInt16.toNat_zero] at hword
      simp only [UInt8.toNat_zero]
      omega
    apply ByteArray.ext
    simp only [bytes, ByteArray.data_extract]
    apply Array.ext
    · simp; omega
    · intro i hi _
      simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
      · simp only [Array.getElem_extract, ← ByteArray.getElem_eq_getElem_data]
        exact hid'.symm
      · simp only [Array.getElem_extract, ← ByteArray.getElem_eq_getElem_data]
        exact hver'.symm
      · simp only [Array.getElem_extract, ← ByteArray.getElem_eq_getElem_data]
        exact hhigh.symm
      · simp only [Array.getElem_extract, ← ByteArray.getElem_eq_getElem_data]
        exact hlow.symm
  rw [htrailer, ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_zero_size]


theorem decodeFrameVersion_toByte (offset : Nat) (version : FrameVersion) :
    decodeFrameVersion offset version.toByte = .ok version := by
  simp [decodeFrameVersion, FrameVersion.ofByte?_toByte]

/-- Decoding a frame built by `encodeFrame` returns its version and data. -/
theorem decodeFrame_encodeFrame (version : FrameVersion) (data : ByteArray)
    (hsize : data.size < 65536) :
    decodeFrame (encodeFrame version data) = .ok (version, data) := by
  have hlength : (UInt16.ofNat data.size).toNat = data.size := by
    rw [UInt16.toNat_ofNat']; omega
  have hframe : encodeFrame version data =
      bytes #[protocolId] ++ (bytes #[version.toByte] ++ (uint16BE (UInt16.ofNat data.size) ++
        (data ++ (bytes #[protocolId] ++ (bytes #[version.toByte] ++ uint16BE 0))))) := by
    simp only [encodeFrame, encodeFrameHeader, frameTrailer, ByteArray.append_assoc]
    rfl
  rw [hframe]
  have r0 := Cursor.readUInt8_append_byte ByteArray.empty
    (bytes #[version.toByte] ++ (uint16BE (UInt16.ofNat data.size) ++
      (data ++ (bytes #[protocolId] ++ (bytes #[version.toByte] ++ uint16BE 0))))) protocolId
  have r1 := Cursor.readUInt8_append_byte (bytes #[protocolId])
    (uint16BE (UInt16.ofNat data.size) ++
      (data ++ (bytes #[protocolId] ++ (bytes #[version.toByte] ++ uint16BE 0)))) version.toByte
  have r2 := Cursor.readUInt16BE_append_uint16BE (bytes #[protocolId] ++ bytes #[version.toByte])
    (data ++ (bytes #[protocolId] ++ (bytes #[version.toByte] ++ uint16BE 0)))
    (UInt16.ofNat data.size)
  have r3 := Cursor.readBytes_append
    (bytes #[protocolId] ++ bytes #[version.toByte] ++ uint16BE (UInt16.ofNat data.size)) data
    (bytes #[protocolId] ++ (bytes #[version.toByte] ++ uint16BE 0))
  have r4 := Cursor.readUInt8_append_byte
    (bytes #[protocolId] ++ bytes #[version.toByte] ++ uint16BE (UInt16.ofNat data.size) ++ data)
    (bytes #[version.toByte] ++ uint16BE 0) protocolId
  have r5 := Cursor.readUInt8_append_byte
    (bytes #[protocolId] ++ bytes #[version.toByte] ++ uint16BE (UInt16.ofNat data.size) ++ data ++
      bytes #[protocolId]) (uint16BE 0) version.toByte
  have r6 := Cursor.readUInt16BE_append_uint16BE
    (bytes #[protocolId] ++ bytes #[version.toByte] ++ uint16BE (UInt16.ofNat data.size) ++ data ++
      bytes #[protocolId] ++ bytes #[version.toByte]) ByteArray.empty 0
  simp only [ByteArray.append_assoc, ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_append, bytes_size, uint16BE_size, ByteArray.size_empty, List.size_toArray,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add] at r0 r1 r2 r3 r4 r5 r6
  rw [show 1 + (1 + (2 + data.size)) = 4 + data.size by omega] at r4
  rw [show 1 + (1 + (2 + (data.size + 1))) = 4 + data.size + 1 by omega] at r5
  rw [show 1 + (1 + (2 + (data.size + (1 + 1)))) = 4 + data.size + 1 + 1 by omega] at r6
  unfold decodeFrame
  simp only [bind, Except.bind, pure, Except.pure]
  rw [show ({ data := bytes #[protocolId] ++ (bytes #[version.toByte] ++
      (uint16BE (UInt16.ofNat data.size) ++ (data ++ (bytes #[protocolId] ++
        (bytes #[version.toByte] ++ uint16BE 0))))) } : Cursor) =
      { data := bytes #[protocolId] ++ (bytes #[version.toByte] ++
      (uint16BE (UInt16.ofNat data.size) ++ (data ++ (bytes #[protocolId] ++
        (bytes #[version.toByte] ++ uint16BE 0))))), offset := 0 } from rfl, r0]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [r1]
  simp only [decodeFrameVersion_toByte]
  rw [r2]
  simp only [hlength]
  rw [r3]
  simp only
  rw [r4]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [r5]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [r6]
  simp [Cursor.finish, ByteArray.size_append, bytes_size, uint16BE_size]
  rw [if_pos (by omega)]

end LeanS7CommPlus
