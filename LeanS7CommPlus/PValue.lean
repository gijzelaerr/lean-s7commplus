import LeanS7.Binary
import LeanS7CommPlus.Vlq
import LeanS7CommPlus.VlqSigned

/-!
# Typed values (PValues)

A PValue is a flags byte, a datatype byte and the value. This module covers scalar
values, BLOBs and WSTRINGs with flags `0x00`. Arrays (flags `0x10`) and structs come
later: the Python reference is inconsistent for both (64-bit VLQ array elements are
read with the 32-bit reader, and `skip_typed_value` does not handle packed structs),
so their wire format is pinned with evidence first.

Value encodings, from `s7commplus/codec.py` (`encode_pvalue_typed`,
`decode_pvalue_to_bytes`):

- fixed width, big-endian: BOOL, USINT, BYTE, SINT (1), UINT, WORD, INT (2), DWORD,
  REAL, RID (4), LWORD, LREAL, TIMESTAMP (8);
- VLQ: UDINT and AID (unsigned 32), ULINT (unsigned 64), DINT (signed 32), LINT and
  TIMESPAN (signed 64);
- BLOB: a VLQ root id, a VLQ length and the bytes;
- WSTRING: a VLQ length and the UTF-8 bytes. They are kept as bytes; checking that
  they are valid UTF-8 is a separate concern.

SINT and INT are kept as their bit patterns, REAL and LREAL as their IEEE bits.
-/

namespace LeanS7CommPlus

open LeanS7

namespace DataType
def null : UInt8 := 0x00
def bool : UInt8 := 0x01
def usint : UInt8 := 0x02
def uint : UInt8 := 0x03
def udint : UInt8 := 0x04
def ulint : UInt8 := 0x05
def sint : UInt8 := 0x06
def int : UInt8 := 0x07
def dint : UInt8 := 0x08
def lint : UInt8 := 0x09
def byte : UInt8 := 0x0a
def word : UInt8 := 0x0b
def dword : UInt8 := 0x0c
def lword : UInt8 := 0x0d
def real : UInt8 := 0x0e
def lreal : UInt8 := 0x0f
def timestamp : UInt8 := 0x10
def timespan : UInt8 := 0x11
def rid : UInt8 := 0x12
def aid : UInt8 := 0x13
def blob : UInt8 := 0x14
def wstring : UInt8 := 0x15
end DataType

inductive PValue where
  | null
  | bool (raw : UInt8)
  | usint (value : UInt8)
  | uint (value : UInt16)
  | udint (value : UInt32)
  | ulint (value : UInt64)
  | sint (bits : UInt8)
  | int (bits : UInt16)
  | dint (value : Int32)
  | lint (value : Int64)
  | byte (value : UInt8)
  | word (value : UInt16)
  | dword (value : UInt32)
  | lword (value : UInt64)
  | real (bits : UInt32)
  | lreal (bits : UInt64)
  | timestamp (value : UInt64)
  | timespan (value : Int64)
  | rid (value : UInt32)
  | aid (value : UInt32)
  | blob (root : UInt32) (data : ByteArray)
  | wstring (utf8 : ByteArray)
  deriving BEq

/-- The datatype byte of a value. -/
def PValue.datatype : PValue → UInt8
  | .null => DataType.null
  | .bool _ => DataType.bool
  | .usint _ => DataType.usint
  | .uint _ => DataType.uint
  | .udint _ => DataType.udint
  | .ulint _ => DataType.ulint
  | .sint _ => DataType.sint
  | .int _ => DataType.int
  | .dint _ => DataType.dint
  | .lint _ => DataType.lint
  | .byte _ => DataType.byte
  | .word _ => DataType.word
  | .dword _ => DataType.dword
  | .lword _ => DataType.lword
  | .real _ => DataType.real
  | .lreal _ => DataType.lreal
  | .timestamp _ => DataType.timestamp
  | .timespan _ => DataType.timespan
  | .rid _ => DataType.rid
  | .aid _ => DataType.aid
  | .blob _ _ => DataType.blob
  | .wstring _ => DataType.wstring

/-- A VLQ length followed by the bytes. -/
def encodeBytes (data : ByteArray) : ByteArray :=
  Vlq.encodeUInt32 (UInt32.ofNat data.size) ++ data

def decodeBytes (cursor : Cursor) : Except DecodeError (ByteArray × Cursor) := do
  let (length, cursor) ← Vlq.decodeUInt32 cursor
  cursor.readBytes length.toNat

/-- The value bytes after the flags and datatype bytes. -/
def PValue.encodeBody : PValue → ByteArray
  | .null => ByteArray.empty
  | .bool raw => bytes #[raw]
  | .usint value => bytes #[value]
  | .uint value => uint16BE value
  | .udint value => Vlq.encodeUInt32 value
  | .ulint value => Vlq.encodeUInt64 value
  | .sint bits => bytes #[bits]
  | .int bits => uint16BE bits
  | .dint value => Vlq.encodeInt32 value
  | .lint value => Vlq.encodeInt64 value
  | .byte value => bytes #[value]
  | .word value => uint16BE value
  | .dword value => uint32BE value
  | .lword value => uint64BE value
  | .real bits => uint32BE bits
  | .lreal bits => uint64BE bits
  | .timestamp value => uint64BE value
  | .timespan value => Vlq.encodeInt64 value
  | .rid value => uint32BE value
  | .aid value => Vlq.encodeUInt32 value
  | .blob root data => Vlq.encodeUInt32 root ++ encodeBytes data
  | .wstring utf8 => encodeBytes utf8

/-- A scalar PValue: flags `0x00`, the datatype byte and the value bytes. BLOB and
    WSTRING lengths are exact up to 2^32 - 1 bytes. -/
def PValue.encode (value : PValue) : ByteArray :=
  bytes #[0x00, value.datatype] ++ value.encodeBody

def decodePValueBody (datatype : UInt8) (cursor : Cursor) :
    Except DecodeError (PValue × Cursor) :=
  if datatype = DataType.null then .ok (.null, cursor)
  else if datatype = DataType.bool then (cursor.readUInt8).map fun (v, c) => (.bool v, c)
  else if datatype = DataType.usint then (cursor.readUInt8).map fun (v, c) => (.usint v, c)
  else if datatype = DataType.uint then (cursor.readUInt16BE).map fun (v, c) => (.uint v, c)
  else if datatype = DataType.udint then (Vlq.decodeUInt32 cursor).map fun (v, c) => (.udint v, c)
  else if datatype = DataType.ulint then (Vlq.decodeUInt64 cursor).map fun (v, c) => (.ulint v, c)
  else if datatype = DataType.sint then (cursor.readUInt8).map fun (v, c) => (.sint v, c)
  else if datatype = DataType.int then (cursor.readUInt16BE).map fun (v, c) => (.int v, c)
  else if datatype = DataType.dint then (Vlq.decodeInt32 cursor).map fun (v, c) => (.dint v, c)
  else if datatype = DataType.lint then (Vlq.decodeInt64 cursor).map fun (v, c) => (.lint v, c)
  else if datatype = DataType.byte then (cursor.readUInt8).map fun (v, c) => (.byte v, c)
  else if datatype = DataType.word then (cursor.readUInt16BE).map fun (v, c) => (.word v, c)
  else if datatype = DataType.dword then (cursor.readUInt32BE).map fun (v, c) => (.dword v, c)
  else if datatype = DataType.lword then (cursor.readUInt64BE).map fun (v, c) => (.lword v, c)
  else if datatype = DataType.real then (cursor.readUInt32BE).map fun (v, c) => (.real v, c)
  else if datatype = DataType.lreal then (cursor.readUInt64BE).map fun (v, c) => (.lreal v, c)
  else if datatype = DataType.timestamp then (cursor.readUInt64BE).map fun (v, c) => (.timestamp v, c)
  else if datatype = DataType.timespan then (Vlq.decodeInt64 cursor).map fun (v, c) => (.timespan v, c)
  else if datatype = DataType.rid then (cursor.readUInt32BE).map fun (v, c) => (.rid v, c)
  else if datatype = DataType.aid then (Vlq.decodeUInt32 cursor).map fun (v, c) => (.aid v, c)
  else if datatype = DataType.blob then do
    let (root, cursor) ← Vlq.decodeUInt32 cursor
    let (data, cursor) ← decodeBytes cursor
    pure (.blob root data, cursor)
  else if datatype = DataType.wstring then (decodeBytes cursor).map fun (v, c) => (.wstring v, c)
  else .error (.invalidField cursor.offset s!"unsupported PValue datatype {datatype}")

/-- Decode a scalar PValue. Flags other than `0x00` (arrays and the rest) are
    rejected until their encodings are pinned down. -/
def decodePValue (cursor : Cursor) : Except DecodeError (PValue × Cursor) := do
  let (flags, cursor) ← cursor.readUInt8
  if flags != 0x00 then
    throw (.invalidField (cursor.offset - 1) s!"unsupported PValue flags {flags}")
  let (datatype, cursor) ← cursor.readUInt8
  decodePValueBody datatype cursor

/-! ## Round trip -/

/-- BLOB and WSTRING lengths fit their VLQ length field. -/
def PValue.LengthsFit : PValue → Prop
  | .blob _ data => data.size < 2 ^ 32
  | .wstring utf8 => utf8.size < 2 ^ 32
  | _ => True

theorem decodeBytes_encodeBytes (data pre suffix : ByteArray) (hsize : data.size < 2 ^ 32) :
    decodeBytes { data := pre ++ (encodeBytes data ++ suffix), offset := pre.size } =
      .ok (data,
        { data := pre ++ (encodeBytes data ++ suffix),
          offset := pre.size + (encodeBytes data).size }) := by
  have hlen : (UInt32.ofNat data.size).toNat = data.size := by
    rw [UInt32.toNat_ofNat']; omega
  unfold decodeBytes encodeBytes
  rw [ByteArray.append_assoc, Vlq.decodeUInt32_encodeUInt32]
  simp only [bind, Except.bind, hlen]
  have h := Cursor.readBytes_append (pre ++ Vlq.encodeUInt32 (UInt32.ofNat data.size)) data suffix
  simp only [ByteArray.append_assoc, ByteArray.size_append] at h
  rw [h]
  simp only [ByteArray.size_append]
  congr 2
  simp only [Cursor.mk.injEq, true_and]
  omega

/-- Decoding the value bytes of any scalar value, after its datatype byte and inside
    arbitrary surrounding bytes, returns the value and consumes exactly its bytes. -/
theorem decodePValueBody_encodeBody (value : PValue) (hfit : value.LengthsFit)
    (pre suffix : ByteArray) :
    decodePValueBody value.datatype
        { data := pre ++ (value.encodeBody ++ suffix), offset := pre.size } =
      .ok (value,
        { data := pre ++ (value.encodeBody ++ suffix),
          offset := pre.size + value.encodeBody.size }) := by
  cases value <;>
    simp only [PValue.datatype, PValue.encodeBody, decodePValueBody, DataType.null,
      DataType.bool, DataType.usint, DataType.uint, DataType.udint, DataType.ulint,
      DataType.sint, DataType.int, DataType.dint, DataType.lint, DataType.byte, DataType.word,
      DataType.dword, DataType.lword, DataType.real, DataType.lreal, DataType.timestamp,
      DataType.timespan, DataType.rid, DataType.aid, DataType.blob, DataType.wstring]
  all_goals simp (config := { decide := true }) only [if_true, if_false]
  case blob root data =>
    simp only [PValue.LengthsFit] at hfit
    rw [ByteArray.append_assoc, Vlq.decodeUInt32_encodeUInt32]
    simp only [bind, Except.bind]
    have h := decodeBytes_encodeBytes data (pre ++ Vlq.encodeUInt32 root) suffix hfit
    simp only [ByteArray.append_assoc, ByteArray.size_append] at h
    rw [h]
    simp only [pure, Except.pure, ByteArray.size_append, Nat.add_assoc]
  case wstring utf8 =>
    simp only [PValue.LengthsFit] at hfit
    rw [decodeBytes_encodeBytes _ _ _ hfit]
    rfl
  all_goals first
    | rfl
    | (rw [Cursor.readUInt8_append_byte]; rfl)
    | (rw [Cursor.readUInt16BE_append_uint16BE]; rfl)
    | (rw [Cursor.readUInt32BE_append_uint32BE]; rfl)
    | (rw [Cursor.readUInt64BE_append_uint64BE]; rfl)
    | (rw [Vlq.decodeUInt32_encodeUInt32]; rfl)
    | (rw [Vlq.decodeUInt64_encodeUInt64]; rfl)
    | (rw [Vlq.decodeInt32_encodeInt32]; rfl)
    | (rw [Vlq.decodeInt64_encodeInt64]; rfl)

/-- Decoding the encoding of any scalar PValue, inside arbitrary surrounding bytes,
    returns the value and consumes exactly its encoding. -/
theorem decodePValue_encode (value : PValue) (hfit : value.LengthsFit) (pre suffix : ByteArray) :
    decodePValue { data := pre ++ (value.encode ++ suffix), offset := pre.size } =
      .ok (value,
        { data := pre ++ (value.encode ++ suffix),
          offset := pre.size + value.encode.size }) := by
  have hshape : value.encode ++ suffix =
      bytes #[0x00] ++ (bytes #[value.datatype] ++ (value.encodeBody ++ suffix)) := by
    simp only [PValue.encode, ← ByteArray.append_assoc]
    rfl
  have r0 := Cursor.readUInt8_append_byte pre
    (bytes #[value.datatype] ++ (value.encodeBody ++ suffix)) 0x00
  have r1 := Cursor.readUInt8_append_byte (pre ++ bytes #[0x00])
    (value.encodeBody ++ suffix) value.datatype
  have r2 := decodePValueBody_encodeBody value hfit (pre ++ bytes #[0x00] ++ bytes #[value.datatype])
    suffix
  simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, List.size_toArray,
    List.length_cons, List.length_nil] at r1 r2
  rw [hshape]
  unfold decodePValue
  rw [r0]
  simp only [bind, Except.bind, bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [r1]
  simp only
  rw [show pre.size + (0 + 1) + 1 = pre.size + (0 + 1 + (0 + 1)) by omega, r2]
  have hsize : value.encode.size = 2 + value.encodeBody.size := by
    simp [PValue.encode]
  rw [hsize]
  congr 2
  simp only [Cursor.mk.injEq, true_and]
  omega

end LeanS7CommPlus
