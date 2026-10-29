import LeanS7.Binary
import LeanS7CommPlus.Vlq
import LeanS7CommPlus.PValue

/-!
# Attribute values and the object tree

An attribute or struct member holds a scalar PValue, a fixed-size array or a struct.

- A **fixed-size array** is flags `0x10`, the element datatype, a VLQ element count
  and the elements. Only element types with a fixed size are accepted: BOOL, USINT,
  BYTE, SINT (1 byte), UINT, WORD, INT (2), REAL, RID (4), LREAL, TIMESTAMP (8). The
  CreateObject reply of a CPU 1214C carries its session challenge as a USINT array.
  Arrays of VLQ element types are not accepted yet: the Python reference reads them
  inconsistently (gijzelaerr/s7commplus#147).
- A **struct** is flags `0x00`, datatype `0x17`, a big-endian struct id, members as
  a nonzero VLQ key followed by a value, and a `0x00` terminator. Packed structs are
  not accepted yet (gijzelaerr/s7commplus#150).

The object tree is read as a flat sequence of items with a stack of open objects
and structs, so nesting needs no recursive datatype:

- `A1` relation id (big-endian), class id, class flags, attribute id (VLQs): start of
  an object;
- `A2`: end of an object;
- `A3` attribute id (VLQ) and a value: an attribute (a struct value opens a struct);
- `A4` relation id (VLQ) and a big-endian target: a relation;
- inside a struct, a key and a value (a struct value opens a struct), or `0x00` to
  close it.
-/

namespace LeanS7CommPlus

open LeanS7

/-! ## Fixed-size arrays and values -/

/-- The element size of an array datatype, or 0 when arrays of it are not accepted. -/
def arrayElementSize (datatype : UInt8) : Nat :=
  if datatype = DataType.bool ∨ datatype = DataType.usint ∨ datatype = DataType.byte ∨
      datatype = DataType.sint then 1
  else if datatype = DataType.uint ∨ datatype = DataType.word ∨ datatype = DataType.int then 2
  else if datatype = DataType.real ∨ datatype = DataType.rid then 4
  else if datatype = DataType.lreal ∨ datatype = DataType.timestamp then 8
  else 0

inductive Value where
  | scalar (value : PValue)
  | array (datatype : UInt8) (elements : ByteArray)
  deriving BEq

def Value.encode : Value → ByteArray
  | .scalar value => value.encode
  | .array datatype elements =>
    bytes #[0x10, datatype] ++
      Vlq.encodeUInt32 (UInt32.ofNat (elements.size / arrayElementSize datatype)) ++ elements

def Value.Fits : Value → Prop
  | .scalar value => value.LengthsFit
  | .array datatype elements =>
    0 < arrayElementSize datatype ∧ elements.size % arrayElementSize datatype = 0 ∧
      elements.size / arrayElementSize datatype < 2 ^ 32

def decodeArray (cursor : Cursor) : Except DecodeError (Value × Cursor) := do
  let (_, cursor) ← cursor.readUInt8
  let (datatype, cursor) ← cursor.readUInt8
  let size := arrayElementSize datatype
  if size = 0 then
    throw (.invalidField cursor.offset s!"unsupported array element datatype {datatype}")
  let (count, cursor) ← Vlq.decodeUInt32 cursor
  let (elements, cursor) ← cursor.readBytes (count.toNat * size)
  pure (.array datatype elements, cursor)

/-- Decode a scalar value (flags `0x00`) or a fixed-size array (flags `0x10`). -/
def decodeValue (cursor : Cursor) : Except DecodeError (Value × Cursor) := do
  let (flags, _) ← cursor.readUInt8
  if flags = 0x10 then decodeArray cursor
  else (decodePValue cursor).map fun (value, next) => (.scalar value, next)

/-! ## Tree items -/

inductive Frame where
  | object
  | struct
  deriving BEq, DecidableEq

inductive Item where
  | objectStart (relationId classId classFlags attributeId : UInt32)
  | objectEnd
  | attribute (id : UInt32) (value : Value)
  | attributeStruct (id : UInt32) (structId : UInt32)
  | relation (id : UInt32) (target : UInt32)
  | member (key : UInt32) (value : Value)
  | memberStruct (key : UInt32) (structId : UInt32)
  | structEnd
  deriving BEq

def structHeader (structId : UInt32) : ByteArray :=
  bytes #[0x00, 0x17] ++ uint32BE structId

def Item.encode : Item → ByteArray
  | .objectStart relationId classId classFlags attributeId =>
    bytes #[0xa1] ++ uint32BE relationId ++ Vlq.encodeUInt32 classId ++
      Vlq.encodeUInt32 classFlags ++ Vlq.encodeUInt32 attributeId
  | .objectEnd => bytes #[0xa2]
  | .attribute id value => bytes #[0xa3] ++ Vlq.encodeUInt32 id ++ value.encode
  | .attributeStruct id structId => bytes #[0xa3] ++ Vlq.encodeUInt32 id ++ structHeader structId
  | .relation id target => bytes #[0xa4] ++ Vlq.encodeUInt32 id ++ uint32BE target
  | .member key value => Vlq.encodeUInt32 key ++ value.encode
  | .memberStruct key structId => Vlq.encodeUInt32 key ++ structHeader structId
  | .structEnd => bytes #[0x00]

def encodeItems : List Item → ByteArray
  | [] => ByteArray.empty
  | item :: rest => item.encode ++ encodeItems rest

/-- The stack after an item, or `none` when the item cannot follow. -/
def step : List Frame → Item → Option (List Frame)
  | [], .objectStart .. => some [.object]
  | [], _ => none
  | .object :: rest, item =>
    match item with
    | .objectStart .. => some (.object :: .object :: rest)
    | .objectEnd => some rest
    | .attribute .. => some (.object :: rest)
    | .attributeStruct .. => some (.struct :: .object :: rest)
    | .relation .. => some (.object :: rest)
    | _ => none
  | .struct :: rest, item =>
    match item with
    | .member .. => some (.struct :: rest)
    | .memberStruct .. => some (.struct :: .struct :: rest)
    | .structEnd => some rest
    | _ => none

/-- The value after an attribute id or member key: a struct header opens a struct. -/
def decodeSlot (cursor : Cursor) : Except DecodeError (Sum UInt32 Value × Cursor) := do
  let (flags, afterFlags) ← cursor.readUInt8
  let (datatype, afterType) ← afterFlags.readUInt8
  if flags = 0x00 ∧ datatype = 0x17 then
    let (structId, next) ← afterType.readUInt32BE
    pure (.inl structId, next)
  else
    let (value, next) ← decodeValue cursor
    pure (.inr value, next)

/-- Decode one item. Outside a struct (and at the start, `top = .object`) it is an
    object element; inside a struct it is a member or the struct terminator. -/
def decodeItem (top : Frame) (cursor : Cursor) : Except DecodeError (Item × Cursor) :=
  match top with
  | .object => do
    let (tag, cursor) ← cursor.readUInt8
    if tag = 0xa1 then
      let (relationId, cursor) ← cursor.readUInt32BE
      let (classId, cursor) ← Vlq.decodeUInt32 cursor
      let (classFlags, cursor) ← Vlq.decodeUInt32 cursor
      let (attributeId, cursor) ← Vlq.decodeUInt32 cursor
      pure (.objectStart relationId classId classFlags attributeId, cursor)
    else if tag = 0xa2 then
      pure (.objectEnd, cursor)
    else if tag = 0xa3 then
      let (id, cursor) ← Vlq.decodeUInt32 cursor
      let (slot, cursor) ← decodeSlot cursor
      match slot with
      | .inl structId => pure (.attributeStruct id structId, cursor)
      | .inr value => pure (.attribute id value, cursor)
    else if tag = 0xa4 then
      let (id, cursor) ← Vlq.decodeUInt32 cursor
      let (target, cursor) ← cursor.readUInt32BE
      pure (.relation id target, cursor)
    else
      throw (.invalidField (cursor.offset - 1) s!"unsupported object element {tag}")
  | .struct => do
    let (first, afterFirst) ← cursor.readUInt8
    if first = 0x00 then
      pure (.structEnd, afterFirst)
    else
      let (key, cursor) ← Vlq.decodeUInt32 cursor
      if key = 0 then
        throw (.invalidField cursor.offset "struct member key 0")
      let (slot, cursor) ← decodeSlot cursor
      match slot with
      | .inl structId => pure (.memberStruct key structId, cursor)
      | .inr value => pure (.member key value, cursor)

/-- Decode items until the outermost object closes; `fuel` bounds the item count. -/
def decodeItems : Nat → List Frame → Cursor → Except DecodeError (List Item × Cursor)
  | 0, _, cursor => .error (.invalidField cursor.offset "object tree has too many items")
  | fuel + 1, stack, cursor => do
    let (item, cursor) ← decodeItem (stack.headD .object) cursor
    match step stack item with
    | none => throw (.invalidField cursor.offset "object tree element out of place")
    | some [] => pure ([item], cursor)
    | some next => do
      let (rest, cursor) ← decodeItems fuel next cursor
      pure (item :: rest, cursor)

/-- Decode one complete object tree, starting with `A1` and ending when it closes. -/
def decodeTree (cursor : Cursor) : Except DecodeError (List Item × Cursor) :=
  decodeItems cursor.remaining [] cursor

/-! ## Round trip of values -/

theorem PValue.encode_shape (value : PValue) (suffix : ByteArray) :
    value.encode ++ suffix = bytes #[0x00] ++ (bytes #[value.datatype] ++ (value.encodeBody ++ suffix)) := by
  simp only [PValue.encode, ← ByteArray.append_assoc]
  rfl

theorem PValue.datatype_ne_struct (value : PValue) : value.datatype ≠ 0x17 := by
  cases value <;> simp [PValue.datatype, DataType.null, DataType.bool, DataType.usint, DataType.uint, DataType.udint, DataType.ulint, DataType.sint, DataType.int, DataType.dint, DataType.lint, DataType.byte, DataType.word, DataType.dword, DataType.lword, DataType.real, DataType.lreal, DataType.timestamp, DataType.timespan, DataType.rid, DataType.aid, DataType.blob, DataType.wstring]

theorem decodeValue_encode (value : Value) (hfit : value.Fits) (pre suffix : ByteArray) :
    decodeValue { data := pre ++ (value.encode ++ suffix), offset := pre.size } =
      .ok (value,
        { data := pre ++ (value.encode ++ suffix),
          offset := pre.size + value.encode.size }) := by
  cases value with
  | scalar value =>
    have h := decodePValue_encode value hfit pre suffix
    unfold decodeValue
    simp only [Value.encode]
    rw [PValue.encode_shape, Cursor.readUInt8_append_byte]
    simp only [bind, Except.bind, show ¬ (0x00 : UInt8) = 0x10 by decide, if_false]
    rw [← PValue.encode_shape, h]
    rfl
  | array datatype elements =>
    obtain ⟨hsize, hmod, hcount⟩ := hfit
    have hcountNat : (UInt32.ofNat (elements.size / arrayElementSize datatype)).toNat =
        elements.size / arrayElementSize datatype := by
      rw [UInt32.toNat_ofNat']
      generalize elements.size / arrayElementSize datatype = quotient at hcount ⊢
      omega
    have hbytes : (elements.size / arrayElementSize datatype) * arrayElementSize datatype =
        elements.size := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
    have hshape : Value.encode (.array datatype elements) ++ suffix =
        bytes #[0x10] ++ (bytes #[datatype] ++
          (Vlq.encodeUInt32 (UInt32.ofNat (elements.size / arrayElementSize datatype)) ++
            (elements ++ suffix))) := by
      simp only [Value.encode, ByteArray.append_assoc]
      rfl
    have r0 := Cursor.readUInt8_append_byte pre (bytes #[datatype] ++
      (Vlq.encodeUInt32 (UInt32.ofNat (elements.size / arrayElementSize datatype)) ++
        (elements ++ suffix))) 0x10
    have r1 := Cursor.readUInt8_append_byte (pre ++ bytes #[0x10])
      (Vlq.encodeUInt32 (UInt32.ofNat (elements.size / arrayElementSize datatype)) ++
        (elements ++ suffix)) datatype
    have r2 := Vlq.decodeUInt32_encodeUInt32 (UInt32.ofNat (elements.size / arrayElementSize datatype))
      (pre ++ bytes #[0x10] ++ bytes #[datatype]) (elements ++ suffix)
    have r3 := Cursor.readBytes_append (pre ++ bytes #[0x10] ++ bytes #[datatype] ++
      Vlq.encodeUInt32 (UInt32.ofNat (elements.size / arrayElementSize datatype))) elements suffix
    simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, List.size_toArray,
      List.length_cons, List.length_nil] at r1 r2 r3
    rw [hshape]
    unfold decodeValue decodeArray
    rw [r0]
    simp only [bind, Except.bind, if_true]
    rw [r1]
    simp only [show ¬ arrayElementSize datatype = 0 by omega, if_false]
    rw [show pre.size + 1 + 1 = pre.size + (0 + 1 + (0 + 1)) by omega, r2]
    simp only [hcountNat, hbytes]
    rw [show pre.size + (0 + 1 + (0 + 1)) +
        (Vlq.encodeUInt32 (UInt32.ofNat (elements.size / arrayElementSize datatype))).size =
        pre.size + (0 + 1 + (0 + 1 + (Vlq.encodeUInt32
          (UInt32.ofNat (elements.size / arrayElementSize datatype))).size)) by omega, r3]
    simp only [pure, Except.pure, Value.encode, ByteArray.size_append, bytes_size,
      List.size_toArray, List.length_cons, List.length_nil]
    congr 2
    simp only [Cursor.mk.injEq, true_and]
    omega

/-! ## Round trip of slots and items -/

theorem decodeSlot_struct (structId : UInt32) (pre suffix : ByteArray) :
    decodeSlot { data := pre ++ (structHeader structId ++ suffix), offset := pre.size } =
      .ok (.inl structId,
        { data := pre ++ (structHeader structId ++ suffix), offset := pre.size + 6 }) := by
  have hshape : structHeader structId ++ suffix =
      bytes #[0x00] ++ (bytes #[0x17] ++ (uint32BE structId ++ suffix)) := by
    simp only [structHeader, ByteArray.append_assoc]
    rfl
  have r1 := Cursor.readUInt8_append_byte (pre ++ bytes #[0x00]) (uint32BE structId ++ suffix) 0x17
  have r2 := Cursor.readUInt32BE_append_uint32BE (pre ++ bytes #[0x00] ++ bytes #[0x17]) suffix structId
  simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, List.size_toArray,
    List.length_cons, List.length_nil] at r1 r2
  rw [hshape]
  unfold decodeSlot
  rw [Cursor.readUInt8_append_byte]
  simp only [bind, Except.bind]
  rw [r1]
  simp only [and_self, if_true]
  rw [show pre.size + 1 + 1 = pre.size + (0 + 1 + (0 + 1)) by omega, r2]
  simp only [pure, Except.pure]

theorem decodeSlot_value (value : Value) (hfit : value.Fits) (pre suffix : ByteArray) :
    decodeSlot { data := pre ++ (value.encode ++ suffix), offset := pre.size } =
      .ok (.inr value,
        { data := pre ++ (value.encode ++ suffix),
          offset := pre.size + value.encode.size }) := by
  have hdecode := decodeValue_encode value hfit pre suffix
  obtain ⟨flags, datatype, rest, hshape, hnot⟩ : ∃ flags datatype rest,
      value.encode ++ suffix = bytes #[flags] ++ (bytes #[datatype] ++ rest) ∧
        ¬ (flags = 0x00 ∧ datatype = 0x17) := by
    cases value with
    | scalar scalar =>
      exact ⟨0x00, scalar.datatype, scalar.encodeBody ++ suffix, PValue.encode_shape scalar suffix,
        fun h => PValue.datatype_ne_struct scalar h.2⟩
    | array datatype elements =>
      refine ⟨0x10, datatype, Vlq.encodeUInt32 (UInt32.ofNat (elements.size / arrayElementSize datatype)) ++
        (elements ++ suffix), ?_, fun h => absurd h.1 (by decide)⟩
      simp only [Value.encode, ByteArray.append_assoc]
      rfl
  have r1 := Cursor.readUInt8_append_byte (pre ++ bytes #[flags]) rest datatype
  simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, List.size_toArray,
    List.length_cons, List.length_nil] at r1
  unfold decodeSlot
  rw [hshape, Cursor.readUInt8_append_byte]
  simp only [bind, Except.bind]
  rw [show pre.size + 1 = pre.size + (0 + 1) by omega, r1]
  simp only [hnot, if_false]
  rw [← hshape, hdecode]
  rfl

/-- The frame an item belongs to. -/
def Item.top : Item → Frame
  | .member .. | .memberStruct .. | .structEnd => .struct
  | _ => .object

def Item.Fits : Item → Prop
  | .attribute _ value => value.Fits
  | .member key value => key ≠ 0 ∧ value.Fits
  | .memberStruct key _ => key ≠ 0
  | _ => True

/-- The VLQ of a nonzero number starts with a nonzero byte. -/
theorem encodeUInt32_head (key : UInt32) (hkey : key ≠ 0) :
    ∃ first rest, Vlq.encodeUInt32 key = bytes #[first] ++ rest ∧ first ≠ 0 := by
  have hk : key.toNat ≠ 0 := by
    intro h; apply hkey; exact UInt32.toNat_inj.mp (by simpa using h)
  simp only [Vlq.encodeUInt32, Vlq.encodeNat]
  have hlt := Vlq.groups_lt key.toNat
  cases hrev : (Vlq.groups key.toNat).reverse with
  | nil => exact absurd (by simpa using hrev) (Vlq.groups_ne_nil key.toNat)
  | cons top lower =>
    have htop : top < 128 := hlt top (by rw [← List.mem_reverse, hrev]; simp)
    cases lower with
    | nil =>
      have hgroups : Vlq.groups key.toNat = [top] := by
        rw [← List.reverse_reverse (Vlq.groups key.toNat), hrev]; rfl
      have hsmall : key.toNat < 128 := by
        rw [Vlq.groups] at hgroups
        split at hgroups
        · assumption
        · rename_i hlarge
          have hne := Vlq.groups_ne_nil (key.toNat / 128)
          simp only [List.cons.injEq] at hgroups
          exact absurd hgroups.2 hne
      have htopval : top = key.toNat := by
        rw [Vlq.groups, if_pos hsmall] at hgroups
        simpa using hgroups.symm
      refine ⟨UInt8.ofNat top, ByteArray.empty, rfl, ?_⟩
      intro h
      have := congrArg UInt8.toNat h
      rw [UInt8.toNat_ofNat'] at this
      simp at this
      omega
    | cons next tail =>
      refine ⟨UInt8.ofNat (top + 128), (Vlq.encodeGroups (next :: tail)).toByteArray, ?_, ?_⟩
      · simp only [Vlq.encodeGroups]
        rw [show UInt8.ofNat (top + 128) :: Vlq.encodeGroups (next :: tail) =
          [UInt8.ofNat (top + 128)] ++ Vlq.encodeGroups (next :: tail) from rfl,
          List.toByteArray_append]
        rfl
      · intro h
        have := congrArg UInt8.toNat h
        rw [UInt8.toNat_ofNat'] at this
        simp at this
        omega

/-- Reading at an offset given in any arithmetic form. -/
private theorem cursor_offset_eq {data : ByteArray} {offset offset' : Nat} (h : offset = offset') :
    ({ data, offset } : Cursor) = { data, offset := offset' } := by
  rw [h]

theorem decodeItem_encode (item : Item) (hfit : item.Fits) (pre suffix : ByteArray) :
    decodeItem item.top { data := pre ++ (item.encode ++ suffix), offset := pre.size } =
      .ok (item,
        { data := pre ++ (item.encode ++ suffix),
          offset := pre.size + item.encode.size }) := by
  cases item
  case objectStart relationId classId classFlags attributeId =>
    have hshape : Item.encode (.objectStart relationId classId classFlags attributeId) ++ suffix =
        bytes #[0xa1] ++ (uint32BE relationId ++ (Vlq.encodeUInt32 classId ++
          (Vlq.encodeUInt32 classFlags ++ (Vlq.encodeUInt32 attributeId ++ suffix)))) := by
      simp only [Item.encode, ByteArray.append_assoc]
    have r1 := Cursor.readUInt32BE_append_uint32BE (pre ++ bytes #[0xa1])
      (Vlq.encodeUInt32 classId ++ (Vlq.encodeUInt32 classFlags ++ (Vlq.encodeUInt32 attributeId ++ suffix)))
      relationId
    have r2 := Vlq.decodeUInt32_encodeUInt32 classId (pre ++ bytes #[0xa1] ++ uint32BE relationId)
      (Vlq.encodeUInt32 classFlags ++ (Vlq.encodeUInt32 attributeId ++ suffix))
    have r3 := Vlq.decodeUInt32_encodeUInt32 classFlags
      (pre ++ bytes #[0xa1] ++ uint32BE relationId ++ Vlq.encodeUInt32 classId)
      (Vlq.encodeUInt32 attributeId ++ suffix)
    have r4 := Vlq.decodeUInt32_encodeUInt32 attributeId
      (pre ++ bytes #[0xa1] ++ uint32BE relationId ++ Vlq.encodeUInt32 classId ++
        Vlq.encodeUInt32 classFlags) suffix
    simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, List.size_toArray,
      List.length_cons, List.length_nil, uint32BE_size] at r1 r2 r3 r4
    simp only [Item.top]
    rw [hshape]
    unfold decodeItem
    rw [Cursor.readUInt8_append_byte]
    simp only [bind, Except.bind, if_true]
    rw [cursor_offset_eq (show pre.size + 1 = pre.size + (0 + 1) by omega), r1]
    simp only
    rw [cursor_offset_eq (show pre.size + (0 + 1) + 4 = pre.size + (0 + 1 + 4) by omega), r2]
    simp only
    rw [cursor_offset_eq (show pre.size + (0 + 1 + 4) + (Vlq.encodeUInt32 classId).size =
      pre.size + (0 + 1 + (4 + (Vlq.encodeUInt32 classId).size)) by omega), r3]
    simp only
    rw [cursor_offset_eq (show pre.size + (0 + 1 + (4 + (Vlq.encodeUInt32 classId).size)) +
        (Vlq.encodeUInt32 classFlags).size =
      pre.size + (0 + 1 + (4 + ((Vlq.encodeUInt32 classId).size +
        (Vlq.encodeUInt32 classFlags).size))) by omega), r4]
    simp only [pure, Except.pure, Item.encode, ByteArray.size_append, bytes_size, uint32BE_size,
      List.size_toArray, List.length_cons, List.length_nil]
    congr 2
    simp only [Cursor.mk.injEq, true_and]
    omega
  case objectEnd =>
    simp only [Item.top, Item.encode]
    unfold decodeItem
    rw [Cursor.readUInt8_append_byte]
    simp only [bind, Except.bind, show ¬ (0xa2 : UInt8) = 0xa1 by decide, if_false, if_true]
    rfl
  case structEnd =>
    simp only [Item.top, Item.encode]
    unfold decodeItem
    rw [Cursor.readUInt8_append_byte]
    simp only [bind, Except.bind, if_true]
    rfl
  case «attribute» id value =>
    simp only [Item.Fits] at hfit
    have r1 := Vlq.decodeUInt32_encodeUInt32 id (pre ++ bytes #[0xa3]) (value.encode ++ suffix)
    have r2 := decodeSlot_value value hfit (pre ++ bytes #[0xa3] ++ Vlq.encodeUInt32 id) suffix
    simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, List.size_toArray,
      List.length_cons, List.length_nil] at r1 r2
    simp only [Item.top, Item.encode, ByteArray.append_assoc]
    unfold decodeItem
    rw [Cursor.readUInt8_append_byte]
    simp only [bind, Except.bind, show ¬ (0xa3 : UInt8) = 0xa1 by decide,
      show ¬ (0xa3 : UInt8) = 0xa2 by decide, if_false, if_true]
    rw [cursor_offset_eq (show pre.size + 1 = pre.size + (0 + 1) by omega), r1]
    simp only
    rw [cursor_offset_eq (show pre.size + (0 + 1) + (Vlq.encodeUInt32 id).size =
      pre.size + (0 + 1 + (Vlq.encodeUInt32 id).size) by omega), r2]
    simp only [pure, Except.pure, ByteArray.size_append, bytes_size, List.size_toArray,
      List.length_cons, List.length_nil]
    congr 2
    simp only [Cursor.mk.injEq, true_and]
    omega
  case attributeStruct id structId =>
    have r1 := Vlq.decodeUInt32_encodeUInt32 id (pre ++ bytes #[0xa3]) (structHeader structId ++ suffix)
    have r2 := decodeSlot_struct structId (pre ++ bytes #[0xa3] ++ Vlq.encodeUInt32 id) suffix
    simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, List.size_toArray,
      List.length_cons, List.length_nil] at r1 r2
    simp only [Item.top, Item.encode, ByteArray.append_assoc]
    unfold decodeItem
    rw [Cursor.readUInt8_append_byte]
    simp only [bind, Except.bind, show ¬ (0xa3 : UInt8) = 0xa1 by decide,
      show ¬ (0xa3 : UInt8) = 0xa2 by decide, if_false, if_true]
    rw [cursor_offset_eq (show pre.size + 1 = pre.size + (0 + 1) by omega), r1]
    simp only
    rw [cursor_offset_eq (show pre.size + (0 + 1) + (Vlq.encodeUInt32 id).size =
      pre.size + (0 + 1 + (Vlq.encodeUInt32 id).size) by omega), r2]
    simp only [pure, Except.pure, ByteArray.size_append, bytes_size, List.size_toArray,
      List.length_cons, List.length_nil, structHeader, uint32BE_size]
    congr 2
  case relation id target =>
    have r1 := Vlq.decodeUInt32_encodeUInt32 id (pre ++ bytes #[0xa4]) (uint32BE target ++ suffix)
    have r2 := Cursor.readUInt32BE_append_uint32BE (pre ++ bytes #[0xa4] ++ Vlq.encodeUInt32 id)
      suffix target
    simp only [ByteArray.append_assoc, ByteArray.size_append, bytes_size, List.size_toArray,
      List.length_cons, List.length_nil] at r1 r2
    simp only [Item.top, Item.encode, ByteArray.append_assoc]
    unfold decodeItem
    rw [Cursor.readUInt8_append_byte]
    simp only [bind, Except.bind, show ¬ (0xa4 : UInt8) = 0xa1 by decide,
      show ¬ (0xa4 : UInt8) = 0xa2 by decide, show ¬ (0xa4 : UInt8) = 0xa3 by decide,
      if_false, if_true]
    rw [cursor_offset_eq (show pre.size + 1 = pre.size + (0 + 1) by omega), r1]
    simp only
    rw [cursor_offset_eq (show pre.size + (0 + 1) + (Vlq.encodeUInt32 id).size =
      pre.size + (0 + 1 + (Vlq.encodeUInt32 id).size) by omega), r2]
    simp only [pure, Except.pure, ByteArray.size_append, bytes_size, List.size_toArray,
      List.length_cons, List.length_nil, uint32BE_size]
    congr 2
  case member key value =>
    obtain ⟨hkey, hvalue⟩ := hfit
    obtain ⟨first, rest, hhead, hfirst⟩ := encodeUInt32_head key hkey
    have hpeek : Cursor.readUInt8
        { data := pre ++ (Vlq.encodeUInt32 key ++ (value.encode ++ suffix)), offset := pre.size } =
        .ok (first,
          { data := pre ++ (Vlq.encodeUInt32 key ++ (value.encode ++ suffix)),
            offset := pre.size + 1 }) := by
      rw [hhead, ByteArray.append_assoc]
      exact Cursor.readUInt8_append_byte _ _ _
    have r2 := decodeSlot_value value hvalue (pre ++ Vlq.encodeUInt32 key) suffix
    simp only [ByteArray.append_assoc, ByteArray.size_append] at r2
    simp only [Item.top, Item.encode, ByteArray.append_assoc]
    unfold decodeItem
    rw [hpeek]
    simp only [bind, Except.bind, hfirst, if_false]
    rw [Vlq.decodeUInt32_encodeUInt32]
    simp only [show ¬ key = 0 from hkey, if_false]
    rw [r2]
    simp [pure, Except.pure, ByteArray.size_append]
    omega
  case memberStruct key structId =>
    have hkey : key ≠ 0 := hfit
    obtain ⟨first, rest, hhead, hfirst⟩ := encodeUInt32_head key hkey
    have hpeek : Cursor.readUInt8
        { data := pre ++ (Vlq.encodeUInt32 key ++ (structHeader structId ++ suffix)), offset := pre.size } =
        .ok (first,
          { data := pre ++ (Vlq.encodeUInt32 key ++ (structHeader structId ++ suffix)),
            offset := pre.size + 1 }) := by
      rw [hhead, ByteArray.append_assoc]
      exact Cursor.readUInt8_append_byte _ _ _
    have r2 := decodeSlot_struct structId (pre ++ Vlq.encodeUInt32 key) suffix
    simp only [ByteArray.append_assoc, ByteArray.size_append] at r2
    simp only [Item.top, Item.encode, ByteArray.append_assoc]
    unfold decodeItem
    rw [hpeek]
    simp only [bind, Except.bind, hfirst, if_false]
    rw [Vlq.decodeUInt32_encodeUInt32]
    simp only [show ¬ key = 0 from hkey, if_false]
    rw [r2]
    simp [pure, Except.pure, ByteArray.size_append, structHeader]
    omega

/-! ## Round trip of trees -/

/-- `items` is a well-nested continuation from `stack` that closes the outermost
    object exactly at its last item. -/
def Closes : List Frame → List Item → Prop
  | _, [] => False
  | stack, item :: rest =>
    match step stack item with
    | none => False
    | some [] => rest = []
    | some next => Closes next rest

theorem step_top (stack : List Frame) (item : Item) (next : List Frame)
    (h : step stack item = some next) : stack.headD .object = item.top := by
  cases stack with
  | nil => cases item <;> simp [step, Item.top] at h ⊢
  | cons frame rest =>
    cases frame <;> cases item <;> simp [step, Item.top] at h ⊢

theorem Item.encode_size_pos (item : Item) : 0 < item.encode.size := by
  cases item
  case member key value =>
    have := (Vlq.encodeUInt32_size key).1
    simp [Item.encode, ByteArray.size_append]
    omega
  case memberStruct key structId =>
    have := (Vlq.encodeUInt32_size key).1
    simp [Item.encode, ByteArray.size_append]
    omega
  all_goals (simp [Item.encode, ByteArray.size_append]; try omega)

theorem encodeItems_size_ge (items : List Item) : items.length ≤ (encodeItems items).size := by
  induction items with
  | nil => simp [encodeItems]
  | cons item rest ih =>
    have := item.encode_size_pos
    simp only [encodeItems, ByteArray.size_append, List.length_cons]
    omega

theorem decodeItems_encode (items : List Item) (stack : List Frame) (hcloses : Closes stack items)
    (hfits : ∀ item ∈ items, item.Fits) (fuel : Nat) (hfuel : items.length ≤ fuel)
    (pre suffix : ByteArray) :
    decodeItems fuel stack { data := pre ++ (encodeItems items ++ suffix), offset := pre.size } =
      .ok (items,
        { data := pre ++ (encodeItems items ++ suffix),
          offset := pre.size + (encodeItems items).size }) := by
  induction items generalizing stack fuel pre with
  | nil => exact absurd hcloses (by simp [Closes])
  | cons item rest ih =>
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    simp only [Closes] at hcloses
    split at hcloses
    · contradiction
    · rename_i hstep
      subst hcloses
      have htop := step_top _ _ _ hstep
      have hitem := decodeItem_encode item (hfits item (by simp)) pre suffix
      simp only [encodeItems, ByteArray.append_empty]
      rw [decodeItems, htop, hitem]
      simp only [bind, Except.bind, hstep, pure, Except.pure]
    · rename_i next hnext hstep
      have htop := step_top _ _ _ hstep
      have hitem := decodeItem_encode item (hfits item (by simp)) pre (encodeItems rest ++ suffix)
      have hrest := ih next hcloses (fun i hi => hfits i (by simp [hi])) fuel
        (by simp at hfuel; omega) (pre ++ item.encode)
      simp only [ByteArray.append_assoc, ByteArray.size_append] at hrest
      simp only [encodeItems, ByteArray.append_assoc]
      rw [decodeItems, htop, hitem]
      simp only [bind, Except.bind]
      split
      · rename_i h; rw [hstep] at h; contradiction
      · rename_i h; rw [hstep] at h; injection h with h; exact absurd (by simp_all) hnext
      · rename_i next' h
        rw [hstep] at h
        injection h with h
        subst h
        rw [hrest]
        simp only [pure, Except.pure, ByteArray.size_append, Nat.add_assoc]

/-- Decoding the encoding of a complete, well-nested object tree, inside arbitrary
    surrounding bytes, returns its items and consumes exactly its encoding. -/
theorem decodeTree_encode (items : List Item) (hcloses : Closes [] items)
    (hfits : ∀ item ∈ items, item.Fits) (pre suffix : ByteArray) :
    decodeTree { data := pre ++ (encodeItems items ++ suffix), offset := pre.size } =
      .ok (items,
        { data := pre ++ (encodeItems items ++ suffix),
          offset := pre.size + (encodeItems items).size }) := by
  unfold decodeTree
  apply decodeItems_encode items [] hcloses hfits
  have := encodeItems_size_ge items
  simp only [Cursor.remaining, ByteArray.size_append]
  omega

end LeanS7CommPlus
