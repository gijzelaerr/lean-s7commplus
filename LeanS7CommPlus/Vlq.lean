import LeanS7.Binary

/-!
# Variable-length quantities

S7CommPlus encodes integers as big-endian groups of seven bits. Every byte except
the last has its high bit set as a continuation flag.

The decoder follows the Python reference (`s7commplus/vlq.py`) where that is safe
and is stricter where it is not:

- like the Python decoder, it accepts **overlong encodings**: leading zero groups
  (`80 00` decodes to 0, as `00` does);
- unlike the Python decoder, it rejects a value that does not fit the type
  (Python's `decode_uint32_vlq` returns 2^35 - 1 for `ff ff ff ff 7f`) and a final
  byte that still has its continuation flag set (Python stops after five bytes
  and ignores the flag).
-/

namespace LeanS7CommPlus.Vlq

open LeanS7

/-- The seven-bit groups of a number, least significant first, with no leading zero
    groups. Zero has the single group `0`. -/
def groups (value : Nat) : List Nat :=
  if value < 128 then [value] else (value % 128) :: groups (value / 128)
termination_by value
decreasing_by omega

/-- Wire bytes of groups given most significant first: every byte but the last
    carries the continuation flag. -/
def encodeGroups : List Nat → List UInt8
  | [] => []
  | [group] => [UInt8.ofNat group]
  | group :: rest => UInt8.ofNat (group + 128) :: encodeGroups rest

/-- The minimal VLQ encoding of a natural number. -/
def encodeNat (value : Nat) : ByteArray :=
  (encodeGroups (groups value).reverse).toByteArray

def encodeUInt32 (value : UInt32) : ByteArray :=
  encodeNat value.toNat

/-- Read continuation-flagged groups, at most `limit` bytes, accumulating the value. -/
def readGroups : Nat → Nat → Cursor → Except DecodeError (Nat × Cursor)
  | 0, _, cursor => .error (.invalidField cursor.offset "VLQ continues past its maximum length")
  | limit + 1, accumulator, cursor => do
    let (byte, next) ← cursor.readUInt8
    let accumulator := accumulator * 128 + byte.toNat % 128
    if byte.toNat < 128 then pure (accumulator, next) else readGroups limit accumulator next

/-- Decode an unsigned 32-bit VLQ: at most five bytes, and a value below 2^32. -/
def decodeUInt32 (cursor : Cursor) : Except DecodeError (UInt32 × Cursor) := do
  let (value, next) ← readGroups 5 0 cursor
  if value < 2 ^ 32 then
    pure (UInt32.ofNat value, next)
  else
    throw (.invalidField cursor.offset "VLQ value exceeds 32 bits")

/-! ## Encoding -/

theorem groups_ne_nil (value : Nat) : groups value ≠ [] := by
  rw [groups]
  split <;> simp

theorem groups_lt (value : Nat) : ∀ group ∈ groups value, group < 128 := by
  induction value using Nat.strongRecOn with
  | _ value ih =>
    rw [groups]
    split
    · intro group h
      simp at h
      omega
    · intro group h
      simp only [List.mem_cons] at h
      rcases h with h | h
      · omega
      · exact ih (value / 128) (by omega) group h

/-- Reading the groups back, most significant first, gives the number. -/
theorem foldl_groups (value : Nat) :
    (groups value).reverse.foldl (fun accumulator group => accumulator * 128 + group) 0 = value := by
  induction value using Nat.strongRecOn with
  | _ value ih =>
    rw [groups]
    split
    · simp
    · simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih (value / 128) (by omega)]
      omega

theorem groups_length_le (value bound : Nat) (h : value < 128 ^ (bound + 1)) :
    (groups value).length ≤ bound + 1 := by
  induction bound generalizing value with
  | zero =>
    rw [groups]
    split
    · simp
    · simp at h; omega
  | succ bound ih =>
    rw [groups]
    split
    · simp
    · simp only [List.length_cons, Nat.add_le_add_iff_right]
      apply ih
      rw [Nat.pow_succ, Nat.mul_comm] at h
      exact Nat.div_lt_of_lt_mul h

theorem encodeGroups_length (gs : List Nat) : (encodeGroups gs).length = gs.length := by
  induction gs with
  | nil => rfl
  | cons group rest ih =>
    cases rest with
    | nil => rfl
    | cons next tail =>
      simp only [encodeGroups, List.length_cons] at ih ⊢
      omega

theorem encodeNat_size (value : Nat) : (encodeNat value).size = (groups value).length := by
  simp [encodeNat, encodeGroups_length]

/-- A 32-bit value encodes to one to five bytes. -/
theorem encodeUInt32_size (value : UInt32) :
    1 ≤ (encodeUInt32 value).size ∧ (encodeUInt32 value).size ≤ 5 := by
  rw [encodeUInt32, encodeNat_size]
  have hne := groups_ne_nil value.toNat
  have hlt := value.toNat_lt
  refine ⟨?_, groups_length_le _ 4 (by simpa using (show value.toNat < 2 ^ 35 by omega))⟩
  cases h : groups value.toNat with
  | nil => exact absurd h hne
  | cons _ _ => simp

/-! ## Round trip -/

/-- Reading the encoding of nonempty groups below 128, inside arbitrary surrounding
    bytes, consumes exactly those bytes and folds the groups into the accumulator. -/
theorem readGroups_encodeGroups (gs : List Nat) (hne : gs ≠ []) (hlt : ∀ group ∈ gs, group < 128)
    (limit accumulator : Nat) (hlimit : gs.length ≤ limit) (pre suffix : ByteArray) :
    readGroups limit accumulator
        { data := pre ++ ((encodeGroups gs).toByteArray ++ suffix), offset := pre.size } =
      .ok (gs.foldl (fun accumulator group => accumulator * 128 + group) accumulator,
        { data := pre ++ ((encodeGroups gs).toByteArray ++ suffix),
          offset := pre.size + gs.length }) := by
  induction gs generalizing limit accumulator pre with
  | nil => exact absurd rfl hne
  | cons group rest ih =>
    have hgroup := hlt group (by simp)
    obtain ⟨limit, rfl⟩ : ∃ smaller, limit = smaller + 1 := ⟨limit - 1, by simp at hlimit; omega⟩
    cases rest with
    | nil =>
      have hbyte : (UInt8.ofNat group).toNat = group := by
        rw [UInt8.toNat_ofNat']; omega
      simp only [encodeGroups, List.foldl_cons, List.foldl_nil, List.length_cons,
        List.length_nil]
      rw [readGroups, show [UInt8.ofNat group].toByteArray = bytes #[UInt8.ofNat group] from rfl,
        Cursor.readUInt8_append_byte]
      simp [bind, Except.bind, hbyte, show group < 128 from hgroup, Nat.mod_eq_of_lt hgroup,
        pure, Except.pure]
    | cons next tail =>
      have hbyte : (UInt8.ofNat (group + 128)).toNat = group + 128 := by
        rw [UInt8.toNat_ofNat']; omega
      have hrest : (encodeGroups (group :: next :: tail)).toByteArray =
          bytes #[UInt8.ofNat (group + 128)] ++ (encodeGroups (next :: tail)).toByteArray := by
        have hlist : encodeGroups (group :: next :: tail) =
            [UInt8.ofNat (group + 128)] ++ encodeGroups (next :: tail) := by
          simp [encodeGroups]
        rw [hlist, List.toByteArray_append]
        rfl
      rw [hrest, ByteArray.append_assoc, readGroups, Cursor.readUInt8_append_byte]
      simp only [bind, Except.bind, hbyte, show ¬ group + 128 < 128 by omega, if_false,
        show (group + 128) % 128 = group by omega]
      have h := ih (by simp) (fun g hg => hlt g (by simp [hg])) limit (accumulator * 128 + group)
        (by simp only [List.length_cons] at hlimit ⊢; omega) (pre ++ bytes #[UInt8.ofNat (group + 128)])
      simp only [ByteArray.size_append, bytes_size, List.size_toArray, List.length_cons,
        List.length_nil, ByteArray.append_assoc] at h
      rw [h]
      simp only [List.foldl_cons, List.length_cons]
      congr 2
      simp only [Cursor.mk.injEq, true_and]
      omega

/-- Decoding the encoding of any 32-bit value, inside arbitrary surrounding bytes,
    returns the value and consumes exactly its encoding. -/
theorem decodeUInt32_encodeUInt32 (value : UInt32) (pre suffix : ByteArray) :
    decodeUInt32 { data := pre ++ (encodeUInt32 value ++ suffix), offset := pre.size } =
      .ok (value,
        { data := pre ++ (encodeUInt32 value ++ suffix),
          offset := pre.size + (encodeUInt32 value).size }) := by
  have hsize := encodeUInt32_size value
  have hlt := value.toNat_lt
  have hread := readGroups_encodeGroups (groups value.toNat).reverse
    (by simpa using groups_ne_nil value.toNat)
    (fun g hg => groups_lt value.toNat g (by simpa using hg)) 5 0
    (by rw [List.length_reverse]; rw [encodeUInt32, encodeNat_size] at hsize; exact hsize.2)
    pre suffix
  rw [foldl_groups] at hread
  unfold decodeUInt32
  rw [show encodeUInt32 value = (encodeGroups (groups value.toNat).reverse).toByteArray from rfl]
  rw [hread]
  simp only [bind, Except.bind, show value.toNat < 2 ^ 32 from hlt, if_true, pure, Except.pure,
    UInt32.ofNat_toNat, List.length_reverse]
  rw [show (encodeGroups (groups value.toNat).reverse).toByteArray.size = (groups value.toNat).length by
    simp [encodeGroups_length]]


/-! ## Canonical form: the decoder accepts only leading zero groups beyond the minimal encoding -/

/-- The bytes `readGroups` consumes are exactly the wire encoding of the groups it read. -/
theorem readGroups_bytes (limit accumulator value : Nat) (cursor next : Cursor)
    (h : readGroups limit accumulator cursor = .ok (value, next)) :
    next.data = cursor.data ∧ ∃ gs : List Nat, gs ≠ [] ∧ (∀ group ∈ gs, group < 128) ∧
      gs.length ≤ limit ∧ next.offset = cursor.offset + gs.length ∧
      cursor.data.extract cursor.offset next.offset = (encodeGroups gs).toByteArray ∧
      value = gs.foldl (fun accumulator group => accumulator * 128 + group) accumulator := by
  induction limit generalizing accumulator cursor with
  | zero => simp [readGroups] at h
  | succ limit ih =>
    simp only [readGroups, bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i read byteCursor hread
      obtain ⟨hlt, hbyte, hnext⟩ := Cursor.readUInt8_value _ _ _ hread
      have hb := byteCursor.fst.toNat_lt
      split at h
      · rename_i hsmall
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by rw [hnext], [byteCursor.fst.toNat], by simp, by simpa using hsmall,
          by simp, by rw [hnext]; simp, ?_, by simp [Nat.mod_eq_of_lt hsmall]⟩
        rw [hnext]
        simp only [encodeGroups, UInt8.ofNat_toNat]
        rw [ByteArray.extract_one _ _ hlt, hbyte]
        rfl
      · rename_i hlarge
        obtain ⟨hdata, gs, hne, hgs, hlen, hoff, hext, hval⟩ := ih _ _ h
        rw [hnext] at hdata hoff hext
        simp only at hdata hoff hext
        refine ⟨hdata, (byteCursor.fst.toNat % 128) :: gs, by simp, ?_, by simp; omega,
          by simp; omega, ?_, by simp [hval]⟩
        · intro group hgroup
          simp only [List.mem_cons] at hgroup
          rcases hgroup with rfl | hgroup
          · omega
          · exact hgs group hgroup
        · obtain ⟨first, rest, rfl⟩ : ∃ first rest, gs = first :: rest := by
            cases gs with
            | nil => exact absurd rfl hne
            | cons first rest => exact ⟨first, rest, rfl⟩
          have hlist : encodeGroups (byteCursor.fst.toNat % 128 :: first :: rest) =
              [UInt8.ofNat (byteCursor.fst.toNat % 128 + 128)] ++ encodeGroups (first :: rest) := by
            simp [encodeGroups]
          have hfirst : UInt8.ofNat (byteCursor.fst.toNat % 128 + 128) = byteCursor.fst := by
            apply UInt8.toNat_inj.mp
            rw [UInt8.toNat_ofNat']
            omega
          rw [hlist, List.toByteArray_append, ← hext, hfirst, ← hbyte,
            show [cursor.data[cursor.offset]].toByteArray =
              cursor.data.extract cursor.offset (cursor.offset + 1) from
              (ByteArray.extract_one _ _ hlt).symm,
            ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]

/-- A list of seven-bit groups that reads as zero consists of zeros. -/
theorem foldl_eq_zero (gs : List Nat) (hlt : ∀ group ∈ gs, group < 128)
    (h : gs.foldl (fun accumulator group => accumulator * 128 + group) 0 = 0) :
    gs = List.replicate gs.length 0 := by
  obtain ⟨l, rfl⟩ : ∃ l : List Nat, gs = l.reverse := ⟨gs.reverse, by simp⟩
  induction l with
  | nil => rfl
  | cons last init ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at h hlt ⊢
    have hinit : init.reverse.foldl (fun accumulator group => accumulator * 128 + group) 0 = 0 := by
      omega
    have hlast : last = 0 := by omega
    rw [ih (fun g hg => hlt g (by simp [hg])) hinit, hlast]
    simp [List.replicate_succ']

/-- Any list of seven-bit groups is leading zero groups followed by the minimal groups
    of the number it reads as. -/
theorem groups_normal_form (gs : List Nat) (hne : gs ≠ []) (hlt : ∀ group ∈ gs, group < 128) :
    ∃ zeros, gs = List.replicate zeros 0 ++
      (groups (gs.foldl (fun accumulator group => accumulator * 128 + group) 0)).reverse := by
  obtain ⟨l, rfl⟩ : ∃ l : List Nat, gs = l.reverse := ⟨gs.reverse, by simp⟩
  induction l with
  | nil => exact absurd rfl hne
  | cons last init' ih =>
    simp only [List.reverse_cons] at hne hlt ⊢
    generalize hi : init'.reverse = init at ih hlt
    have hlast : last < 128 := hlt last (by simp)
    have hinit : ∀ group ∈ init, group < 128 := fun g hg => hlt g (by simp [hg])
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hw : init.foldl (fun accumulator group => accumulator * 128 + group) 0 = w
    by_cases hzero : w = 0
    · refine ⟨init.length, ?_⟩
      rw [hzero, Nat.zero_mul, Nat.zero_add, groups, if_pos hlast]
      rw [← foldl_eq_zero init hinit (by rw [hw, hzero])]
      simp
    · have hne' : init ≠ [] := by
        intro hnil
        simp [hnil] at hw
        omega
      obtain ⟨zeros, hz⟩ := ih hne' hinit
      refine ⟨zeros, ?_⟩
      rw [groups, if_neg (by omega), show (w * 128 + last) % 128 = last by omega,
        show (w * 128 + last) / 128 = w by omega]
      rw [hw] at hz
      rw [hz]
      simp

theorem encodeGroups_replicate_append (zeros : Nat) (gs : List Nat) (hne : gs ≠ []) :
    encodeGroups (List.replicate zeros 0 ++ gs) =
      List.replicate zeros (0x80 : UInt8) ++ encodeGroups gs := by
  induction zeros with
  | zero => simp
  | succ zeros ih =>
    rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append, ← ih]
    cases h : List.replicate zeros 0 ++ gs with
    | nil => simp at h; exact absurd h.2 hne
    | cons first rest => simp [encodeGroups]

/-- Canonical form of an unsigned 32-bit VLQ: the bytes the decoder accepts are the
    minimal encoding of the decoded value, preceded by zero or more `0x80` bytes (leading
    zero groups), and at most five bytes in all. -/
theorem decodeUInt32_canonical (cursor next : Cursor) (value : UInt32)
    (h : decodeUInt32 cursor = .ok (value, next)) :
    next.data = cursor.data ∧ next.offset ≤ cursor.offset + 5 ∧
      ∃ zeros, cursor.data.extract cursor.offset next.offset =
        (List.replicate zeros (0x80 : UInt8)).toByteArray ++ encodeUInt32 value := by
  simp only [decodeUInt32, bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i read result hread
    split at h
    · rename_i hrange
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hdata, gs, hne, hgs, hlen, hoff, hext, hval⟩ := readGroups_bytes _ _ _ _ _ hread
      refine ⟨hdata, by omega, ?_⟩
      obtain ⟨zeros, hz⟩ := groups_normal_form gs hne hgs
      refine ⟨zeros, ?_⟩
      rw [hext, hz, ← hval, encodeGroups_replicate_append _ _ (by
        simpa using groups_ne_nil result.fst), List.toByteArray_append]
      congr 1
      simp only [encodeUInt32, encodeNat, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hrange]
    · simp [throw, throwThe, MonadExceptOf.throw] at h


/-! ## Unsigned 64-bit

Eight seven-bit groups hold only 56 bits, so a 64-bit VLQ whose eighth group still
has its continuation flag set ends with a ninth byte that carries all eight bits.
The encoder uses the nine-byte form exactly for values of 2^56 and above: eight
continuation groups for the top 56 bits (padded with leading `0x80`), then the low
byte. -/

/-- Read continuation-flagged groups; after `limit` of them, one more byte that
    carries eight bits. -/
def readGroupsThenByte : Nat → Nat → Cursor → Except DecodeError (Nat × Cursor)
  | 0, accumulator, cursor => do
    let (byte, next) ← cursor.readUInt8
    pure (accumulator * 256 + byte.toNat, next)
  | limit + 1, accumulator, cursor => do
    let (byte, next) ← cursor.readUInt8
    let accumulator := accumulator * 128 + byte.toNat % 128
    if byte.toNat < 128 then pure (accumulator, next)
    else readGroupsThenByte limit accumulator next

def encodeUInt64 (value : UInt64) : ByteArray :=
  if value.toNat < 2 ^ 56 then
    encodeNat value.toNat
  else
    let high := (groups (value.toNat / 256)).reverse
    (List.replicate (8 - high.length) (0x80 : UInt8) ++
      high.map (fun group => UInt8.ofNat (group + 128)) ++
      [UInt8.ofNat (value.toNat % 256)]).toByteArray

/-- Decode an unsigned 64-bit VLQ: at most eight seven-bit groups, then a full byte. -/
def decodeUInt64 (cursor : Cursor) : Except DecodeError (UInt64 × Cursor) := do
  let (value, next) ← readGroupsThenByte 8 0 cursor
  if value < 2 ^ 64 then
    pure (UInt64.ofNat value, next)
  else
    throw (.invalidField cursor.offset "VLQ value exceeds 64 bits")

theorem readGroupsThenByte_encodeGroups (gs : List Nat) (hne : gs ≠ [])
    (hlt : ∀ group ∈ gs, group < 128) (limit accumulator : Nat) (hlimit : gs.length ≤ limit)
    (pre suffix : ByteArray) :
    readGroupsThenByte limit accumulator
        { data := pre ++ ((encodeGroups gs).toByteArray ++ suffix), offset := pre.size } =
      .ok (gs.foldl (fun accumulator group => accumulator * 128 + group) accumulator,
        { data := pre ++ ((encodeGroups gs).toByteArray ++ suffix),
          offset := pre.size + gs.length }) := by
  induction gs generalizing limit accumulator pre with
  | nil => exact absurd rfl hne
  | cons group rest ih =>
    have hgroup := hlt group (by simp)
    obtain ⟨limit, rfl⟩ : ∃ smaller, limit = smaller + 1 := ⟨limit - 1, by simp at hlimit; omega⟩
    cases rest with
    | nil =>
      have hbyte : (UInt8.ofNat group).toNat = group := by
        rw [UInt8.toNat_ofNat']; omega
      simp only [encodeGroups, List.foldl_cons, List.foldl_nil, List.length_cons,
        List.length_nil]
      rw [readGroupsThenByte, show [UInt8.ofNat group].toByteArray = bytes #[UInt8.ofNat group] from rfl,
        Cursor.readUInt8_append_byte]
      simp [bind, Except.bind, hbyte, show group < 128 from hgroup, Nat.mod_eq_of_lt hgroup,
        pure, Except.pure]
    | cons next tail =>
      have hbyte : (UInt8.ofNat (group + 128)).toNat = group + 128 := by
        rw [UInt8.toNat_ofNat']; omega
      have hrest : (encodeGroups (group :: next :: tail)).toByteArray =
          bytes #[UInt8.ofNat (group + 128)] ++ (encodeGroups (next :: tail)).toByteArray := by
        have hlist : encodeGroups (group :: next :: tail) =
            [UInt8.ofNat (group + 128)] ++ encodeGroups (next :: tail) := by
          simp [encodeGroups]
        rw [hlist, List.toByteArray_append]
        rfl
      rw [hrest, ByteArray.append_assoc, readGroupsThenByte, Cursor.readUInt8_append_byte]
      simp only [bind, Except.bind, hbyte, show ¬ group + 128 < 128 by omega, if_false,
        show (group + 128) % 128 = group by omega]
      have h := ih (by simp) (fun g hg => hlt g (by simp [hg])) limit (accumulator * 128 + group)
        (by simp only [List.length_cons] at hlimit ⊢; omega) (pre ++ bytes #[UInt8.ofNat (group + 128)])
      simp only [ByteArray.size_append, bytes_size, List.size_toArray, List.length_cons,
        List.length_nil, ByteArray.append_assoc] at h
      rw [h]
      simp only [List.foldl_cons, List.length_cons]
      congr 2
      simp only [Cursor.mk.injEq, true_and]
      omega

/-- Reading `limit` continuation groups and then a full byte. -/
theorem readGroupsThenByte_continued (gs : List Nat) (hlt : ∀ group ∈ gs, group < 128)
    (accumulator : Nat) (last : UInt8) (pre suffix : ByteArray) :
    readGroupsThenByte gs.length accumulator
        { data := pre ++ ((gs.map (fun group => UInt8.ofNat (group + 128)) ++ [last]).toByteArray ++
            suffix), offset := pre.size } =
      .ok (gs.foldl (fun accumulator group => accumulator * 128 + group) accumulator * 256 +
          last.toNat,
        { data := pre ++ ((gs.map (fun group => UInt8.ofNat (group + 128)) ++ [last]).toByteArray ++
            suffix), offset := pre.size + gs.length + 1 }) := by
  induction gs generalizing accumulator pre with
  | nil =>
    simp only [List.map_nil, List.nil_append, List.length_nil, List.foldl_nil, Nat.add_zero]
    rw [readGroupsThenByte, show [last].toByteArray = bytes #[last] from rfl,
      Cursor.readUInt8_append_byte]
    rfl
  | cons group rest ih =>
    have hgroup := hlt group (by simp)
    have hbyte : (UInt8.ofNat (group + 128)).toNat = group + 128 := by
      rw [UInt8.toNat_ofNat']; omega
    have hsplit : (List.map (fun group => UInt8.ofNat (group + 128)) (group :: rest) ++ [last]).toByteArray =
        bytes #[UInt8.ofNat (group + 128)] ++
          (List.map (fun group => UInt8.ofNat (group + 128)) rest ++ [last]).toByteArray := by
      rw [List.map_cons, List.cons_append, show UInt8.ofNat (group + 128) ::
        (List.map (fun group => UInt8.ofNat (group + 128)) rest ++ [last]) =
        [UInt8.ofNat (group + 128)] ++ (List.map (fun group => UInt8.ofNat (group + 128)) rest ++ [last])
        from rfl, List.toByteArray_append]
      rfl
    rw [hsplit, ByteArray.append_assoc, List.length_cons, readGroupsThenByte,
      Cursor.readUInt8_append_byte]
    simp only [bind, Except.bind, hbyte, show ¬ group + 128 < 128 by omega, if_false,
      show (group + 128) % 128 = group by omega]
    have h := ih (fun g hg => hlt g (by simp [hg])) (accumulator * 128 + group)
      (pre ++ bytes #[UInt8.ofNat (group + 128)])
    simp only [ByteArray.size_append, bytes_size, List.size_toArray, List.length_cons,
      List.length_nil, ByteArray.append_assoc] at h
    rw [h]
    simp only [List.foldl_cons]
    congr 2
    simp only [Cursor.mk.injEq, true_and]
    omega

theorem foldl_replicate_zero (zeros : Nat) (gs : List Nat) :
    (List.replicate zeros 0 ++ gs).foldl (fun accumulator group => accumulator * 128 + group) 0 =
      gs.foldl (fun accumulator group => accumulator * 128 + group) 0 := by
  induction zeros with
  | zero => simp
  | succ zeros ih => simp [List.replicate_succ, ih]

/-- A 64-bit value encodes to one to nine bytes. -/
theorem encodeUInt64_size (value : UInt64) :
    1 ≤ (encodeUInt64 value).size ∧ (encodeUInt64 value).size ≤ 9 := by
  unfold encodeUInt64
  split
  · rename_i hsmall
    rw [encodeNat_size]
    have hne := groups_ne_nil value.toNat
    refine ⟨?_, ?_⟩
    · cases h : groups value.toNat with
      | nil => exact absurd h hne
      | cons _ _ => simp
    · have := groups_length_le value.toNat 7 (by simpa using (show value.toNat < 2 ^ 56 from hsmall))
      omega
  · rename_i hlarge
    have hlt := value.toNat_lt
    have hhigh := groups_length_le (value.toNat / 256) 7 (by
      show value.toNat / 256 < 128 ^ 8
      omega)
    simp only [List.size_toByteArray, List.length_append, List.length_replicate, List.length_map,
      List.length_reverse, List.length_cons, List.length_nil]
    omega

/-- Decoding the encoding of any 64-bit value, inside arbitrary surrounding bytes,
    returns the value and consumes exactly its encoding. -/
theorem decodeUInt64_encodeUInt64 (value : UInt64) (pre suffix : ByteArray) :
    decodeUInt64 { data := pre ++ (encodeUInt64 value ++ suffix), offset := pre.size } =
      .ok (value,
        { data := pre ++ (encodeUInt64 value ++ suffix),
          offset := pre.size + (encodeUInt64 value).size }) := by
  have hlt := value.toNat_lt
  unfold decodeUInt64
  by_cases hsmall : value.toNat < 2 ^ 56
  · have hlen := groups_length_le value.toNat 7 (by simpa using hsmall)
    have hread := readGroupsThenByte_encodeGroups (groups value.toNat).reverse
      (by simpa using groups_ne_nil value.toNat)
      (fun g hg => groups_lt value.toNat g (by simpa using hg)) 8 0
      (by rw [List.length_reverse]; omega) pre suffix
    rw [foldl_groups] at hread
    have henc : encodeUInt64 value = (encodeGroups (groups value.toNat).reverse).toByteArray := by
      simp [encodeUInt64, hsmall, encodeNat]
    rw [henc, hread]
    simp only [bind, Except.bind, show value.toNat < 2 ^ 64 from hlt, if_true, pure, Except.pure,
      UInt64.ofNat_toNat, List.length_reverse]
    simp [encodeGroups_length]
  · have hhigh := groups_length_le (value.toNat / 256) 7 (by
      show value.toNat / 256 < 128 ^ 8
      omega)
    let high := (groups (value.toNat / 256)).reverse
    let padded := List.replicate (8 - high.length) 0 ++ high
    have hpadded : padded.length = 8 := by
      simp only [padded, high, List.length_append, List.length_replicate, List.length_reverse]
      omega
    have hpadlt : ∀ group ∈ padded, group < 128 := by
      intro g hg
      simp only [padded, high, List.mem_append, List.mem_replicate, List.mem_reverse] at hg
      rcases hg with ⟨_, rfl⟩ | hg
      · omega
      · exact groups_lt _ g hg
    have henc : encodeUInt64 value =
        (padded.map (fun group => UInt8.ofNat (group + 128)) ++
          [UInt8.ofNat (value.toNat % 256)]).toByteArray := by
      simp only [encodeUInt64, hsmall, if_false, padded, high, List.map_append, List.map_replicate]
      rfl
    have hread := readGroupsThenByte_continued padded hpadlt 0 (UInt8.ofNat (value.toNat % 256))
      pre suffix
    rw [hpadded, foldl_replicate_zero, foldl_groups] at hread
    have hvalue : value.toNat / 256 * 256 + (UInt8.ofNat (value.toNat % 256)).toNat = value.toNat := by
      rw [UInt8.toNat_ofNat']
      omega
    rw [henc, hread, hvalue]
    simp only [bind, Except.bind, show value.toNat < 2 ^ 64 from hlt, if_true, pure, Except.pure,
      UInt64.ofNat_toNat]
    simp [hpadded]

/-! ## Canonical form of the 64-bit VLQ

An unsigned 64-bit VLQ has two forms. The short form is one to eight groups, the last
without a continuation flag; as for 32 bits, its only freedom is leading `0x80` groups.
The long form is eight continuation groups and a ninth byte that carries all eight bits.
The encoder uses it from 2^56 up, but the decoder accepts it for every value, and so
does the Python reference: `80 80 80 80 80 80 80 80 05` decodes to 5. -/

/-- The minimal encoding preceded by `zeros` leading zero groups (`0x80` bytes). -/
def encodeNatPadded (zeros value : Nat) : ByteArray :=
  (List.replicate zeros (0x80 : UInt8)).toByteArray ++ encodeNat value

/-- The nine-byte form: eight continuation groups for the top 56 bits, padded with
    `0x80`, then the low byte. -/
def encodeUInt64Long (value : UInt64) : ByteArray :=
  let high := (groups (value.toNat / 256)).reverse
  (List.replicate (8 - high.length) (0x80 : UInt8) ++
    high.map (fun group => UInt8.ofNat (group + 128)) ++
    [UInt8.ofNat (value.toNat % 256)]).toByteArray

/-- The encoder's long form is `encodeUInt64Long`. -/
theorem encodeUInt64_of_le (value : UInt64) (h : 2 ^ 56 ≤ value.toNat) :
    encodeUInt64 value = encodeUInt64Long value := by
  simp [encodeUInt64, encodeUInt64Long, show ¬ value.toNat < 2 ^ 56 by omega]

theorem foldl_lt (gs : List Nat) (hlt : ∀ group ∈ gs, group < 128) :
    gs.foldl (fun accumulator group => accumulator * 128 + group) 0 < 128 ^ gs.length := by
  obtain ⟨l, rfl⟩ : ∃ l : List Nat, gs = l.reverse := ⟨gs.reverse, by simp⟩
  induction l with
  | nil => simp
  | cons last init ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_reverse, List.length_cons, List.length_nil] at hlt ⊢
    have hl := hlt last (by simp)
    have hi := ih (fun g hg => hlt g (by simp [hg]))
    rw [List.length_reverse] at hi
    rw [Nat.pow_succ]
    generalize 128 ^ init.length = power at hi ⊢
    generalize init.reverse.foldl (fun accumulator group => accumulator * 128 + group) 0 = folded at hi ⊢
    have : (folded + 1) * 128 ≤ power * 128 := Nat.mul_le_mul_right 128 hi
    omega

/-- The bytes `readGroupsThenByte` consumes: either one to `limit` groups, the last
    without a continuation flag, or `limit` continuation groups and a full byte. -/
theorem readGroupsThenByte_bytes (limit accumulator value : Nat) (cursor next : Cursor)
    (h : readGroupsThenByte limit accumulator cursor = .ok (value, next)) :
    next.data = cursor.data ∧
      ((∃ gs : List Nat, gs ≠ [] ∧ (∀ group ∈ gs, group < 128) ∧
          gs.length ≤ limit ∧ next.offset = cursor.offset + gs.length ∧
          cursor.data.extract cursor.offset next.offset = (encodeGroups gs).toByteArray ∧
          value = gs.foldl (fun accumulator group => accumulator * 128 + group) accumulator) ∨
        (∃ (gs : List Nat) (last : UInt8), (∀ group ∈ gs, group < 128) ∧
          gs.length = limit ∧ next.offset = cursor.offset + limit + 1 ∧
          cursor.data.extract cursor.offset next.offset =
            (gs.map (fun group => UInt8.ofNat (group + 128)) ++ [last]).toByteArray ∧
          value = gs.foldl (fun accumulator group => accumulator * 128 + group) accumulator * 256 +
            last.toNat)) := by
  induction limit generalizing accumulator cursor with
  | zero =>
    simp only [readGroupsThenByte, bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i read byteCursor hread
      obtain ⟨hlt, hbyte, hnext⟩ := Cursor.readUInt8_value _ _ _ hread
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by rw [hnext], Or.inr ⟨[], byteCursor.fst, by simp, rfl, by simp [hnext], ?_,
        by simp⟩⟩
      rw [hnext]
      simp only [List.map_nil, List.nil_append]
      rw [ByteArray.extract_one _ _ hlt, hbyte]
      rfl
  | succ limit ih =>
    simp only [readGroupsThenByte, bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i read byteCursor hread
      obtain ⟨hlt, hbyte, hnext⟩ := Cursor.readUInt8_value _ _ _ hread
      have hb := byteCursor.fst.toNat_lt
      split at h
      · rename_i hsmall
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by rw [hnext], Or.inl ⟨[byteCursor.fst.toNat], by simp, by simpa using hsmall,
          by simp, by rw [hnext]; simp, ?_, by simp [Nat.mod_eq_of_lt hsmall]⟩⟩
        rw [hnext]
        simp only [encodeGroups, UInt8.ofNat_toNat]
        rw [ByteArray.extract_one _ _ hlt, hbyte]
        rfl
      · rename_i hlarge
        obtain ⟨hdata, hcases⟩ := ih _ _ h
        rw [hnext] at hdata
        simp only at hdata
        have hfirst : UInt8.ofNat (byteCursor.fst.toNat % 128 + 128) = byteCursor.fst := by
          apply UInt8.toNat_inj.mp
          rw [UInt8.toNat_ofNat']
          omega
        have hhead : [cursor.data[cursor.offset]].toByteArray =
            cursor.data.extract cursor.offset (cursor.offset + 1) :=
          (ByteArray.extract_one _ _ hlt).symm
        have hmem : ∀ gs : List Nat, (∀ group ∈ gs, group < 128) →
            ∀ group ∈ byteCursor.fst.toNat % 128 :: gs, group < 128 := by
          intro gs hgs group hgroup
          simp only [List.mem_cons] at hgroup
          rcases hgroup with rfl | hgroup
          · omega
          · exact hgs group hgroup
        refine ⟨hdata, ?_⟩
        rcases hcases with ⟨gs, hne, hgs, hlen, hoff, hext, hval⟩ |
            ⟨gs, last, hgs, hlen, hoff, hext, hval⟩
        · rw [hnext] at hoff hext
          simp only at hoff hext
          refine Or.inl ⟨(byteCursor.fst.toNat % 128) :: gs, by simp, hmem gs hgs,
            by simp; omega, by simp; omega, ?_, by simp [hval]⟩
          obtain ⟨first, rest, rfl⟩ : ∃ first rest, gs = first :: rest := by
            cases gs with
            | nil => exact absurd rfl hne
            | cons first rest => exact ⟨first, rest, rfl⟩
          have hlist : encodeGroups (byteCursor.fst.toNat % 128 :: first :: rest) =
              [UInt8.ofNat (byteCursor.fst.toNat % 128 + 128)] ++ encodeGroups (first :: rest) := by
            simp [encodeGroups]
          rw [hlist, List.toByteArray_append, ← hext, hfirst, ← hbyte, hhead,
            ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]
        · rw [hnext] at hoff hext
          simp only at hoff hext
          refine Or.inr ⟨(byteCursor.fst.toNat % 128) :: gs, last, hmem gs hgs, by simp [hlen],
            by omega, ?_, by simp [hval]⟩
          have hlist : List.map (fun group => UInt8.ofNat (group + 128))
                (byteCursor.fst.toNat % 128 :: gs) ++ [last] =
              [UInt8.ofNat (byteCursor.fst.toNat % 128 + 128)] ++
                (gs.map (fun group => UInt8.ofNat (group + 128)) ++ [last]) := by
            simp
          rw [hlist, List.toByteArray_append, ← hext, hfirst, ← hbyte, hhead,
            ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]

/-- Canonical form of an unsigned 64-bit VLQ. The bytes the decoder accepts are either
    the short form, the minimal encoding preceded by leading `0x80` groups, or the long
    nine-byte form `encodeUInt64Long`. Nothing else. -/
theorem decodeUInt64_canonical (cursor next : Cursor) (value : UInt64)
    (h : decodeUInt64 cursor = .ok (value, next)) :
    next.data = cursor.data ∧ next.offset ≤ cursor.offset + 9 ∧
      ((∃ zeros, cursor.data.extract cursor.offset next.offset =
          encodeNatPadded zeros value.toNat) ∨
        cursor.data.extract cursor.offset next.offset = encodeUInt64Long value) := by
  simp only [decodeUInt64, bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i read result hread
    split at h
    · rename_i hrange
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hval64 : (UInt64.ofNat result.fst).toNat = result.fst := by
        rw [UInt64.toNat_ofNat']
        exact Nat.mod_eq_of_lt hrange
      obtain ⟨hdata, hcases⟩ := readGroupsThenByte_bytes _ _ _ _ _ hread
      refine ⟨hdata, ?_, ?_⟩
      · rcases hcases with ⟨gs, _, _, hlen, hoff, _, _⟩ | ⟨gs, last, _, hlen, hoff, _, _⟩ <;>
          omega
      · rcases hcases with ⟨gs, hne, hgs, hlen, hoff, hext, hval⟩ |
            ⟨gs, last, hgs, hlen, hoff, hext, hval⟩
        · left
          obtain ⟨zeros, hz⟩ := groups_normal_form gs hne hgs
          refine ⟨zeros, ?_⟩
          rw [hext, hz, ← hval, encodeGroups_replicate_append _ _ (by
            simpa using groups_ne_nil result.fst), List.toByteArray_append, hval64]
          rfl
        · right
          have hlast := last.toNat_lt
          have hne : gs ≠ [] := by
            intro hnil
            simp [hnil] at hlen
          obtain ⟨zeros, hz⟩ := groups_normal_form gs hne hgs
          have hdiv : result.fst / 256 =
              gs.foldl (fun accumulator group => accumulator * 128 + group) 0 := by
            rw [hval]; omega
          have hmod : result.fst % 256 = last.toNat := by
            rw [hval]; omega
          have hzeros : 8 - (groups (result.fst / 256)).reverse.length = zeros := by
            have := congrArg List.length hz
            simp only [List.length_append, List.length_replicate, List.length_reverse] at this
            rw [List.length_reverse, hdiv]
            omega
          have hgs : gs.map (fun group => UInt8.ofNat (group + 128)) =
              List.replicate zeros (0x80 : UInt8) ++
                (groups (result.fst / 256)).reverse.map (fun group => UInt8.ofNat (group + 128)) := by
            conv => lhs; rw [hz]
            rw [hdiv, List.map_append, List.map_replicate]
            rfl
          rw [hext, encodeUInt64Long]
          simp only [hval64]
          rw [hzeros, hmod, UInt8.ofNat_toNat, hgs]
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The decoder accepts the short form with leading zero groups, up to eight groups. -/
theorem decodeUInt64_encodeNatPadded (zeros : Nat) (value : UInt64)
    (hfit : zeros + (groups value.toNat).length ≤ 8) (pre suffix : ByteArray) :
    decodeUInt64 { data := pre ++ (encodeNatPadded zeros value.toNat ++ suffix), offset := pre.size } =
      .ok (value,
        { data := pre ++ (encodeNatPadded zeros value.toNat ++ suffix),
          offset := pre.size + (encodeNatPadded zeros value.toNat).size }) := by
  have hlt := value.toNat_lt
  have hne := groups_ne_nil value.toNat
  have hpadded : encodeNatPadded zeros value.toNat =
      (encodeGroups (List.replicate zeros 0 ++ (groups value.toNat).reverse)).toByteArray := by
    rw [encodeGroups_replicate_append _ _ (by simpa using hne), List.toByteArray_append]
    rfl
  have hread := readGroupsThenByte_encodeGroups (List.replicate zeros 0 ++ (groups value.toNat).reverse)
    (by simp [hne])
    (by
      intro g hg
      simp only [List.mem_append, List.mem_replicate, List.mem_reverse] at hg
      rcases hg with ⟨_, rfl⟩ | hg
      · omega
      · exact groups_lt _ g hg)
    8 0 (by simp; omega) pre suffix
  rw [foldl_replicate_zero, foldl_groups] at hread
  unfold decodeUInt64
  rw [hpadded, hread]
  simp only [bind, Except.bind, show value.toNat < 2 ^ 64 from hlt, if_true, pure, Except.pure,
    UInt64.ofNat_toNat]
  simp [encodeGroups_length]

/-- The decoder accepts the long form of every value, not only from 2^56 up. -/
theorem decodeUInt64_encodeUInt64Long (value : UInt64) (pre suffix : ByteArray) :
    decodeUInt64 { data := pre ++ (encodeUInt64Long value ++ suffix), offset := pre.size } =
      .ok (value,
        { data := pre ++ (encodeUInt64Long value ++ suffix),
          offset := pre.size + (encodeUInt64Long value).size }) := by
  have hlt := value.toNat_lt
  unfold decodeUInt64
  have hhigh := groups_length_le (value.toNat / 256) 7 (by
    show value.toNat / 256 < 128 ^ 8
    omega)
  let high := (groups (value.toNat / 256)).reverse
  let padded := List.replicate (8 - high.length) 0 ++ high
  have hpadded : padded.length = 8 := by
    simp only [padded, high, List.length_append, List.length_replicate, List.length_reverse]
    omega
  have hpadlt : ∀ group ∈ padded, group < 128 := by
    intro g hg
    simp only [padded, high, List.mem_append, List.mem_replicate, List.mem_reverse] at hg
    rcases hg with ⟨_, rfl⟩ | hg
    · omega
    · exact groups_lt _ g hg
  have henc : encodeUInt64Long value =
      (padded.map (fun group => UInt8.ofNat (group + 128)) ++
        [UInt8.ofNat (value.toNat % 256)]).toByteArray := by
    simp only [encodeUInt64Long, padded, high, List.map_append, List.map_replicate]
    rfl
  have hread := readGroupsThenByte_continued padded hpadlt 0 (UInt8.ofNat (value.toNat % 256))
    pre suffix
  rw [hpadded, foldl_replicate_zero, foldl_groups] at hread
  have hvalue : value.toNat / 256 * 256 + (UInt8.ofNat (value.toNat % 256)).toNat = value.toNat := by
    rw [UInt8.toNat_ofNat']
    omega
  rw [henc, hread, hvalue]
  simp only [bind, Except.bind, show value.toNat < 2 ^ 64 from hlt, if_true, pure, Except.pure,
    UInt64.ofNat_toNat]
  simp [hpadded]

/-- The decoder accepts the 32-bit short form with leading zero groups, up to five
    groups. With `decodeUInt32_canonical`, this is exactly what it accepts. -/
theorem decodeUInt32_encodeNatPadded (zeros : Nat) (value : UInt32)
    (hfit : zeros + (groups value.toNat).length ≤ 5) (pre suffix : ByteArray) :
    decodeUInt32 { data := pre ++ (encodeNatPadded zeros value.toNat ++ suffix), offset := pre.size } =
      .ok (value,
        { data := pre ++ (encodeNatPadded zeros value.toNat ++ suffix),
          offset := pre.size + (encodeNatPadded zeros value.toNat).size }) := by
  have hlt := value.toNat_lt
  have hne := groups_ne_nil value.toNat
  have hpadded : encodeNatPadded zeros value.toNat =
      (encodeGroups (List.replicate zeros 0 ++ (groups value.toNat).reverse)).toByteArray := by
    rw [encodeGroups_replicate_append _ _ (by simpa using hne), List.toByteArray_append]
    rfl
  have hread := readGroups_encodeGroups (List.replicate zeros 0 ++ (groups value.toNat).reverse)
    (by simp [hne])
    (by
      intro g hg
      simp only [List.mem_append, List.mem_replicate, List.mem_reverse] at hg
      rcases hg with ⟨_, rfl⟩ | hg
      · omega
      · exact groups_lt _ g hg)
    5 0 (by simp; omega) pre suffix
  rw [foldl_replicate_zero, foldl_groups] at hread
  unfold decodeUInt32
  rw [hpadded, hread]
  simp only [bind, Except.bind, show value.toNat < 2 ^ 32 from hlt, if_true, pure, Except.pure,
    UInt32.ofNat_toNat]
  simp [encodeGroups_length]

end LeanS7CommPlus.Vlq
