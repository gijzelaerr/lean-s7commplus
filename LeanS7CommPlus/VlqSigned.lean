import LeanS7CommPlus.Vlq

/-!
# Signed variable-length quantities

A signed VLQ of `n` groups is the `7n`-bit two's-complement value of its groups;
bit 6 of the first byte is the sign. The 64-bit form ends, like the unsigned one,
with a full ninth byte when eight groups still continue; it then holds a 64-bit
two's-complement value.

The encoders reproduce the Python reference (`s7commplus/vlq.py`) byte for byte.
Python chooses the number of groups from the absolute value, so it is not always
minimal: it encodes -64 as `ff 40`, although `40` alone decodes to -64. Both decode
to the same value here and in Python.

The decoders reject values outside the type's range, which the Python decoders
return (`decode_int32_vlq` gives 4294967295 for `8f ff ff ff 7f`).
-/

namespace LeanS7CommPlus.Vlq

open LeanS7

/-- Exactly `count` seven-bit groups of a number, least significant first. -/
def groupsN : Nat → Nat → List Nat
  | 0, _ => []
  | count + 1, value => value % 128 :: groupsN count (value / 128)

/-- The number of groups the Python encoder uses for a magnitude: one, plus one for
    every further group while the remaining magnitude is at least 64, up to
    `extra` further groups. -/
def signedCount : Nat → Nat → Nat
  | 0, _ => 1
  | extra + 1, magnitude => if magnitude ≥ 64 then signedCount extra (magnitude / 128) + 1 else 1

/-- Two's-complement interpretation of a `width`-bit pattern. -/
def signedOf (unsigned width : Nat) : Int :=
  if 2 * unsigned ≥ width then (unsigned : Int) - width else unsigned

/-- The bytes of `count` groups of the two's-complement pattern of `value`. -/
def encodeSignedGroups (count : Nat) (value : Int) : ByteArray :=
  (encodeGroups (groupsN count (value % (128 ^ count : Nat)).toNat).reverse).toByteArray

def encodeInt32 (value : Int32) : ByteArray :=
  encodeSignedGroups (signedCount 4 value.toInt.natAbs) value.toInt

/-- Decode a signed 32-bit VLQ: at most five bytes, and a value in the int32 range. -/
def decodeInt32 (cursor : Cursor) : Except DecodeError (Int32 × Cursor) := do
  let (unsigned, next) ← readGroups 5 0 cursor
  let value := signedOf unsigned (128 ^ (next.offset - cursor.offset))
  if -2 ^ 31 ≤ value ∧ value < 2 ^ 31 then
    pure (Int32.ofInt value, next)
  else
    throw (.invalidField cursor.offset "VLQ value is outside the int32 range")

def encodeInt64 (value : Int64) : ByteArray :=
  let magnitude := value.toInt.natAbs
  if magnitude < 2 ^ 55 then
    encodeSignedGroups (signedCount 7 magnitude) value.toInt
  else
    let pattern := (value.toInt % (2 ^ 64 : Nat)).toNat
    ((groupsN 8 (pattern / 256)).reverse.map (fun group => UInt8.ofNat (group + 128)) ++
      [UInt8.ofNat (pattern % 256)]).toByteArray

/-- Decode a signed 64-bit VLQ: at most eight groups, then a full byte. -/
def decodeInt64 (cursor : Cursor) : Except DecodeError (Int64 × Cursor) := do
  let (unsigned, next) ← readGroupsThenByte 8 0 cursor
  let consumed := next.offset - cursor.offset
  let width := if consumed = 9 then 2 ^ 64 else 128 ^ consumed
  let value := signedOf unsigned width
  if -2 ^ 63 ≤ value ∧ value < 2 ^ 63 then
    pure (Int64.ofInt value, next)
  else
    throw (.invalidField cursor.offset "VLQ value is outside the int64 range")

/-! ## Group lemmas -/

theorem groupsN_length (count value : Nat) : (groupsN count value).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp [groupsN, ih]

theorem groupsN_lt (count value : Nat) : ∀ group ∈ groupsN count value, group < 128 := by
  induction count generalizing value with
  | zero => simp [groupsN]
  | succ count ih =>
    intro group h
    simp only [groupsN, List.mem_cons] at h
    rcases h with rfl | h
    · omega
    · exact ih _ group h

theorem foldl_groupsN (count value : Nat) :
    (groupsN count value).reverse.foldl (fun accumulator group => accumulator * 128 + group) 0 =
      value % 128 ^ count := by
  induction count generalizing value with
  | zero => simp [groupsN, Nat.mod_one]
  | succ count ih =>
    simp only [groupsN, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    rw [Nat.pow_succ, Nat.mul_comm (128 ^ count) 128, Nat.mod_mul]
    omega

theorem signedCount_pos (extra magnitude : Nat) : 1 ≤ signedCount extra magnitude := by
  cases extra with
  | zero => simp [signedCount]
  | succ extra => simp only [signedCount]; split <;> omega

theorem signedCount_le (extra magnitude : Nat) : signedCount extra magnitude ≤ extra + 1 := by
  induction extra generalizing magnitude with
  | zero => simp [signedCount]
  | succ extra ih =>
    simp only [signedCount]
    split
    · have := ih (magnitude / 128); omega
    · omega

/-- The magnitude fits the chosen number of groups with room for the sign. -/
theorem signedCount_bound (extra magnitude : Nat) (h : magnitude < 64 * 128 ^ extra) :
    magnitude < 64 * 128 ^ (signedCount extra magnitude - 1) := by
  induction extra generalizing magnitude with
  | zero => simpa [signedCount] using h
  | succ extra ih =>
    simp only [signedCount]
    split
    · rw [Nat.pow_succ] at h
      have hdiv : magnitude / 128 < 64 * 128 ^ extra := by
        generalize 128 ^ extra = power at h ⊢
        omega
      have hrec := ih (magnitude / 128) hdiv
      have hpos := signedCount_pos extra (magnitude / 128)
      rw [show signedCount extra (magnitude / 128) + 1 - 1 =
        (signedCount extra (magnitude / 128) - 1) + 1 by omega, Nat.pow_succ]
      generalize 128 ^ (signedCount extra (magnitude / 128) - 1) = power at hrec ⊢
      omega
    · simp
      omega

/-- Reading back `count` groups of the two's-complement pattern of a value whose
    magnitude leaves room for the sign recovers the value. -/
theorem signedOf_pattern (count : Nat) (value : Int)
    (h : value.natAbs < 64 * 128 ^ (count - 1)) (hcount : 1 ≤ count) :
    signedOf (value % (128 ^ count : Nat)).toNat (128 ^ count) = value := by
  have hpow : 128 ^ count = 128 * 128 ^ (count - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hP := Nat.pow_pos (n := count - 1) (show 0 < 128 by decide)
  rw [hpow]
  generalize 128 ^ (count - 1) = power at h hP ⊢
  unfold signedOf
  rcases Int.lt_or_le value 0 with hneg | hnonneg
  · have hmod : value % ((128 * power : Nat) : Int) = value + ((128 * power : Nat) : Int) := by
      rw [← Int.add_emod_right]
      apply Int.emod_eq_of_lt <;> omega
    rw [hmod]
    split <;> omega
  · have hmod : value % ((128 * power : Nat) : Int) = value := by
      apply Int.emod_eq_of_lt <;> omega
    rw [hmod]
    split <;> omega

theorem pattern_lt (count : Nat) (value : Int) :
    (value % (128 ^ count : Nat)).toNat < 128 ^ count := by
  have hpos := Nat.pow_pos (n := count) (show 0 < 128 by decide)
  have hlt := Int.emod_lt_of_pos value (show (0 : Int) < (128 ^ count : Nat) by omega)
  have hnn := Int.emod_nonneg value (show ((128 ^ count : Nat) : Int) ≠ 0 by omega)
  generalize value % (128 ^ count : Nat) = residue at hlt hnn ⊢
  omega

theorem encodeSignedGroups_size (count : Nat) (value : Int) :
    (encodeSignedGroups count value).size = count := by
  simp [encodeSignedGroups, encodeGroups_length, groupsN_length]

/-- Reading `count` groups of a value's pattern back, inside arbitrary surrounding
    bytes, gives the pattern and consumes exactly `count` bytes. -/
theorem readGroups_encodeSignedGroups (count limit : Nat) (value : Int) (hcount : 1 ≤ count)
    (hlimit : count ≤ limit) (pre suffix : ByteArray) :
    readGroups limit 0
        { data := pre ++ (encodeSignedGroups count value ++ suffix), offset := pre.size } =
      .ok ((value % (128 ^ count : Nat)).toNat,
        { data := pre ++ (encodeSignedGroups count value ++ suffix), offset := pre.size + count }) := by
  have hread := readGroups_encodeGroups (groupsN count (value % (128 ^ count : Nat)).toNat).reverse
    (by
      obtain ⟨rest, hrest⟩ : ∃ rest, count = rest + 1 := ⟨count - 1, by omega⟩
      subst hrest
      simp [groupsN])
    (fun g hg => groupsN_lt _ _ g (by simpa using hg)) limit 0
    (by simp [groupsN_length]; omega) pre suffix
  rw [foldl_groupsN, Nat.mod_eq_of_lt (pattern_lt count value)] at hread
  simp only [List.length_reverse, groupsN_length] at hread
  exact hread

/-- Decoding the encoding of any int32 value, inside arbitrary surrounding bytes,
    returns the value and consumes exactly its encoding. -/
theorem decodeInt32_encodeInt32 (value : Int32) (pre suffix : ByteArray) :
    decodeInt32 { data := pre ++ (encodeInt32 value ++ suffix), offset := pre.size } =
      .ok (value,
        { data := pre ++ (encodeInt32 value ++ suffix),
          offset := pre.size + (encodeInt32 value).size }) := by
  have hlow := value.le_toInt
  have hhigh := value.toInt_lt
  have hmag : value.toInt.natAbs < 64 * 128 ^ 4 := by omega
  have hpos := signedCount_pos 4 value.toInt.natAbs
  have hle := signedCount_le 4 value.toInt.natAbs
  have hbound := signedCount_bound 4 value.toInt.natAbs hmag
  generalize hcount : signedCount 4 value.toInt.natAbs = count at hpos hle hbound
  have henc : encodeInt32 value = encodeSignedGroups count value.toInt := by
    simp [encodeInt32, hcount]
  rw [henc, encodeSignedGroups_size]
  unfold decodeInt32
  rw [readGroups_encodeSignedGroups count 5 value.toInt hpos (by omega)]
  simp only [bind, Except.bind, show pre.size + count - pre.size = count by omega,
    signedOf_pattern count value.toInt hbound hpos]
  rw [if_pos ⟨hlow, hhigh⟩]
  simp [pure, Except.pure, Int32.ofInt_toInt]

theorem signedOf_pattern64 (value : Int) (hlow : -2 ^ 63 ≤ value) (hhigh : value < 2 ^ 63) :
    signedOf (value % (2 ^ 64 : Nat)).toNat (2 ^ 64) = value := by
  unfold signedOf
  split <;> omega

/-- Decoding the encoding of any int64 value, inside arbitrary surrounding bytes,
    returns the value and consumes exactly its encoding. -/
theorem decodeInt64_encodeInt64 (value : Int64) (pre suffix : ByteArray) :
    decodeInt64 { data := pre ++ (encodeInt64 value ++ suffix), offset := pre.size } =
      .ok (value,
        { data := pre ++ (encodeInt64 value ++ suffix),
          offset := pre.size + (encodeInt64 value).size }) := by
  have hlow := value.le_toInt
  have hhigh := value.toInt_lt
  unfold decodeInt64
  by_cases hsmall : value.toInt.natAbs < 2 ^ 55
  · have hmag : value.toInt.natAbs < 64 * 128 ^ 7 := by omega
    have hpos := signedCount_pos 7 value.toInt.natAbs
    have hle := signedCount_le 7 value.toInt.natAbs
    have hbound := signedCount_bound 7 value.toInt.natAbs hmag
    generalize hcount : signedCount 7 value.toInt.natAbs = count at hpos hle hbound
    have henc : encodeInt64 value = encodeSignedGroups count value.toInt := by
      simp [encodeInt64, hsmall, hcount]
    rw [henc, encodeSignedGroups_size]
    have hread := readGroupsThenByte_encodeGroups
      (groupsN count (value.toInt % (128 ^ count : Nat)).toNat).reverse
      (by
        obtain ⟨rest, hrest⟩ : ∃ rest, count = rest + 1 := ⟨count - 1, by omega⟩
        subst hrest
        simp [groupsN])
      (fun g hg => groupsN_lt _ _ g (by simpa using hg)) 8 0
      (by simp [groupsN_length]; omega) pre suffix
    rw [foldl_groupsN, Nat.mod_eq_of_lt (pattern_lt count value.toInt)] at hread
    simp only [List.length_reverse, groupsN_length] at hread
    rw [show encodeSignedGroups count value.toInt =
      (encodeGroups (groupsN count (value.toInt % (128 ^ count : Nat)).toNat).reverse).toByteArray
      from rfl, hread]
    simp only [bind, Except.bind, show pre.size + count - pre.size = count by omega,
      show count ≠ 9 by omega, if_false, signedOf_pattern count value.toInt hbound hpos]
    rw [if_pos ⟨hlow, hhigh⟩]
    simp [pure, Except.pure, Int64.ofInt_toInt]
  · have henc : encodeInt64 value =
        ((groupsN 8 ((value.toInt % (2 ^ 64 : Nat)).toNat / 256)).reverse.map
          (fun group => UInt8.ofNat (group + 128)) ++
          [UInt8.ofNat ((value.toInt % (2 ^ 64 : Nat)).toNat % 256)]).toByteArray := by
      simp only [encodeInt64, hsmall, if_false]
    have hp64 : (value.toInt % (2 ^ 64 : Nat)).toNat < 2 ^ 64 := by
      have := Int.emod_lt_of_pos value.toInt (show (0 : Int) < (2 ^ 64 : Nat) by decide)
      have := Int.emod_nonneg value.toInt (show ((2 ^ 64 : Nat) : Int) ≠ 0 by decide)
      generalize value.toInt % (2 ^ 64 : Nat) = residue at *
      omega
    have hread := readGroupsThenByte_continued
      (groupsN 8 ((value.toInt % (2 ^ 64 : Nat)).toNat / 256)).reverse
      (fun g hg => groupsN_lt _ _ g (by simpa using hg)) 0
      (UInt8.ofNat ((value.toInt % (2 ^ 64 : Nat)).toNat % 256)) pre suffix
    simp only [List.length_reverse, groupsN_length, foldl_groupsN] at hread
    have hvalue : (value.toInt % (2 ^ 64 : Nat)).toNat / 256 % 128 ^ 8 * 256 +
        (UInt8.ofNat ((value.toInt % (2 ^ 64 : Nat)).toNat % 256)).toNat =
          (value.toInt % (2 ^ 64 : Nat)).toNat := by
      rw [UInt8.toNat_ofNat']
      generalize (value.toInt % (2 ^ 64 : Nat)).toNat = pattern at hp64 ⊢
      omega
    rw [hvalue] at hread
    have hsize : (encodeInt64 value).size = 9 := by
      rw [henc]
      simp [groupsN_length]
    rw [hsize, henc, hread]
    simp only [bind, Except.bind, show pre.size + 8 + 1 - pre.size = 9 by omega, if_true,
      signedOf_pattern64 value.toInt hlow hhigh]
    rw [if_pos ⟨hlow, hhigh⟩]
    simp only [pure, Except.pure, Int64.ofInt_toInt]

/-! ## Canonical form: the only freedom is the number of groups -/

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

theorem groupsN_foldl (gs : List Nat) (hlt : ∀ group ∈ gs, group < 128) :
    (groupsN gs.length (gs.foldl (fun accumulator group => accumulator * 128 + group) 0)).reverse =
      gs := by
  obtain ⟨l, rfl⟩ : ∃ l : List Nat, gs = l.reverse := ⟨gs.reverse, by simp⟩
  induction l with
  | nil => rfl
  | cons last init ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_reverse, List.length_cons, List.length_nil] at hlt ⊢
    have hl := hlt last (by simp)
    have hi := ih (fun g hg => hlt g (by simp [hg]))
    rw [List.length_reverse] at hi
    rw [groupsN, show (init.reverse.foldl (fun accumulator group => accumulator * 128 + group) 0 * 128 +
        last) % 128 = last by omega,
      show (init.reverse.foldl (fun accumulator group => accumulator * 128 + group) 0 * 128 +
        last) / 128 = init.reverse.foldl (fun accumulator group => accumulator * 128 + group) 0 by omega,
      List.reverse_cons, hi]

theorem signedOf_emod (unsigned width : Nat) (h : unsigned < width) :
    (signedOf unsigned width % (width : Int)).toNat = unsigned := by
  unfold signedOf
  split
  · rw [← Int.add_emod_right, show (unsigned : Int) - width + width = unsigned by omega,
      Int.emod_eq_of_lt (by omega) (by omega)]
    simp
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    simp

/-- Canonical form of a signed 32-bit VLQ: the bytes the decoder accepts are exactly
    the `count`-group two's-complement pattern of the decoded value, for the number of
    groups it read. The number of groups is the only freedom: sign-extension groups,
    and Python's non-minimal encodings such as `ff 40` for -64, decode to the same
    value as the shortest form. -/
theorem decodeInt32_canonical (cursor next : Cursor) (value : Int32)
    (h : decodeInt32 cursor = .ok (value, next)) :
    next.data = cursor.data ∧ ∃ count, 1 ≤ count ∧ count ≤ 5 ∧
      next.offset = cursor.offset + count ∧
      cursor.data.extract cursor.offset next.offset = encodeSignedGroups count value.toInt := by
  simp only [decodeInt32, bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i read result hread
    split at h
    · rename_i hrange
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hdata, gs, hne, hgs, hlen, hoff, hext, hval⟩ := readGroups_bytes _ _ _ _ _ hread
      have hpos : 1 ≤ gs.length := by
        cases gs with
        | nil => exact absurd rfl hne
        | cons _ _ => simp
      refine ⟨hdata, gs.length, hpos, hlen, hoff, ?_⟩
      rw [Int32.toInt_ofInt_of_le hrange.1 hrange.2, hext, hoff,
        show cursor.offset + gs.length - cursor.offset = gs.length by omega]
      unfold encodeSignedGroups
      rw [hval, signedOf_emod _ _ (foldl_lt gs hgs), groupsN_foldl gs hgs]
    · simp [throw, throwThe, MonadExceptOf.throw] at h

end LeanS7CommPlus.Vlq
