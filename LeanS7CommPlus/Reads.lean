import LeanS7.Binary

/-!
# What the fixed-width cursor reads consume

Each successful big-endian read returns the encoding of its value as exactly the input
bytes it covered. The canonical-form theorems of the message and value decoders are
built from these.
-/

namespace LeanS7CommPlus

open LeanS7

theorem readUInt8_extract (cursor next : Cursor) (value : UInt8)
    (h : cursor.readUInt8 = .ok (value, next)) :
    cursor.offset + 1 ≤ cursor.data.size ∧
      bytes #[value] = cursor.data.extract cursor.offset (cursor.offset + 1) ∧
      next = { cursor with offset := cursor.offset + 1 } := by
  obtain ⟨hlt, hv, hn⟩ := Cursor.readUInt8_value _ _ _ h
  refine ⟨hlt, ?_, hn⟩
  rw [ByteArray.extract_one _ _ hlt, hv]
  rfl

theorem readUInt16BE_extract (cursor next : Cursor) (value : UInt16)
    (h : cursor.readUInt16BE = .ok (value, next)) :
    cursor.offset + 2 ≤ cursor.data.size ∧
      uint16BE value = cursor.data.extract cursor.offset (cursor.offset + 2) ∧
      next = { cursor with offset := cursor.offset + 2 } := by
  obtain ⟨hl, hv, hn⟩ := Cursor.readUInt16BE_value _ _ _ h
  exact ⟨hl, by rw [hv, ByteArray.extract_two_uint16BE _ _ hl], hn⟩

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

theorem uint64BE_halves (high low : UInt32) :
    uint64BE (UInt64.ofNat (high.toNat * 4294967296 + low.toNat)) = uint32BE high ++ uint32BE low := by
  have hh := high.toNat_lt
  have hl := low.toNat_lt
  have hn : (UInt64.ofNat (high.toNat * 4294967296 + low.toNat)).toNat =
      high.toNat * 4294967296 + low.toNat := by
    rw [UInt64.toNat_ofNat']; omega
  have key : ∀ a b c d e f g h a' b' c' d' e' f' g' h' : UInt8,
      a = a' → b = b' → c = c' → d = d' → e = e' → f = f' → g = g' → h = h' →
      ByteArray.mk #[a, b, c, d, e, f, g, h] =
        ByteArray.mk #[a', b', c', d'] ++ ByteArray.mk #[e', f', g', h'] := by
    intros; subst_vars; rfl
  unfold uint64BE uint32BE
  apply key <;> (apply UInt8.toNat_inj.mp; simp only [UInt8.toNat_ofNat', hn]; omega)

theorem readUInt64BE_value (cursor next : Cursor) (value : UInt64)
    (h : cursor.readUInt64BE = .ok (value, next)) :
    cursor.offset + 8 ≤ cursor.data.size ∧
      uint64BE value = cursor.data.extract cursor.offset (cursor.offset + 8) ∧
      next = { cursor with offset := cursor.offset + 8 } := by
  simp only [Cursor.readUInt64BE, bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · rename_i first rest e1
    split at h
    · contradiction
    · rename_i second rest' e2
      injection h with h
      injection h with hv hn
      obtain ⟨l1, d1, n1⟩ := readUInt32BE_value _ _ _ e1
      rw [n1] at e2
      obtain ⟨l2, d2, n2⟩ := readUInt32BE_value _ _ _ e2
      simp only at l2 d2 n2
      refine ⟨by omega, ?_, by rw [← hn, n2]⟩
      rw [← hv, uint64BE_halves, d1, d2,
        ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]

/-- A successful bounded read covers exactly the bytes it returns. -/
theorem readBytes_extract (cursor next : Cursor) (count : Nat) (payload : ByteArray)
    (h : cursor.readBytes count = .ok (payload, next)) :
    payload = cursor.data.extract cursor.offset (cursor.offset + count) ∧
      next = { cursor with offset := cursor.offset + count } :=
  Cursor.readBytes_value _ _ _ _ h

/-- A successful bounded read returns exactly `count` bytes. -/
theorem readBytes_size (cursor next : Cursor) (count : Nat) (payload : ByteArray)
    (h : cursor.readBytes count = .ok (payload, next)) : payload.size = count := by
  have hfits : count ≤ cursor.remaining := by
    unfold Cursor.readBytes at h
    split at h
    · assumption
    · contradiction
  obtain ⟨hp, -⟩ := Cursor.readBytes_value _ _ _ _ h
  rw [hp, ByteArray.size_extract]
  unfold Cursor.remaining at hfits
  omega

/-- A two-byte literal is its two one-byte literals. -/
theorem bytes_pair (first second : UInt8) :
    bytes #[first, second] = bytes #[first] ++ bytes #[second] := by
  apply ByteArray.ext
  simp [bytes]

/-- One `if` of a long `if … else if …` chain in a hypothesis, as two cases. `split`
    gives up on chains as long as the PValue datatype dispatch. -/
theorem ite_eq_cases {α : Sort _} {c : Prop} {inst : Decidable c} {a b x : α}
    (h : @ite α c inst a b = x) : (c ∧ a = x) ∨ (¬ c ∧ b = x) := by
  by_cases hc : c
  · exact Or.inl ⟨hc, by rwa [if_pos hc] at h⟩
  · exact Or.inr ⟨hc, by rwa [if_neg hc] at h⟩

theorem Except.map_eq_ok {ε α β : Type} {f : α → β} {e : Except ε α} {b : β}
    (h : e.map f = .ok b) : ∃ a, e = .ok a ∧ f a = b := by
  cases e with
  | error _ => simp [Except.map] at h
  | ok a => exact ⟨a, rfl, by simpa [Except.map] using h⟩

end LeanS7CommPlus
