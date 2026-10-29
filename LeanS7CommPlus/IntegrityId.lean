import LeanS7CommPlus.Protocol
import LeanS7CommPlus.Write

/-!
# IntegrityIds

Sessions with integrity tracking (V2, and V1 with a SessionKey) number their
requests with an IntegrityId, a VLQ in the request payload. The client keeps two
counters: one for reads, one for everything else. This follows the Python client:
`READ_FUNCTION_CODES` picks the counter, a request carries the counter's value, and
the counter then steps by one, modulo 2³².

The request places the IntegrityId before the payload's trailing fill bytes: four of
them for GetMultiVariables and SetMultiVariables (`ReadRequest.encode`,
`WriteRequest.encode`). Responses carry one too, but where depends on the controller
family and the function; `ResponseIntegrity` is that position as a named parameter.

The theorems: `IntegrityCounters.next_read` and `next_write` (a request uses and steps
only its own counter), `ids_consecutive` and `ids_nodup` (the requests of one kind get
consecutive ids, none repeated within 2³² requests), `ReadRequest.encode_insert` and
`WriteRequest.encode_insert` (the request encoders place the id before the fill), and
round trips for both response positions.
-/

namespace LeanS7CommPlus

open LeanS7

namespace FunctionCode
def getVariable : UInt16 := 0x04fc
def getLink : UInt16 := 0x0524
def getVariablesAddress : UInt16 := 0x0590
end FunctionCode

/-- The functions numbered with the read counter, as in the Python client. -/
def readFunctions : List UInt16 :=
  [FunctionCode.getMultiVariables, FunctionCode.explore, FunctionCode.getVarSubstreamed,
    FunctionCode.getLink, FunctionCode.getVariable, FunctionCode.getVariablesAddress]

def isReadFunction (function : UInt16) : Bool := readFunctions.contains function

structure IntegrityCounters where
  read : UInt32 := 0
  write : UInt32 := 0
  deriving Repr, BEq, DecidableEq

/-- The IntegrityId for a request with this function, and the counters after it. -/
def IntegrityCounters.next (counters : IntegrityCounters) (function : UInt16) :
    UInt32 × IntegrityCounters :=
  if isReadFunction function then (counters.read, { counters with read := counters.read + 1 })
  else (counters.write, { counters with write := counters.write + 1 })

/-- The IntegrityIds of a run of requests, each paired with its function. -/
def IntegrityCounters.run (counters : IntegrityCounters) :
    List UInt16 → List (UInt16 × UInt32) × IntegrityCounters
  | [] => ([], counters)
  | function :: rest =>
    let (id, counters) := counters.next function
    let (ids, counters) := counters.run rest
    ((function, id) :: ids, counters)

/-- Place an IntegrityId before the last `tail` bytes of a payload, or in front of a
    payload shorter than that, as the Python client does. -/
def insertIntegrityId (payload : ByteArray) (tail : Nat) (id : UInt32) : ByteArray :=
  if tail ≤ payload.size then
    payload.extract 0 (payload.size - tail) ++ Vlq.encodeUInt32 id ++ payload.extract (payload.size - tail) payload.size
  else Vlq.encodeUInt32 id ++ payload

/-- Where a response carries its IntegrityId: nowhere (no integrity tracking), leading
    the payload, or after the body and before `tail` fill bytes. Which one applies is a
    controller fact per family and function. In the CPU 1214C V4.2 capture
    (s7commplus#136) the GetMultiVariables reply has it trailing, before four fill bytes. -/
inductive ResponseIntegrity where
  | none
  | leading
  | trailing (tail : Nat)
  deriving Repr, BEq

/-- Remove a leading IntegrityId. -/
def decodeLeadingIntegrityId (payload : ByteArray) : Except DecodeError (UInt32 × ByteArray) :=
  match Vlq.decodeUInt32 { data := payload } with
  | .error error => .error error
  | .ok (id, cursor) => .ok (id, payload.extract cursor.offset payload.size)

/-- Read a trailing IntegrityId from where the body ends: the VLQ, then exactly `tail`
    zero bytes. -/
def decodeTrailingIntegrityId (tail : Nat) (cursor : Cursor) : Except DecodeError UInt32 :=
  match Vlq.decodeUInt32 cursor with
  | .error error => .error error
  | .ok (id, cursor) =>
    if cursor.data.extract cursor.offset cursor.data.size = ByteArray.mk (Array.replicate tail 0) then .ok id
    else .error (.invalidField cursor.offset s!"expected {tail} fill bytes after the IntegrityId")

/-! ## Counters -/

theorem IntegrityCounters.next_read (counters : IntegrityCounters) (function : UInt16)
    (h : isReadFunction function = true) :
    counters.next function = (counters.read, { counters with read := counters.read + 1 }) := by
  simp [IntegrityCounters.next, h]

theorem IntegrityCounters.next_write (counters : IntegrityCounters) (function : UInt16)
    (h : isReadFunction function = false) :
    counters.next function = (counters.write, { counters with write := counters.write + 1 }) := by
  simp [IntegrityCounters.next, h]

/-- After a run, each counter has stepped once per request of its kind. -/
theorem IntegrityCounters.run_counters (counters : IntegrityCounters) (functions : List UInt16) :
    (counters.run functions).2 =
      { read := counters.read + UInt32.ofNat (functions.filter isReadFunction).length,
        write := counters.write + UInt32.ofNat (functions.filter (! isReadFunction ·)).length } := by
  induction functions generalizing counters with
  | nil => simp [IntegrityCounters.run]
  | cons function rest ih =>
    cases h : isReadFunction function
    · simp only [IntegrityCounters.run, counters.next_write function h, ih, List.filter_cons, h]
      simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false, List.length_cons]
      congr 1
      rw [UInt32.ofNat_add, UInt32.ofNat_one, UInt32.add_assoc, UInt32.add_comm 1]
    · simp only [IntegrityCounters.run, counters.next_read function h, ih, List.filter_cons, h]
      simp only [Bool.not_true, if_true, Bool.false_eq_true, if_false, List.length_cons]
      congr 1
      rw [UInt32.ofNat_add, UInt32.ofNat_one, UInt32.add_assoc, UInt32.add_comm 1]

/-- The read requests of a run get consecutive ids from the read counter, and the other
    requests consecutive ids from the write counter. -/
theorem IntegrityCounters.ids_consecutive (counters : IntegrityCounters) (functions : List UInt16) :
    ((counters.run functions).1.filter (isReadFunction ·.1)).map (·.2) =
        (List.range (functions.filter isReadFunction).length).map
          (fun i => counters.read + UInt32.ofNat i) ∧
      ((counters.run functions).1.filter (! isReadFunction ·.1)).map (·.2) =
        (List.range (functions.filter (! isReadFunction ·)).length).map
          (fun i => counters.write + UInt32.ofNat i) := by
  induction functions generalizing counters with
  | nil => simp [IntegrityCounters.run]
  | cons function rest ih =>
    cases h : isReadFunction function
    · simp only [IntegrityCounters.run, counters.next_write function h, List.filter_cons, h,
        Bool.not_false, if_true, Bool.false_eq_true, if_false, List.map_cons, List.length_cons]
      refine ⟨(ih _).1, ?_⟩
      rw [(ih _).2, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Function.comp_def, Nat.succ_eq_add_one,
        UInt32.ofNat_add, UInt32.ofNat_one, UInt32.add_assoc, UInt32.add_comm 1]
      rw [show UInt32.ofNat 0 = 0 from rfl, UInt32.add_zero]
    · simp only [IntegrityCounters.run, counters.next_read function h, List.filter_cons, h,
        Bool.not_true, if_true, Bool.false_eq_true, if_false, List.map_cons, List.length_cons]
      refine ⟨?_, (ih _).2⟩
      rw [(ih _).1, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Function.comp_def, Nat.succ_eq_add_one,
        UInt32.ofNat_add, UInt32.ofNat_one, UInt32.add_assoc, UInt32.add_comm 1]
      rw [show UInt32.ofNat 0 = 0 from rfl, UInt32.add_zero]

/-- Consecutive ids do not repeat within 2³² of them. -/
theorem consecutive_nodup (start : UInt32) (count : Nat) (hcount : count ≤ 2 ^ 32) :
    ((List.range count).map (fun i => start + UInt32.ofNat i)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  apply List.nodup_range.imp_of_mem
  intro i j hi hj hne heq
  simp only [List.mem_range] at hi hj
  have hij : UInt32.ofNat i = UInt32.ofNat j := by simpa using heq
  have h := congrArg UInt32.toNat hij
  rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  exact hne h

/-- No IntegrityId repeats among the first 2³² requests of either kind. -/
theorem IntegrityCounters.ids_nodup (counters : IntegrityCounters) (functions : List UInt16)
    (hcount : functions.length ≤ 2 ^ 32) :
    (((counters.run functions).1.filter (isReadFunction ·.1)).map (·.2)).Nodup ∧
      (((counters.run functions).1.filter (! isReadFunction ·.1)).map (·.2)).Nodup := by
  obtain ⟨hr, hw⟩ := counters.ids_consecutive functions
  rw [hr, hw]
  exact ⟨consecutive_nodup _ _ (Nat.le_trans (List.length_filter_le _ _) hcount),
    consecutive_nodup _ _ (Nat.le_trans (List.length_filter_le _ _) hcount)⟩

/-! ## Request placement -/

theorem insertIntegrityId_append (body fill : ByteArray) (id : UInt32) :
    insertIntegrityId (body ++ fill) fill.size id = body ++ Vlq.encodeUInt32 id ++ fill := by
  simp only [insertIntegrityId, ByteArray.size_append, Nat.le_add_left, if_true, Nat.add_sub_cancel]
  rw [ByteArray.extract_append_eq_left rfl, ByteArray.extract_append_eq_right rfl rfl]

/-- The read request encoder places the IntegrityId before the four fill bytes. -/
theorem ReadRequest.encode_insert (request : ReadRequest) (id : UInt32) :
    request.encode (some id) = insertIntegrityId (request.encode none) 4 id := by
  have h := insertIntegrityId_append request.encodeBody (uint32BE 0) id
  rw [uint32BE_size] at h
  simp only [ReadRequest.encode, ByteArray.append_empty]
  rw [h]

/-- The write request encoder places the IntegrityId before the four fill bytes. -/
theorem WriteRequest.encode_insert (request : WriteRequest) (id : UInt32) :
    request.encode (some id) = insertIntegrityId (request.encode none) 4 id := by
  have h := insertIntegrityId_append request.encodeBody (uint32BE 0) id
  rw [uint32BE_size] at h
  simp only [WriteRequest.encode, ByteArray.append_empty]
  rw [h]

/-! ## Response positions -/

theorem decodeLeadingIntegrityId_encode (id : UInt32) (payload : ByteArray) :
    decodeLeadingIntegrityId (Vlq.encodeUInt32 id ++ payload) = .ok (id, payload) := by
  have r := Vlq.decodeUInt32_encodeUInt32 id ByteArray.empty payload
  simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at r
  simp only [decodeLeadingIntegrityId]
  rw [show ({ data := Vlq.encodeUInt32 id ++ payload } : Cursor) =
    { data := Vlq.encodeUInt32 id ++ payload, offset := 0 } from rfl, r]
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
  exact ByteArray.extract_append_eq_right rfl (by simp [ByteArray.size_append])

theorem decodeTrailingIntegrityId_encode (id : UInt32) (body : ByteArray) (tail : Nat) :
    decodeTrailingIntegrityId tail
      { data := body ++ (Vlq.encodeUInt32 id ++ ByteArray.mk (Array.replicate tail 0)), offset := body.size } =
      .ok id := by
  simp only [decodeTrailingIntegrityId]
  rw [Vlq.decodeUInt32_encodeUInt32]
  simp only
  rw [if_pos]
  rw [show body ++ (Vlq.encodeUInt32 id ++ ByteArray.mk (Array.replicate tail 0)) =
    (body ++ Vlq.encodeUInt32 id) ++ ByteArray.mk (Array.replicate tail 0) by simp [ByteArray.append_assoc]]
  exact ByteArray.extract_append_eq_right (by simp [ByteArray.size_append])
    (by simp [ByteArray.size_append])

end LeanS7CommPlus
