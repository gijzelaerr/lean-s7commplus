import LeanS7CommPlus.Session
import LeanS7CommPlus.Integrity
import LeanS7CommPlus.IntegrityId
import LeanS7CommPlus.SessionKey

/-!
# Sessions with a SessionKey

After an accepted SessionKey setup, every request travels in a V3 frame sealed with
HMAC-SHA256 under the session key, and carries the next IntegrityId of its counter
before its trailing fill bytes. Replies are V3 too; a reply split over fragments is
checked with the state-resume chain of real S7-1200/1500 firmware, which starts with
the standard HMAC, so a single-fragment reply is a plain sealed frame.

`Session.sendKeyed_spec` states exactly what goes on the wire, and
`Session.sendKeyed_opens` that it opens under the session key to the request message.
-/

namespace LeanS7CommPlus

open LeanS7

/-- The fill bytes after a keyed request's IntegrityId: three for the activation and the
    S7-1200 legitimation requests, four for the other requests. -/
def Request.integrityTail : Request → Nat
  | .activate => 3
  | .getVarSubstreamedV1 _ => 3
  | .legitimate _ => 3
  | _ => 4

/-- The session key and the IntegrityId counters of a keyed session. -/
structure Keyed where
  sessionKey : ByteArray
  counters : IntegrityCounters

/-- The state right after an accepted SessionKey setup: both counters at zero. -/
def Keyed.install (sessionKey : ByteArray) : Keyed := { sessionKey, counters := {} }

def Keyed.mac (keyed : Keyed) : Mac := .hmacSha256 keyed.sessionKey

/-- The request message under a keyed session: header, then the payload with the
    IntegrityId before its fill. -/
def Session.keyedMessage (session : Session) (request : Request) (id : UInt32) : ByteArray :=
  encodeRequestHeader (session.frameFor request).2 ++
    insertIntegrityId (request.payload session) request.integrityTail id

/-- Send `request` in a keyed session: the sealed V3 frame, its header, and the session
    and counters after it; `none` outside the request's phase. -/
def Session.sendKeyed (session : Session) (keyed : Keyed) (request : Request) :
    Option (ByteArray × RequestHeader × Session × Keyed) :=
  if request.phase = session.phase then
    let (id, counters) := keyed.counters.next request.function
    some (sealV3 keyed.mac (session.keyedMessage request id), (session.frameFor request).2,
      { session with sequence := session.sequence + 1 }, { keyed with counters })
  else none

/-- An S7-1215C on FW V4.2 expects both counters one id further after the legitimation
    step, whether or not a legitimation was sent (s7commplus
    `_skip_integrity_ids_after_legitimation`; the #136 capture shows the same ids). -/
def Keyed.skipAfterLegitimation (keyed : Keyed) (family : KeyFamily) : Keyed :=
  if family = .s71200 then
    { keyed with counters := { read := keyed.counters.read + 1, write := keyed.counters.write + 1 } }
  else keyed

/-- Check a keyed reply, possibly fragmented, and return its message. -/
def Keyed.openReply (keyed : Keyed) (reply : ByteArray) : Except OpenError ByteArray :=
  openFragments (.stateResume keyed.sessionKey) reply

/-! ## Where a keyed reply carries its IntegrityId

A peer fact the session cannot detect: the emulator and a CPU 1214C share key family 01
but place the SetMultiVariables reply's IntegrityId differently. -/

/-- The kind of peer, for the facts the session cannot detect. -/
inductive PeerProfile where
  /-- A real controller (or PLCSIM), following s7commplus's hardware rules. -/
  | controller
  /-- The s7commplus 0.3.0 emulator (`SessionKeyServer`), as `integration/run.py` runs it. -/
  | emulator
  deriving Repr, BEq, DecidableEq

/-- Where a keyed reply carries its IntegrityId, per peer, key family and function.

    - **Controllers** follow s7commplus's V1 SessionKey profile, which its hardware runs
      validated (s7commplus#136: `_strip_response_integrity_id`,
      `_integrity_id_follows_body`). GetMultiVariables and EXPLORE replies carry the id
      after the body: on a CPU 1214C FW V4.2 before four fill bytes (`fixtures/`),
      elsewhere in an unchecked layout. So do every PLCSIM reply and an S7-1200's
      CreateObject and SetMultiVariables replies. Every other reply leads with it.
    - **The emulator**, probed with the Python client on 2026-11-11: a GetMultiVariables
      reply carries the id after the body with no fill (`… 00 00 02`), a
      SetMultiVariables reply leads with it (`02 00 00 00`), and an EXPLORE reply
      starts with its return value. -/
def responseIntegrity (peer : PeerProfile) (family : KeyFamily) (function : UInt16) :
    ResponseIntegrity :=
  match peer with
  | .emulator =>
    if function = FunctionCode.getMultiVariables then .trailing 0
    else if function = FunctionCode.explore then .afterBody
    else .leading
  | .controller =>
    if function = FunctionCode.getMultiVariables then
      if family = .s71200 then .trailing 4 else .afterBody
    else if function = FunctionCode.explore then .afterBody
    else if family = .plcsim then .afterBody
    else if family = .s71200 ∧
        (function = FunctionCode.createObject ∨ function = FunctionCode.setMultiVariables) then
      .afterBody
    else .leading

/-! ## Key renewal

A SessionKey expires, so the client renews it: it reads a fresh challenge, builds a new
SecurityKey, and writes it with SetVariable to address 1830, all under the old key.
The new key is installed only once the reply opens under the old key and accepts the
write; otherwise the session is closed. s7commplus renews every 25 minutes. -/

/-- A SetVariable reply message accepts the write: it carries the SetVariable function
    (not the generic error), and after its leading IntegrityId, the low 16 bits of the
    return value have no sign bit (s7commplus `_check_set_variable_response`). -/
def setVariableAccepted (message : ByteArray) : Bool :=
  match splitResponse message with
  | .error _ => false
  | .ok (header, payload) =>
    header.function == FunctionCode.setVariable &&
      match decodeLeadingIntegrityId payload with
      | .error _ => false
      | .ok (_, rest) =>
        match decodeReturnValue rest with
        | .ok returnValue => returnValue &&& 0x8000 == 0
        | .error _ => false

/-- An accepted SetVariable reply is a response header with the SetVariable function,
    a leading IntegrityId in any 32-bit VLQ form, and a return value whose low 16 bits
    have no sign bit. -/
theorem setVariableAccepted_spec (message : ByteArray) (h : setVariableAccepted message = true) :
    ∃ header reserved1 reserved2 idBytes id rest returnValue,
      message = encodeResponseHeaderWith reserved1 reserved2 header ++ (idBytes ++ rest) ∧
      header.function = FunctionCode.setVariable ∧ Vlq.UInt32Form id idBytes ∧
      decodeReturnValue rest = .ok returnValue ∧ returnValue &&& 0x8000 = 0 := by
  unfold setVariableAccepted at h
  split at h
  · contradiction
  · rename_i header payload hsplit
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hfunction, h⟩ := h
    split at h
    · contradiction
    · rename_i id rest hleading
      split at h
      · rename_i returnValue hreturn
        obtain ⟨-, reserved1, reserved2, hmessage⟩ := splitResponse_canonical _ _ _ hsplit
        obtain ⟨idBytes, hpayload, hform⟩ := decodeLeadingIntegrityId_canonical _ _ _ hleading
        refine ⟨header, reserved1, reserved2, idBytes, id, rest, returnValue, ?_, hfunction, hform,
          hreturn, by simpa using h⟩
        rw [hmessage, hpayload]
      · contradiction

/-- Finish a renewal with the reply to the SecurityKey write: the session with the new
    key, or `none` when the session must be closed. -/
def Keyed.finishRenewal (keyed : Keyed) (newKey reply : ByteArray) : Option Keyed :=
  match keyed.openReply reply with
  | .error _ => none
  | .ok message => if setVariableAccepted message then some { keyed with sessionKey := newKey } else none

/-! ## Properties -/

/-- What a keyed send puts on the wire: the request message, with the IntegrityId the
    request's own counter holds, sealed under the session key. Only that counter steps;
    the phase, header and sequence number are those of a plain send. -/
theorem Session.sendKeyed_spec (session : Session) (keyed : Keyed) (request : Request)
    (frame : ByteArray) (header : RequestHeader) (next : Session) (keyed' : Keyed)
    (h : session.sendKeyed keyed request = some (frame, header, next, keyed')) :
    request.phase = session.phase ∧ header = (session.frameFor request).2 ∧
      frame = sealV3 keyed.mac (session.keyedMessage request (keyed.counters.next request.function).1) ∧
      keyed'.counters = (keyed.counters.next request.function).2 ∧
      keyed'.sessionKey = keyed.sessionKey ∧
      next.phase = session.phase ∧ next.sequence = session.sequence + 1 := by
  unfold Session.sendKeyed at h
  split at h
  · rename_i hphase
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hframe, hheader, hnext, hkeyed⟩ := h
    subst hframe hheader hnext hkeyed
    exact ⟨hphase, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · contradiction

/-- A keyed frame opens under the session key to the request message, provided the
    message fits a frame with its envelope. -/
theorem Session.sendKeyed_opens (session : Session) (keyed : Keyed) (request : Request)
    (frame : ByteArray) (header : RequestHeader) (next : Session) (keyed' : Keyed)
    (h : session.sendKeyed keyed request = some (frame, header, next, keyed'))
    (hsize : (session.keyedMessage request (keyed.counters.next request.function).1).size + 33 < 65536) :
    openV3 keyed.mac frame = .ok (session.keyedMessage request (keyed.counters.next request.function).1) := by
  obtain ⟨_, _, hframe, _⟩ := session.sendKeyed_spec keyed request frame header next keyed' h
  rw [hframe]
  exact openV3_sealV3 _ _ hsize

/-- Reads use and step the read counter, every other request the write counter. -/
theorem Session.sendKeyed_counter (session : Session) (keyed : Keyed) (request : Request)
    (frame : ByteArray) (header : RequestHeader) (next : Session) (keyed' : Keyed)
    (h : session.sendKeyed keyed request = some (frame, header, next, keyed')) :
    (isReadFunction request.function = true →
      keyed'.counters = { keyed.counters with read := keyed.counters.read + 1 }) ∧
    (isReadFunction request.function = false →
      keyed'.counters = { keyed.counters with write := keyed.counters.write + 1 }) := by
  obtain ⟨_, _, _, hcounters, _⟩ := session.sendKeyed_spec keyed request frame header next keyed' h
  refine ⟨fun hr => ?_, fun hw => ?_⟩
  · rw [hcounters, keyed.counters.next_read _ hr]
  · rw [hcounters, keyed.counters.next_write _ hw]

/-- The new key is installed only after the renewal reply opens under the old key and
    accepts the write; the IntegrityId counters carry on. -/
theorem Keyed.finishRenewal_spec (keyed keyed' : Keyed) (newKey reply : ByteArray)
    (h : keyed.finishRenewal newKey reply = some keyed') :
    ∃ message, keyed.openReply reply = .ok message ∧ setVariableAccepted message = true ∧
      keyed'.sessionKey = newKey ∧ keyed'.counters = keyed.counters := by
  unfold Keyed.finishRenewal at h
  split at h
  · contradiction
  · rename_i message hopen
    split at h
    · rename_i haccepted
      injection h with h
      subst h
      exact ⟨message, hopen, haccepted, rfl, rfl⟩
    · contradiction

/-- A reply that does not open under the old key never installs a key. -/
theorem Keyed.finishRenewal_unopened (keyed : Keyed) (newKey reply : ByteArray) (error : OpenError)
    (h : keyed.openReply reply = .error error) : keyed.finishRenewal newKey reply = none := by
  simp [Keyed.finishRenewal, h]

/-- A keyed reply is accepted only if it is exactly the state-resume sealing of the
    message it yields. -/
theorem Keyed.openReply_sound (keyed : Keyed) (reply message : ByteArray)
    (h : keyed.openReply reply = .ok message) :
    ∃ pieces, message = joinFragments pieces ∧
      reply = sealFragments (.stateResume keyed.sessionKey) pieces :=
  openFragments_sound _ _ _ h

end LeanS7CommPlus
