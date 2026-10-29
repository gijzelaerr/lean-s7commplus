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

/-- A keyed reply is accepted only if it is exactly the state-resume sealing of the
    message it yields. -/
theorem Keyed.openReply_sound (keyed : Keyed) (reply message : ByteArray)
    (h : keyed.openReply reply = .ok message) :
    ∃ pieces, message = joinFragments pieces ∧
      reply = sealFragments (.stateResume keyed.sessionKey) pieces :=
  openFragments_sound _ _ _ h

end LeanS7CommPlus
