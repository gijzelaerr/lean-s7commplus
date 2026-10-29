import LeanS7.Binary
import LeanS7CommPlus.Protocol
import LeanS7CommPlus.Frame
import LeanS7CommPlus.Message
import LeanS7CommPlus.Tree
import LeanS7CommPlus.Access
import LeanS7CommPlus.Write

/-!
# Plain V1 sessions

The requests of a plain V1 session (no TLS, no SessionKey) and the state machine
that orders them, as the Python client sends them (`s7commplus/connection.py`) and
as captured against the Python emulator:

1. **InitSSL** (`0x05b3`, sequence 0, session 0, transport flags `0x30`), a V1
   frame. Without TLS the reply's function is not checked: real PLCs answer with
   ERROR2 (`0x05a9`), the emulator with `0x05b3`.
2. **CreateObject** (`0x04ca`, sequence 1, session 288, flags `0x36`), a V1 frame
   with the ServerSession object tree. The reply carries the session id as its
   first object id and the ServerSessionVersion as attribute 306.
3. **SetupSession**: SetMultiVariables (`0x0542`, sequence 2, the session id,
   flags `0x34`) in a V2 frame, writing the ServerSessionVersion back to
   attribute 306 of the session object.
4. Data requests (GetMultiVariables, SetMultiVariables, EXPLORE) with increasing
   sequence numbers, the session id and flags `0x34`, in V1 frames.

A reply belongs to the outstanding request when its function matches (or is the
generic ERROR function `0x04b1`) and its sequence number is the request's.
-/

namespace LeanS7CommPlus

open LeanS7

namespace ObjectId
/-- The session object placeholder in requests before a session exists. -/
def nullServerSession : UInt32 := 288
def serverSessionContainer : UInt32 := 285
def getNewRidOnServer : UInt32 := 211
def classServerSession : UInt32 := 287
def classSubscriptions : UInt32 := 255
def thePlcProgram : UInt32 := 3
end ObjectId

namespace AttributeId
def objectVariableTypeName : UInt32 := 233
def serverSessionClientRid : UInt32 := 300
def serverSessionVersion : UInt32 := 306
def blockNumber : UInt32 := 2521
end AttributeId

/-- The generic error function a PLC may answer any request with. -/
def errorFunction : UInt16 := 0x04b1

/-! ## Request payloads -/

/-- The InitSSL request payload. -/
def initSslPayload : ByteArray := uint32BE 0

/-- A WSTRING of ASCII text. -/
def asciiWString (text : String) : Value :=
  .scalar (.wstring text.toUTF8)

/-- The ServerSession object tree the Python client creates. -/
def createObjectItems : List Item :=
  [.objectStart ObjectId.getNewRidOnServer ObjectId.classServerSession 0 0,
   .attribute AttributeId.objectVariableTypeName (asciiWString "s7commplus"),
   .attribute 289 (asciiWString "1:::6.0::s7commplus"),
   .attribute 296 (asciiWString "s7commplus"),
   .attribute 297 (asciiWString ""),
   .attribute 298 (asciiWString "s7commplus"),
   .attribute 299 (.scalar (.udint 1)),
   .attribute AttributeId.serverSessionClientRid (.scalar (.rid 0x80c3c901)),
   .attribute 301 (asciiWString ""),
   .objectStart ObjectId.getNewRidOnServer ObjectId.classSubscriptions 0 0,
   .attribute AttributeId.objectVariableTypeName (asciiWString "SubscriptionContainer"),
   .objectEnd,
   .objectEnd]

/-- The CreateObject request payload: the container id, a UDINT 0, a zero word, the
    object tree and a zero word. -/
def createObjectPayload : ByteArray :=
  uint32BE ObjectId.serverSessionContainer ++ (PValue.udint 0).encode ++ uint32BE 0 ++
    encodeItems createObjectItems ++ uint32BE 0

/-- The SetupSession payload: SetMultiVariables on the session object, writing
    `serverSessionVersion` (the bytes of the reply's attribute 306) to attribute 306. -/
def setupSessionPayload (sessionId : UInt32) (serverSessionVersion : ByteArray) : ByteArray :=
  uint32BE sessionId ++ Vlq.encodeUInt32 1 ++ Vlq.encodeUInt32 1 ++
    Vlq.encodeUInt32 AttributeId.serverSessionVersion ++ Vlq.encodeUInt32 1 ++
    serverSessionVersion ++ bytes #[0x00] ++ encodeObjectQualifier .fixed 0 ++ uint32BE 0

/-- An EXPLORE request for the attributes of an object's children. -/
def explorePayload (exploreId : UInt32) (attributes : List UInt32) : ByteArray :=
  uint32BE exploreId ++ Vlq.encodeUInt32 0 ++ bytes #[1, 1, 0, 0] ++
    Vlq.encodeUInt32 (UInt32.ofNat attributes.length) ++ encodeVlqList attributes ++
    uint32BE 0 ++ bytes #[0x00]

/-! ## CreateObject reply -/

/-- The bytes of the last value of an attribute in a decoded tree: a value, or a
    struct up to its terminator. The emulator sends attribute 306 twice; like the
    Python client, the last one counts. -/
def attributeBytes (id : UInt32) : List Item → Option ByteArray
  | [] => none
  | .attribute attributeId value :: rest =>
    match attributeBytes id rest with
    | some later => some later
    | none => if attributeId = id then some value.encode else none
  | .attributeStruct attributeId structId :: rest =>
    match attributeBytes id rest with
    | some later => some later
    | none => if attributeId = id then some (structHeader structId ++ structBody 1 rest) else none
  | _ :: rest => attributeBytes id rest
where
  /-- The encoding of the struct's members up to its terminator, at nesting `depth`. -/
  structBody : Nat → List Item → ByteArray
    | _, [] => ByteArray.empty
    | depth, item :: rest =>
      match item with
      | .structEnd => if depth ≤ 1 then item.encode else item.encode ++ structBody (depth - 1) rest
      | .memberStruct .. => item.encode ++ structBody (depth + 1) rest
      | _ => item.encode ++ structBody depth rest

structure CreateObjectReply where
  returnValue : UInt64
  sessionId : UInt32
  serverSessionVersion : ByteArray

/-- Decode a CreateObject reply payload: return value, object ids, then the tree. -/
def decodeCreateObjectReply (payload : ByteArray) : Except DecodeError CreateObjectReply := do
  let cursor : Cursor := { data := payload }
  let (returnValue, cursor) ← Vlq.decodeUInt64 cursor
  let (count, cursor) ← cursor.readUInt8
  if count = 0 then
    throw (.invalidField cursor.offset "CreateObject reply carries no object id")
  let (ids, cursor) ← decodeVlqList count.toNat cursor
  let (items, _) ← decodeTree cursor
  let some sessionId := ids.head? | throw (.invalidField 0 "no object id")
  let some version := attributeBytes AttributeId.serverSessionVersion items
    | throw (.invalidField 0 "CreateObject reply has no ServerSessionVersion")
  pure { returnValue, sessionId, serverSessionVersion := version }

/-! ## The session state machine -/

inductive Phase where
  | connected
  | sslProbed
  | created
  | ready
  deriving BEq, DecidableEq, Repr

structure Session where
  phase : Phase
  sessionId : UInt32
  sequence : UInt16
  deriving BEq, Repr

def Session.initial : Session := { phase := .connected, sessionId := 0, sequence := 0 }

/-- A request the session can send. -/
inductive Request where
  | initSsl
  | createObject
  | setupSession (serverSessionVersion : ByteArray)
  | read (request : ReadRequest)
  | write (request : WriteRequest)
  | explore (exploreId : UInt32) (attributes : List UInt32)

def Request.function : Request → UInt16
  | .initSsl => FunctionCode.initSsl
  | .createObject => FunctionCode.createObject
  | .setupSession _ => FunctionCode.setMultiVariables
  | .read _ => FunctionCode.getMultiVariables
  | .write _ => FunctionCode.setMultiVariables
  | .explore .. => FunctionCode.explore

/-- The phase a request may be sent in. -/
def Request.phase : Request → Phase
  | .initSsl => .connected
  | .createObject => .sslProbed
  | .setupSession _ => .created
  | _ => .ready

/-- The frame version and request header of a request in a session. -/
def Session.frameFor (session : Session) (request : Request) : FrameVersion × RequestHeader :=
  let header (sessionId : UInt32) (flags : UInt8) : RequestHeader :=
    { function := request.function, sequence := session.sequence, session := sessionId,
      transportFlags := flags }
  match request with
  | .initSsl => (.v1, header 0 0x30)
  | .createObject => (.v1, header ObjectId.nullServerSession 0x36)
  | .setupSession _ => (.v2, header session.sessionId 0x34)
  | _ => (.v1, header session.sessionId 0x34)

def Request.payload (session : Session) : Request → ByteArray
  | .initSsl => initSslPayload
  | .createObject => createObjectPayload
  | .setupSession version => setupSessionPayload session.sessionId version
  | .read request => request.encode none
  | .write request => request.encode none
  | .explore exploreId attributes => explorePayload exploreId attributes

/-- Send `request`: the frame to put on the wire and the session after it, or `none`
    when the request is not allowed in the session's phase. -/
def Session.send (session : Session) (request : Request) : Option (ByteArray × RequestHeader × Session) :=
  if request.phase = session.phase then
    let (version, header) := session.frameFor request
    let frame := encodeFrame version (encodeRequestHeader header ++ request.payload session)
    some (frame, header, { session with sequence := session.sequence + 1 })
  else none

/-- Whether a reply header answers the outstanding request. -/
def answers (request : RequestHeader) (reply : ResponseHeader) : Bool :=
  isResponseOpcode reply.opcode && reply.sequence == request.sequence &&
    (reply.function == request.function || reply.function == errorFunction)

/-- The phase after a successful reply to a request of the given kind. -/
def Phase.after (phase : Phase) (request : Request) : Phase :=
  match request with
  | .initSsl => .sslProbed
  | .createObject => .created
  | .setupSession _ => .ready
  | _ => phase

/-- Whether a reply's function is checked: every request but InitSSL. -/
def Request.checksFunction : Request → Bool
  | .initSsl => false
  | _ => true

/-- The session id after a request's reply: CreateObject sets it. -/
def Request.nextSessionId : Request → UInt32 → Option UInt32 → UInt32
  | .createObject, _, some id => id
  | _, current, _ => current

/-- Accept a reply to the outstanding request. InitSSL is the only request whose reply
    function is not checked; CreateObject also sets the session id. -/
def Session.receive (session : Session) (request : Request) (pending : RequestHeader)
    (reply : ResponseHeader) (sessionId : Option UInt32) : Option Session :=
  if isResponseOpcode reply.opcode && reply.sequence == pending.sequence &&
      (!request.checksFunction || reply.function == pending.function ||
        reply.function == errorFunction) then
    some { session with
      phase := session.phase.after request
      sessionId := request.nextSessionId session.sessionId sessionId }
  else none

/-! ## Properties -/

/-- Sending is only possible in the request's phase, stamps the request with the
    session's sequence number and the request's function, keeps the phase, and
    advances the sequence number. -/
theorem Session.send_spec (session : Session) (request : Request) (frame : ByteArray)
    (header : RequestHeader) (next : Session)
    (h : session.send request = some (frame, header, next)) :
    request.phase = session.phase ∧ header.sequence = session.sequence ∧
      header.function = request.function ∧ next.phase = session.phase ∧
      next.sessionId = session.sessionId ∧ next.sequence = session.sequence + 1 := by
  unfold Session.send at h
  split at h
  · rename_i hphase
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hheader, hnext⟩ := h
    subst hheader hnext
    refine ⟨hphase, ?_, ?_, rfl, rfl, rfl⟩ <;>
      (unfold Session.frameFor; cases request <;> rfl)
  · contradiction

/-- A reply is accepted only if it carries the outstanding request's sequence number
    and, except for InitSSL, its function or the generic error function. -/
theorem Session.receive_spec (session : Session) (request : Request) (pending : RequestHeader)
    (reply : ResponseHeader) (sessionId : Option UInt32) (next : Session)
    (h : session.receive request pending reply sessionId = some next) :
    reply.sequence = pending.sequence ∧ isResponseOpcode reply.opcode ∧
      (request.checksFunction → reply.function = pending.function ∨ reply.function = errorFunction) ∧
      next.phase = session.phase.after request ∧ next.sequence = session.sequence := by
  simp only [Session.receive, Option.ite_none_right_eq_some, Option.some.injEq] at h
  obtain ⟨hc, rfl⟩ := h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
  obtain ⟨⟨hopcode, hsequence⟩, hfunction⟩ := hc
  refine ⟨hsequence, hopcode, fun hchecks => ?_, rfl, rfl⟩
  rcases hfunction with (hno | hsame) | herror
  · simp [hchecks] at hno
  · exact Or.inl hsame
  · exact Or.inr herror

/-- The phase after a request sent in its own phase: one step along InitSSL,
    CreateObject, SetupSession, and then ready for data requests. -/
theorem Phase.after_spec (request : Request) :
    request.phase.after request =
      match request.phase with
      | .connected => .sslProbed
      | .sslProbed => .created
      | .created => .ready
      | .ready => .ready := by
  cases request <;> rfl

/-- Data requests (reads, writes, EXPLORE) can only be sent once the session is ready,
    and the only request that makes a session ready is SetupSession. -/
theorem Session.ready_only_after_setup (session : Session) (request : Request) :
    session.phase.after request = .ready → session.phase = .ready ∨
      ∃ version, request = .setupSession version := by
  cases request <;> simp [Phase.after]

end LeanS7CommPlus
