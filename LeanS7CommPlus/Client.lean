import Std.Async.TCP
import LeanS7.Transport
import LeanS7CommPlus.Session
import LeanS7CommPlus.Fragments
import LeanS7CommPlus.KeyedSession
import LeanS7CommPlus.KeyDerivation

/-!
# A plain V1 client

Connects over ISO-on-TCP with the S7CommPlus TSAPs (calling `0x0600`, called
`SIMATIC-ROOT-HMI`), opens a plain V1 session and reads, writes and browses data
blocks. The socket, TPKT and COTP data handling come from lean-s7; this module adds
the S7CommPlus connection request, whose called TSAP is a 16-byte name.

Replies split over several fragments are reassembled.

This is a test client for the Python emulator. It does not speak TLS or the
SessionKey handshake, and a real S7-1200/1500 with access protection will refuse it.
-/

namespace LeanS7CommPlus

open LeanS7 Std Std.Net Std.Async

/-- The S7CommPlus COTP connection request, in the parameter order of the Python
    client: calling TSAP, called TSAP, TPDU size. -/
def encodeS7CommPlusConnectionRequest (callingTsap : UInt16) (calledTsap : ByteArray)
    (tpduSizeExponent : UInt8) : ByteArray :=
  let parameters := bytes #[0xc1, 2] ++ uint16BE callingTsap ++
    bytes #[0xc2, UInt8.ofNat calledTsap.size] ++ calledTsap ++ bytes #[0xc0, 1, tpduSizeExponent]
  bytes #[UInt8.ofNat (6 + parameters.size), 0xe0, 0, 0, 0, 1, 0] ++ parameters

def remoteTsap : ByteArray := "SIMATIC-ROOT-HMI".toUTF8
def localTsap : UInt16 := 0x0600

structure Client where
  connection : Transport.Connection
  session : Session
  /-- The session key and IntegrityId counters, once a SessionKey setup is accepted. -/
  keyed : Option Keyed := none
  timeoutMs : Option Nat

private def awaitIO (operation : Async α) : IO α := do
  let task ← operation.toIO
  task.block

private def orFail [Repr ε] (label : String) (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{label}: {reprStr error}"

/-- Open a TCP connection and the ISO transport connection. -/
def connectTransport (host : String) (port : UInt16) (timeoutMs : Option Nat) :
    IO Transport.Connection := do
  let addresses ← Transport.resolve (.hostname host) port timeoutMs
  let some address := addresses[0]? | throw <| IO.userError s!"cannot resolve {host}"
  let socket ← TCP.Socket.Client.mk
  awaitIO (socket.connect address)
  socket.noDelay
  Transport.sendFrame socket (encodeS7CommPlusConnectionRequest localTsap remoteTsap 0x0a) timeoutMs
  let confirmation ← orFail "COTP connection confirm" <|
    COTP.decodeConnectionConfirm (← Transport.receiveFrame socket timeoutMs)
  let connection : Transport.Connection :=
    { socket, localReference := 1, remoteReference := confirmation.sourceReference,
      tpduSizeExponent := 0x0a }
  pure connection

/-- The most bytes of one reassembled reply, as in the Python client. -/
def maxReplyBytes : Nat := 16 * 1024 * 1024

/-- Receive ISO data units until they hold a whole, possibly fragmented, message. -/
def receiveMessage (connection : Transport.Connection) (timeoutMs : Option Nat) : IO ByteArray := do
  let mut buffer ← Transport.receiveData connection.socket timeoutMs
  let mut units := 1
  while !fragmentsComplete buffer do
    if units ≥ maxFragments || buffer.size > maxReplyBytes then
      throw <| IO.userError s!"reply exceeds {maxFragments} fragments or {maxReplyBytes} bytes"
    buffer := buffer ++ (← Transport.receiveData connection.socket timeoutMs)
    units := units + 1
  pure buffer

/-- Send a request and receive its reply: the reply header and the payload after it.
    In a keyed session the request is sealed and the reply checked under the key. -/
def Client.exchange (client : Client) (request : Request) :
    IO (ResponseHeader × ByteArray × RequestHeader × Session × Option Keyed) := do
  let (frame, header, sent, keyed) ← match client.keyed with
    | none =>
      match client.session.send request with
      | some (frame, header, sent) => pure (frame, header, sent, none)
      | none => throw <| IO.userError s!"request {request.function} is not allowed in phase {repr client.session.phase}"
    | some keyed =>
      match client.session.sendKeyed keyed request with
      | some (frame, header, sent, keyed) => pure (frame, header, sent, some keyed)
      | none => throw <| IO.userError s!"request {request.function} is not allowed in phase {repr client.session.phase}"
  Transport.sendData client.connection.socket frame client.timeoutMs
  let replyFrame ← receiveMessage client.connection client.timeoutMs
  let message ← match keyed with
    | none => pure (← orFail "reply frame" (reassemble replyFrame)).2
    | some keyed => orFail "keyed reply" (keyed.openReply replyFrame)
  let (reply, _) ← orFail "reply header" (decodeResponseHeader { data := message })
  pure (reply, message.extract 10 message.size, header, sent, keyed)

/-- Run one request through the session state machine. -/
def Client.step (client : Client) (request : Request) (sessionId : ByteArray → Option UInt32 := fun _ => none) :
    IO (Client × ByteArray) := do
  let (reply, payload, header, sent, keyed) ← client.exchange request
  let some next := sent.receive request header reply (sessionId payload)
    | throw <| IO.userError s!"reply function {reply.function} sequence {reply.sequence} does not answer request {header.function} sequence {header.sequence}"
  pure ({ client with session := next, keyed }, payload)

/-- Connect, then InitSSL and CreateObject: the client and the CreateObject reply. -/
def Client.create (host : String) (port : UInt16) (timeoutMs : Option Nat) :
    IO (Client × CreateObjectReply) := do
  let connection ← connectTransport host port timeoutMs
  let client : Client := { connection, session := Session.initial, timeoutMs }
  let (client, _) ← client.step .initSsl
  let (client, payload) ← client.step .createObject fun payload =>
    match decodeCreateObjectReply payload with
    | .ok reply => some reply.sessionId
    | .error _ => none
  let reply ← orFail "CreateObject reply" (decodeCreateObjectReply payload)
  if reply.returnValue != 0 then
    throw <| IO.userError s!"CreateObject failed with return value {reply.returnValue}"
  pure (client, reply)

def Client.checkSetupReply (setupReply : ByteArray) : IO Unit := do
  let (returnValue, _) ← orFail "SetupSession reply" (Vlq.decodeUInt64 { data := setupReply })
  if returnValue != 0 then
    throw <| IO.userError s!"SetupSession failed with return value {returnValue}"

/-- Connect and open a plain V1 session: InitSSL, CreateObject, SetupSession. -/
def Client.connect (host : String) (port : UInt16) (timeoutMs : Option Nat := some 5000) : IO Client := do
  let (client, reply) ← Client.create host port timeoutMs
  let (client, setupReply) ← client.step (.setupSession reply.serverSessionVersion)
  Client.checkSetupReply setupReply
  pure client

/-- TEST ONLY. Open a V1 SessionKey session with key2 and the blob given by the caller
    instead of drawn and built by the handshake: the session key is derived from key2
    and the controller's challenge (`deriveSessionKey`), then the SessionKey setup, the
    activation and the protection-level read, then V3 frames throughout. This is how
    the emulator, which holds a configured key and cannot decrypt a blob, is tested;
    it exercises the key derivation, the wire format and the keyed session, not the
    blob. -/
def Client.connectWithTestKey2 (host : String) (port : UInt16) (key2 : ByteArray)
    (blob : ByteArray := ByteArray.mk (Array.replicate 180 0)) (timeoutMs : Option Nat := some 5000) :
    IO Client := do
  let (client, reply) ← Client.create host port timeoutMs
  let some challenge := reply.challenge
    | throw <| IO.userError "the controller sends no session challenge"
  if challenge.size < 18 then
    throw <| IO.userError s!"session challenge of {challenge.size} bytes is too short"
  let sessionKey := deriveSessionKey key2 challenge
  let some fingerprint := reply.fingerprint
    | throw <| IO.userError "the controller advertises no public-key fingerprint"
  let some (family, _) := parseFingerprint fingerprint
    | throw <| IO.userError s!"unsupported fingerprint {fingerprint}"
  let some publicKey := publicKey? fingerprint
    | throw <| IO.userError s!"no bundled public key for {fingerprint}"
  let securityKey := SecurityKey.ofKeys family publicKey sessionKey blob
  let (client, setupReply) ← client.step (.setupSessionKey reply.serverSessionVersion securityKey.encode)
  Client.checkSetupReply setupReply
  let client := { client with keyed := some (Keyed.install sessionKey) }
  let (client, _) ← client.step .activate
  let client := { client with keyed := client.keyed.map (Keyed.skipAfterLegitimation · family) }
  let (client, _) ← client.step (.getVarSubstreamed AttributeId.effectiveProtectionLevel)
  pure client

def Client.qualifierForm (client : Client) : QualifierForm :=
  if client.keyed.isSome then .vlq else .fixed

/-- Read `size` bytes at `start` of data block `db`. -/
def Client.readDb (client : Client) (db : UInt16) (start size : UInt32) : IO (Client × ByteArray) := do
  let request : ReadRequest :=
    { addresses := [ItemAddress.db db start size], form := client.qualifierForm, keyQualifier := 0 }
  let (client, payload) ← client.step (.read request)
  let (reply, _) ← orFail "read reply" (decodeReadReply { data := payload })
  let results ← orFail "read results" (reply.results 1)
  match results with
  | [.ok (.scalar (.blob _ data))] => pure (client, data)
  | [.ok _] => throw <| IO.userError "read returned a value that is not a byte block"
  | [.error code] => throw <| IO.userError s!"read failed with PLC error {code}"
  | _ => throw <| IO.userError "read returned no result"

/-- Write bytes at `start` of data block `db`. -/
def Client.writeDb (client : Client) (db : UInt16) (start : UInt32) (data : ByteArray) : IO Client := do
  let request : WriteRequest :=
    { addresses := [ItemAddress.db db start (UInt32.ofNat data.size)],
      values := [.scalar (.blob 0 data)], form := client.qualifierForm, keyQualifier := 0 }
  let (client, payload) ← client.step (.write request)
  -- A keyed write reply leads with its IntegrityId.
  let payload ← if client.keyed.isSome then
      pure (← orFail "write reply IntegrityId" (decodeLeadingIntegrityId payload)).2
    else pure payload
  let (reply, _) ← orFail "write reply" (decodeWriteReply { data := payload })
  if reply.returnValue != 0 then
    throw <| IO.userError s!"write failed with return value {reply.returnValue}"
  if let some (_, code) := reply.errors.head? then
    throw <| IO.userError s!"write failed with PLC error {code}"
  pure client

/-- A name attribute as text: UTF-16BE when it contains a zero byte (the emulator),
    one byte per character otherwise (an S7-1500), as the Python client decides. -/
def decodeName (utf8OrUtf16 : ByteArray) : String :=
  let bytes := utf8OrUtf16.toList
  if bytes.contains 0 then
    let rec pairs : List UInt8 → List Char
      | high :: low :: rest => Char.ofNat (high.toNat * 256 + low.toNat) :: pairs rest
      | _ => []
    String.ofList (pairs bytes)
  else String.ofList (bytes.map fun byte => Char.ofNat byte.toNat)

/-- The data blocks of the program: relation id, name and block number. -/
def Client.listDataBlocks (client : Client) : IO (Client × List (UInt32 × String × UInt32)) := do
  let (client, payload) ← client.step
    (.explore ObjectId.thePlcProgram [AttributeId.objectVariableTypeName, AttributeId.blockNumber])
  let (returnValue, cursor) ← orFail "EXPLORE reply" (Vlq.decodeUInt64 { data := payload })
  if returnValue != 0 then
    throw <| IO.userError s!"EXPLORE failed with return value {returnValue}"
  -- s7commplus 0.3.0 sends the data blocks as consecutive top-level objects; later
  -- versions wrap them in thePLCProgram. Read every tree that follows.
  let rec trees : Nat → Cursor → Except DecodeError (List Item)
    | 0, _ => .ok []
    | fuel + 1, cursor =>
      match cursor.readUInt8 with
      | .ok (0xa1, _) => do
        let (items, cursor) ← decodeTree cursor
        pure (items ++ (← trees fuel cursor))
      | _ => .ok []
  let items ← orFail "EXPLORE tree" (trees cursor.remaining cursor)
  -- Collect each data-block object (class 2574) with its name and block number.
  let rec collect : List Item → Option (UInt32 × String × UInt32) → List (UInt32 × String × UInt32)
    | [], _ => []
    | .objectStart relationId 2574 _ _ :: rest, _ => collect rest (some (relationId, "", 0))
    | .attribute 233 (.scalar (.wstring name)) :: rest, some (id, _, number) =>
      collect rest (some (id, decodeName name, number))
    | .attribute 2521 (.scalar (.udint number)) :: rest, some (id, name, _) =>
      collect rest (some (id, name, number))
    | .objectEnd :: rest, some block => block :: collect rest none
    | _ :: rest, current => collect rest current
  pure (client, collect items none)

def Client.close (client : Client) : IO Unit :=
  Transport.disconnect client.connection client.timeoutMs

end LeanS7CommPlus
