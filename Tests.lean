import LeanS7CommPlus

open LeanS7 LeanS7CommPlus

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

/-- Bytes of an even-length lowercase hex string. -/
def hexBytes (text : String) : ByteArray :=
  let rec go : List Char → List UInt8
    | high :: low :: rest => UInt8.ofNat (hexDigit high * 16 + hexDigit low) :: go rest
    | _ => []
  (go text.toList).toByteArray

def toHex (data : ByteArray) : String :=
  String.join (data.toList.map fun byte =>
    let digits := Nat.toDigits 16 byte.toNat
    String.ofList (if digits.length == 1 then '0' :: digits else digits))

/-- Encodings from the Python reference `s7commplus.vlq.encode_uint32_vlq`. -/
def uint32Vectors : List (UInt32 × String) := [
  (0, "00"),
  (1, "01"),
  (63, "3f"),
  (64, "40"),
  (127, "7f"),
  (128, "8100"),
  (129, "8101"),
  (255, "817f"),
  (256, "8200"),
  (16383, "ff7f"),
  (16384, "818000"),
  (2097151, "ffff7f"),
  (2097152, "81808000"),
  (268435455, "ffffff7f"),
  (268435456, "8180808000"),
  (305419896, "8191d1ac78"),
  (2147483648, "8880808000"),
  (4294967295, "8fffffff7f")
]

/-- Encodings from the Python reference `s7commplus.vlq.encode_uint64_vlq`. -/
def uint64Vectors : List (UInt64 × String) := [
  (0, "00"),
  (1, "01"),
  (127, "7f"),
  (128, "8100"),
  (4294967296, "9080808000"),
  (562949953421312, "8180808080808000"),
  (36028797018963968, "c080808080808000"),
  (72057594037927935, "ffffffffffffff7f"),
  (72057594037927936, "80c080808080808000"),
  (72057594037927937, "80c080808080808001"),
  (81985529216486895, "80c8e8d6bca6d7cdef"),
  (9223372036854775808, "c08080808080808000"),
  (18364758544493064720, "ffb797a9c3d9a8b210"),
  (18446744073709551615, "ffffffffffffffffff")
]

/-- Complete frames of the CPU 1214C V4.2.2 session (`fixtures/s7-1200-v4.2-sessionkey-session.json`),
    with the expected frame version. -/
def sessionFrames : List (String × FrameVersion × String) := [
  ("InitSSL (client-to-plc)", .v1,
    "7201001231000005b30000000000000000300000000072010000"),
  ("InitSSL (plc-to-client)", .v1,
    "7201001732000005a90000000034d180b3a08086b9ff890000000072010000"),
  ("CreateObject (client-to-plc)", .v1,
    "720100b031000004ca0000000100000120360000011d00040000000000a1000000d3821f0000a3816900150a7337636f6d6d706c7573a38221001513313a3a3a362e303a3a7337636f6d6d706c7573a3822800150a7337636f6d6d706c7573a38229001500a3822a00150a7337636f6d6d706c7573a3822b000401a3822c001280c3c901a3822d001500a1000000d3817f0000a38169001515537562736372697074696f6e436f6e7461696e6572a2a20000000072010000"),
  ("CreateObject (plc-to-client)", .v1,
    "720100c732000004ca00000001360002871b8742a100000120821f0000a3816900151330313a42443432364230393146303837333141a3822b00048280808002a3822d0015104f4d53502e52454c2e383038392e3231a3822f10021480a3f56a13349870b925847c376e602ae19f7f12a3823200170000013a823b00048400823c00048400823d00048480c200823e00048480c200823f00151b313b36455337203231342d31414734302d30584230203b56342e328240001505323b38323682410003000300a20000000072010000"),
  ("SetupSession (client-to-plc)", .v2,
    "7202017f3100000542000000020000039b340000039b02028e268232010017000007088e090004008e0a0002008e0b0017000007218e220005ded0cdb0c8fc90f31a8e23000482108e24000400008e0c0017000007218e220005f7c7d7c6a1dcf59a008e2300048482018e24000400008e0d0014008134addee1feb4000000010000000100000093f3af24b124dccb01010000000000001a73081f096b42bd100100000000000014aadf58e307658515a5dcca1cd066661b08ec98325959f4ad49113faed52c77b04b4e01fecee84826940d155f6b9223cad160c8b10e0859c73007bfb91096a178dcc66c32aabe93ebab9614f964a1694d1bda0ce3fcb8991f24badc75f96388a61e1656f8b723519b17051423d652aa9c883523be7eefc70e2d372106076e9da11b113f000200170000013a823b00048400823c00048400823d00048480c200823e00048480c200823f0015008240001505323b3832368241000300030000000004e88969001200000000896a001300896b0004000000000000000072020000"),
  ("SetupSession (plc-to-client)", .v2,
    "72020011320000054200000002340000000000000072020000"),
  ("request function 0x04F2 (client-to-plc)", .v3,
    "72030056206486002b9ebffacd6d57a9cdbfd8e35c148939e57da0d5a004f8cafabd99489c31000004f2000000030000039b340000039b018243000205000004e88969001200000000896a001300896b0004000000030000000072030000"),
  ("response function 0x04F2 (plc-to-client)", .v3,
    "7203003120350cd1c2eaada6250012bd211fbfb2bb259145af48af6cbb92e5038f6ba8fd2132000004f2000000033400060000000072030000"),
  ("request function 0x0586 (client-to-plc)", .v3,
    "7203005620cb140b58ff689c428ea20251eb24c981c29703abd1ac1a0de05511af2d288fa83100000586000000040000039b340000039b2004018e32000004e88969001200000000896a001300896b000400000001010000000072030000"),
  ("response function 0x0586 (plc-to-client)", .v3,
    "720300352066574bb4b605d94632cb8833889dbd625be28aabaed59fcff2fa00a655d74002320000058600000004340000000401050000000072030000"),
  ("request function 0x054C (client-to-plc)", .v3,
    "7203005d20dda029837a70713baf396bcb66f08f47ace0f3f4a73867c69981b9fa90969454310000054c000000050000039b340000000001070088d0b88001049376030001000004e88969001200000000896a001300896b00040000020000000072030000"),
  ("response function 0x054C (plc-to-client)", .v3,
    "7203003920430cfd040e13810b65eaa526dbdcd8c5f906f39c1563d080a2fbbb916fe3417a320000054c00000005340001001400012a0000070000000072030000"),
  ("request function 0x0542 (client-to-plc)", .v3,
    "7203006420bb06e260137ba55be658ec89a7a9a8c714e37a57aea3cea018d93fb74a6f73fa3100000542000000060000039b340000000001070088d0b8800104937603000101001400012a00000004e88969001200000000896a001300896b00040000020000000072030000")
]

/-- Encodings from the Python reference `s7commplus.vlq.encode_int32_vlq`. -/
def int32Vectors : List (Int × String) := [
  ((-2147483648), "f880808000"),
  ((-305419896), "feeeaed308"),
  ((-1048576), "ffc08000"),
  ((-8193), "ffbf7f"),
  ((-8192), "ffc000"),
  ((-65), "ff3f"),
  ((-64), "ff40"),
  ((-1), "7f"),
  (0, "00"),
  (1, "01"),
  (63, "3f"),
  (64, "8040"),
  (8191, "bf7f"),
  (8192, "80c000"),
  (1048576, "80c08000"),
  (305419896, "8191d1ac78"),
  (2147483647, "87ffffff7f")
]

/-- Encodings from the Python reference `s7commplus.vlq.encode_int64_vlq`. -/
def int64Vectors : List (Int × String) := [
  ((-9223372036854775808), "c08080808080808000"),
  ((-4611686018427387904), "e08080808080808000"),
  ((-81985529216486895), "ffb797a9c3d9a8b211"),
  ((-36028797018963969), "ffdfffffffffffffff"),
  ((-36028797018963968), "ffe080808080808000"),
  ((-2147483648), "f880808000"),
  ((-65), "ff3f"),
  ((-64), "ff40"),
  ((-1), "7f"),
  (0, "00"),
  (1, "01"),
  (63, "3f"),
  (64, "8040"),
  (2147483648, "8880808000"),
  (36028797018963967, "bfffffffffffff7f"),
  (36028797018963968, "80a080808080808000"),
  (72057594037927936, "80c080808080808000"),
  (81985529216486895, "80c8e8d6bca6d7cdef"),
  (4611686018427387904, "a08080808080808000"),
  (9223372036854775807, "bfffffffffffffffff")
]

/-- Encodings from the Python reference `s7commplus.codec.encode_pvalue_typed`. -/
def pvalueVectors : List (PValue × String) := [
  (.null, "0000"),
  (.bool 1, "000101"),
  (.usint 0xab, "0002ab"),
  (.uint 0x1234, "00031234"),
  (.udint 0x12345678, "00048191d1ac78"),
  (.ulint 0x1000000000000000, "0005888080808080808000"),
  (.sint 0xf0, "0006f0"),
  (.int 0xfffe, "0007fffe"),
  (.dint (Int32.ofInt (-100000)), "0008f9f260"),
  (.lint (Int64.ofInt (-1152921504606846976)), "0009f88080808080808000"),
  (.byte 0x7f, "000a7f"),
  (.word 0xbeef, "000bbeef"),
  (.dword 0xdeadbeef, "000cdeadbeef"),
  (.lword 0x0123456789abcdef, "000d0123456789abcdef"),
  (.real 0x3f800000, "000e3f800000"),
  (.lreal 0x400921fb54442d18, "000f400921fb54442d18"),
  (.timestamp 0x0123456789abcdef, "00100123456789abcdef"),
  (.timespan (Int64.ofInt (-5)), "00117b"),
  (.rid 0x8a0e0001, "00128a0e0001"),
  (.aid 2521, "00139359"),
  (.blob 0 (hexBytes "010203"), "00140003010203"),
  (.wstring (hexBytes "6869"), "0015026869")
]

/-- GetMultiVariables replies of a CPU 1512SP-1 FW V2.9 with failing items
    (`fixtures/s7-1500-v2.9-multiread-partial-failure.json`). -/
def partialFailureReplies : List (String × String) := [
  ("missing DB in the middle", "9089f0808082b480130100140002000a020000030014000442f6e6660002c08895b080e6a5fff4000a00000000"),
  ("offset past end", "9089f0808082b480130100140002000a030014000442f6e6660002c181d1d0808ba3ffc3000c00000000"),
  ("only failing", "9089f0808082b480130100000001c08895b080e6a5fff402c181d1d0808ba3ffc3000e00000000"),
  ("failing first", "9089f0808082b480130100000200140002000a0001c08895b080e6a5fff4001000000000")
]

/-- The lean-s7 dependency is usable: its cursor reads an S7CommPlus frame header. -/
def testFrameHeaderBytes : IO Unit := do
  let header := bytes #[protocolId, FrameVersion.v1.toByte, 0x00, 0x12]
  match Cursor.readUInt8 { data := header } with
  | .ok (id, cursor) =>
    check (id == 0x72) "protocol id"
    match cursor.readUInt8 with
    | .ok (version, cursor) =>
      check (FrameVersion.ofByte? version == some .v1) "frame version"
      match cursor.readUInt16BE with
      | .ok (length, _) => check (length == 0x12) "frame length"
      | .error _ => throw <| IO.userError "frame length read failed"
    | .error _ => throw <| IO.userError "frame version read failed"
  | .error _ => throw <| IO.userError "protocol id read failed"

def testFrameVersionBytes : IO Unit := do
  for version in [FrameVersion.v1, .v2, .v3, .systemEvent] do
    check (FrameVersion.ofByte? version.toByte == some version) s!"frame version {repr version}"
  check (FrameVersion.ofByte? 0x04 == none) "unknown frame version"

def decodesUInt32To (hex : String) (expected : UInt32) : Bool :=
  match Vlq.decodeUInt32 { data := hexBytes hex } with
  | .ok (value, next) => value == expected && next.offset == (hexBytes hex).size
  | .error _ => false

def rejectsUInt32 (hex : String) : Bool :=
  match Vlq.decodeUInt32 { data := hexBytes hex } with
  | .ok _ => false
  | .error _ => true

def testUInt32Vectors : IO Unit := do
  for (value, hex) in uint32Vectors do
    check (toHex (Vlq.encodeUInt32 value) == hex) s!"uint32 encoding of {value}: {toHex (Vlq.encodeUInt32 value)} != {hex}"
    check (decodesUInt32To hex value) s!"uint32 decoding of {hex}"

def testUInt32Leniency : IO Unit := do
  -- Overlong encodings: leading zero groups are accepted, as in the Python decoder.
  check (decodesUInt32To "8000" 0) "80 00 decodes to 0"
  check (decodesUInt32To "80807f" 127) "80 80 7f decodes to 127"
  check (decodesUInt32To "8fffffff7f" 0xffffffff) "five-byte maximum"
  -- Divergences from Python: out-of-range values and a final continuation flag.
  check (rejectsUInt32 "ffffffff7f") "2^35 - 1 is rejected (Python returns it)"
  check (rejectsUInt32 "8080808080") "continuation on the fifth byte is rejected (Python returns 0)"
  check (rejectsUInt32 "80") "truncated VLQ is rejected"
  check (rejectsUInt32 "") "empty input is rejected"

def testUInt64Vectors : IO Unit := do
  for (value, hex) in uint64Vectors do
    check (toHex (Vlq.encodeUInt64 value) == hex) s!"uint64 encoding of {value}: {toHex (Vlq.encodeUInt64 value)} != {hex}"
    match Vlq.decodeUInt64 { data := hexBytes hex } with
    | .ok (decoded, next) =>
      check (decoded == value && next.offset == (hexBytes hex).size) s!"uint64 decoding of {hex}"
    | .error _ => throw <| IO.userError s!"uint64 decoding of {hex} failed"

def testInt32Vectors : IO Unit := do
  for (value, hex) in int32Vectors do
    let typed := Int32.ofInt value
    check (toHex (Vlq.encodeInt32 typed) == hex) s!"int32 encoding of {value}: {toHex (Vlq.encodeInt32 typed)} != {hex}"
    match Vlq.decodeInt32 { data := hexBytes hex } with
    | .ok (decoded, next) =>
      check (decoded.toInt == value && next.offset == (hexBytes hex).size) s!"int32 decoding of {hex}"
    | .error _ => throw <| IO.userError s!"int32 decoding of {hex} failed"

def decodesInt32To (hex : String) (expected : Int) : Bool :=
  match Vlq.decodeInt32 { data := hexBytes hex } with
  | .ok (value, next) => value.toInt == expected && next.offset == (hexBytes hex).size
  | .error _ => false

def testInt32Leniency : IO Unit := do
  -- Python encodes -64 as ff 40; the single byte 40 decodes to the same value.
  check (decodesInt32To "40" (-64)) "40 decodes to -64"
  check (decodesInt32To "ff40" (-64)) "ff 40 decodes to -64"
  check (decodesInt32To "803f" 63) "sign extension of a positive value"
  -- Divergence from Python: decode_int32_vlq returns 4294967295 for this input.
  check (Vlq.decodeInt32 { data := hexBytes "8fffffff7f" } matches .error _) "out-of-range int32"
  check (Vlq.decodeInt32 { data := hexBytes "8080808080" } matches .error _) "continuation on the fifth byte"

def testInt64Vectors : IO Unit := do
  for (value, hex) in int64Vectors do
    let typed := Int64.ofInt value
    check (toHex (Vlq.encodeInt64 typed) == hex) s!"int64 encoding of {value}: {toHex (Vlq.encodeInt64 typed)} != {hex}"
    match Vlq.decodeInt64 { data := hexBytes hex } with
    | .ok (decoded, next) =>
      check (decoded.toInt == value && next.offset == (hexBytes hex).size) s!"int64 decoding of {hex}"
    | .error _ => throw <| IO.userError s!"int64 decoding of {hex} failed"

def testPValueVectors : IO Unit := do
  for (value, hex) in pvalueVectors do
    check (toHex value.encode == hex) s!"PValue encoding {toHex value.encode} != {hex}"
    match decodePValue { data := hexBytes hex } with
    | .ok (decoded, next) =>
      check (decoded == value && next.offset == (hexBytes hex).size) s!"PValue decoding of {hex}"
    | .error _ => throw <| IO.userError s!"PValue decoding of {hex} failed"

def testPValueRejections : IO Unit := do
  -- Arrays (flags 0x10) are not accepted yet.
  check (decodePValue { data := hexBytes "100201ab" } matches .error _) "array flags"
  -- VARIANT, STRUCT and S7STRING are not scalar values here.
  check (decodePValue { data := hexBytes "0016" } matches .error _) "VARIANT"
  check (decodePValue { data := hexBytes "0017" } matches .error _) "STRUCT"
  check (decodePValue { data := hexBytes "0019" } matches .error _) "S7STRING"
  -- Truncated fixed-width and length-prefixed values.
  check (decodePValue { data := hexBytes "000c0102" } matches .error _) "truncated DWORD"
  check (decodePValue { data := hexBytes "0015056869" } matches .error _) "truncated WSTRING"

/-- The object trees of the CPU 1214C CreateObject request and reply decode, and
    re-encode to exactly the bytes they were read from. -/
def testCreateObjectTrees : IO Unit := do
  for (label, start, expected) in [("CreateObject (client-to-plc)", 25, 13),
      ("CreateObject (plc-to-client)", 16, 15)] do
    let some (_, _, hex) := sessionFrames.find? (fun (l, _, _) => l == label)
      | throw <| IO.userError s!"{label}: missing fixture"
    match decodeFrame (hexBytes hex) with
    | .error error => throw <| IO.userError s!"{label}: {repr error}"
    | .ok (_, data) =>
      match decodeTree { data, offset := start } with
      | .error error => throw <| IO.userError s!"{label}: tree: {repr error}"
      | .ok (items, next) =>
        check (items.length == expected) s!"{label}: {items.length} items"
        check (encodeItems items == data.extract start next.offset) s!"{label}: re-encoding differs"
        check (data.extract next.offset data.size == bytes #[0, 0, 0, 0]) s!"{label}: trailing bytes"

/-- The message under each fixture frame: the integrity envelope comes off V3 frames,
    then the header decodes with the function and sequence number of the capture. -/
def testSessionHeaders : IO Unit := do
  -- (function, sequence) in capture order; requests and responses alternate. The PLC
  -- answers InitSSL with the ERROR2 function 0x05a9: this session runs without TLS.
  let expected : List (UInt16 × UInt16) := [(0x05b3, 0), (0x05a9, 0), (0x04ca, 1), (0x04ca, 1),
    (0x0542, 2), (0x0542, 2), (0x04f2, 3), (0x04f2, 3), (0x0586, 4), (0x0586, 4),
    (0x054c, 5), (0x054c, 5), (0x0542, 6)]
  for ((label, version, hex), (function, sequence)) in sessionFrames.zip expected do
    match decodeFrame (hexBytes hex) with
    | .error error => throw <| IO.userError s!"{label}: {repr error}"
    | .ok (_, data) =>
      let message ← if version == .v3 then
          match decodeIntegrityEnvelope data with
          | .ok (digest, message) =>
            check (digest.size == 32) s!"{label}: digest size"
            check (encodeIntegrityEnvelope digest message == data) s!"{label}: envelope re-encoding"
            pure message
          | .error error => throw <| IO.userError s!"{label}: envelope: {repr error}"
        else pure data
      if label.endsWith "(client-to-plc)" then
        match decodeRequestHeader { data := message } with
        | .ok (header, next) =>
          check (header.function == function && header.sequence == sequence && next.offset == 14)
            s!"{label}: request header {repr header}"
        | .error error => throw <| IO.userError s!"{label}: {repr error}"
      else
        match decodeResponseHeader { data := message } with
        | .ok (header, next) =>
          check (header.function == function && header.sequence == sequence && next.offset == 10)
            s!"{label}: response header {repr header}"
        | .error error => throw <| IO.userError s!"{label}: {repr error}"

/-- The message of a fixture frame, after the integrity envelope of V3 frames. -/
def fixtureMessage (label : String) : IO ByteArray := do
  let some (_, version, hex) := sessionFrames.find? (fun (l, _, _) => l == label)
    | throw <| IO.userError s!"{label}: missing fixture"
  match decodeFrame (hexBytes hex) with
  | .error error => throw <| IO.userError s!"{label}: {repr error}"
  | .ok (_, data) =>
    if version == .v3 then
      match decodeIntegrityEnvelope data with
      | .ok (_, message) => pure message
      | .error error => throw <| IO.userError s!"{label}: {repr error}"
    else pure data

/-- The CPU 1214C read of one byte of DB1: the request payload decodes to that address
    with IntegrityId 2 and re-encodes exactly; the reply decodes to the value 42. -/
def testFixtureRead : IO Unit := do
  let request ← fixtureMessage "request function 0x054C (client-to-plc)"
  let payload := request.extract 14 request.size
  match decodeReadRequest .vlq true payload with
  | .error error => throw <| IO.userError s!"read request: {repr error}"
  | .ok (decoded, integrityId) =>
    check (decoded.addresses == [ItemAddress.db 1 0 1]) s!"read request addresses {repr decoded.addresses}"
    check (integrityId == some 2) "read request IntegrityId"
    check (decoded.encode integrityId == payload) "read request re-encoding"
  let reply ← fixtureMessage "response function 0x054C (plc-to-client)"
  let replyPayload := reply.extract 10 reply.size
  match decodeReadReply { data := replyPayload } with
  | .error error => throw <| IO.userError s!"read reply: {repr error}"
  | .ok (decoded, next) =>
    check (decoded.returnValue == 0) "read reply return value"
    check (decoded.values == [(1, .scalar (.blob 0 (bytes #[42])))]) "read reply value"
    check (decoded.errors.isEmpty) "read reply errors"
    check (decoded.encode == replyPayload.extract 0 next.offset) "read reply re-encoding"
    check (replyPayload.extract next.offset replyPayload.size == hexBytes "0700000000")
      "IntegrityId and fill after the reply"

/-- The S7-1500 partial-failure replies decode with their nonzero return value, the
    values of the good items and the errors of the failing ones, and re-encode to
    exactly the bytes read. -/
def testPartialFailureReplies : IO Unit := do
  -- (value item numbers, error item numbers) per reply, in fixture order. A missing DB
  -- is answered twice, with a NULL value and an error (gijzelaerr/s7commplus#130).
  let expected : List (List UInt32 × List UInt32) :=
    [([1, 2, 3], [2]), ([1, 3], [2]), ([1], [1, 2]), ([1, 2], [1])]
  for ((label, hex), (valueItems, errorItems)) in partialFailureReplies.zip expected do
    let payload := hexBytes hex
    match decodeReadReply { data := payload } with
    | .error error => throw <| IO.userError s!"{label}: {repr error}"
    | .ok (decoded, next) =>
      check (decoded.returnValue == 0x20278000009A0013) s!"{label}: return value"
      check (decoded.values.map Prod.fst == valueItems) s!"{label}: value items {decoded.values.map Prod.fst}"
      check (decoded.errors.map Prod.fst == errorItems) s!"{label}: error items {decoded.errors.map Prod.fst}"
      check (decoded.encode == payload.extract 0 next.offset) s!"{label}: re-encoding"

/-- The CPU 1214C write of one byte to DB1 (the one the PLC rejected): the request
    payload decodes to that address and value with IntegrityId 2, and re-encodes. -/
def testFixtureWrite : IO Unit := do
  let request ← fixtureMessage "request function 0x0542 (client-to-plc)"
  let payload := request.extract 14 request.size
  match decodeWriteRequest .vlq true payload with
  | .error error => throw <| IO.userError s!"write request: {repr error}"
  | .ok (decoded, integrityId) =>
    check (decoded.addresses == [ItemAddress.db 1 0 1]) "write request addresses"
    check (decoded.values == [.scalar (.blob 0 (bytes #[42]))]) "write request value"
    check (integrityId == some 2) "write request IntegrityId"
    check (decoded.encode integrityId == payload) "write request re-encoding"

def resultShape (results : List ItemResult) : List Bool :=
  results.map fun result => match result with
    | .ok _ => true
    | .error _ => false

/-- Per-item results of the S7-1500 partial-failure replies: the good items keep their
    values despite the nonzero return value (#129), and a missing DB is one error (#130). -/
def testPartialFailureResults : IO Unit := do
  let expected : List (Nat × List Bool) :=
    [(3, [true, false, true]), (3, [true, false, true]), (2, [false, false]), (2, [false, true])]
  for ((label, hex), (count, shape)) in partialFailureReplies.zip expected do
    match decodeReadReply { data := hexBytes hex } with
    | .error error => throw <| IO.userError s!"{label}: {repr error}"
    | .ok (reply, _) =>
      match reply.results count with
      | .ok results => check (resultShape results == shape) s!"{label}: results {resultShape results}"
      | .error error => throw <| IO.userError s!"{label}: results: {repr error}"
  -- The same reply checked against the wrong item count is refused.
  match partialFailureReplies.head? with
  | none => pure ()
  | some (_, hex) =>
    match decodeReadReply { data := hexBytes hex } with
    | .ok (reply, _) => check (reply.results 2 matches .error _) "item outside the request"
    | .error _ => throw <| IO.userError "decode"
  -- A value and an error for the same item, with a non-NULL value, is refused.
  let both : ReadReply := { returnValue := 0, values := [(1, .scalar (.usint 1))], errors := [(1, 5)] }
  check (both.results 1 matches .error _) "value and error for one item"
  -- An unanswered item is refused.
  let unanswered : ReadReply := { returnValue := 0, values := [(1, .scalar (.usint 1))], errors := [] }
  check (unanswered.results 2 matches .error _) "unanswered item"

/-- The session's request frames are byte for byte those of the Python client: the
    CreateObject of the CPU 1214C capture, and the plain V1 conversation with the Python
    emulator (session id 1). -/
def testSessionRequests : IO Unit := do
  let frameOf (session : Session) (request : Request) : IO ByteArray :=
    match session.send request with
    | some (frame, _, _) => pure frame
    | none => throw <| IO.userError "request not allowed in this phase"
  check (toHex (← frameOf Session.initial .initSsl) ==
    "72010012310000 05b300000000000000003000000000720100 00".replace " " "") "InitSSL frame"
  let some (_, _, createHex) := sessionFrames.find? (fun (l, _, _) => l == "CreateObject (client-to-plc)")
    | throw <| IO.userError "missing CreateObject fixture"
  let probed : Session := { Session.initial with phase := .sslProbed, sequence := 1 }
  check (toHex (← frameOf probed .createObject) == createHex) "CreateObject frame"
  let created : Session := { phase := .created, sessionId := 1, sequence := 2 }
  check (toHex (← frameOf created (.setupSession (hexBytes "000401"))) ==
    "72020038310000054200000002000000013400000001010182320100040100000004e88969001200000000896a0013" ++
    "00896b000400000000000000007202" ++ "0000") "SetupSession frame"
  let ready (sequence : UInt16) : Session := { phase := .ready, sessionId := 1, sequence }
  let readRequest : ReadRequest := { addresses := [ItemAddress.db 1 2 4], form := .fixed, keyQualifier := 0 }
  check (toHex (← frameOf (ready 4) (.read readRequest)) ==
    "7201003d310000054c00000004000000013400000000010700 88d0b88001049376030204000004e88969001200000000896a001300896b000400000000000000007201 0000".replace " " "")
    "read frame"
  let writeRequest : WriteRequest :=
    { addresses := [ItemAddress.db 1 0 2], values := [.scalar (.blob 0 (hexBytes "aabb"))], form := .fixed, keyQualifier := 0 }
  check (toHex (← frameOf (ready 5) (.write writeRequest)) ==
    "72010045310000054200000005000000013400000000010700 88d0b88001049376030002010014000 2aabb00000004e88969001200000000896a001300896b000400000000000000007201 0000".replace " " "")
    "write frame"
  check (toHex (← frameOf (ready 7) (.explore ObjectId.thePlcProgram
      [AttributeId.objectVariableTypeName, AttributeId.blockNumber])) ==
    "72010021310000 04bb000000070000000134000000030001010000028169935900000000007201 0000".replace " " "")
    "explore frame"
  -- Requests out of phase are refused.
  check (Session.initial.send .createObject).isNone "CreateObject before InitSSL"
  check (created.send (.read { addresses := [], form := .fixed, keyQualifier := 0 })).isNone
    "read before SetupSession"
  -- The emulator's CreateObject reply: session id 1 and the last attribute 306.
  match decodeFrame (hexBytes "7201002c32000004ca0000000100000101a100000001000000a38231000401a38232000201a38232000401a20000000072010000") with
  | .error error => throw <| IO.userError s!"emulator CreateObject frame: {repr error}"
  | .ok (_, data) =>
    match decodeCreateObjectReply (data.extract 10 data.size) with
    | .error error => throw <| IO.userError s!"emulator CreateObject reply: {repr error}"
    | .ok reply =>
      check (reply.sessionId == 1) "emulator session id"
      check (toHex reply.serverSessionVersion == "000401") "emulator ServerSessionVersion"

def testSessionFrames : IO Unit := do
  for (label, version, hex) in sessionFrames do
    let frame := hexBytes hex
    match decodeFrame frame with
    | .ok (decodedVersion, data) =>
      check (decodedVersion == version) s!"{label}: frame version"
      check (encodeFrame decodedVersion data == frame) s!"{label}: re-encoding differs"
    | .error error => throw <| IO.userError s!"{label}: {repr error}"

def testFrameRejections : IO Unit := do
  let good := hexBytes "720100043100000072010000"
  check (decodeFrame good matches .ok _) "minimal frame"
  check (decodeFrame (hexBytes "730100043100000072010000") matches .error _) "wrong protocol id"
  check (decodeFrame (hexBytes "720400043100000072040000") matches .error _) "unknown version"
  check (decodeFrame (hexBytes "720100043100000072020000") matches .error _) "trailer version differs"
  check (decodeFrame (hexBytes "720100043100000072010001") matches .error _) "nonzero trailer word"
  check (decodeFrame (hexBytes "72010004310000007201000000") matches .error _) "trailing byte"
  check (decodeFrame (hexBytes "7201000431000000720100") matches .error _) "truncated trailer"

/-- The Python emulator's split of the bytes 0..19 with `max_response_pdu=8`
    (`send_app_frame`): three fragments, the trailer after the last. -/
def emulatorSplit : String :=
  "7201000800010203040506077201000808090a0b0c0d0e0f720100041011121372010000"

def testFragments : IO Unit := do
  let data := (List.range 20).map UInt8.ofNat |>.toByteArray
  match reassemble (hexBytes emulatorSplit) with
  | .ok (version, joined) =>
    check (version == .v1 && joined == data) "reassembled emulator split"
  | .error error => throw <| IO.userError s!"emulator split rejected: {reprStr error}"
  check (fragmentsComplete (hexBytes emulatorSplit)) "complete split"
  check (encodeFragments .v1 (splitData 8 data) == hexBytes emulatorSplit) "splitData matches the emulator"
  match decodeFragments (hexBytes emulatorSplit) with
  | .ok (_, pieces) => check (pieces.map ByteArray.size == [8, 8, 4]) "fragment sizes"
  | .error _ => throw <| IO.userError "fragments rejected"
  -- Every proper prefix is incomplete, so a receiver waits for more data.
  for cut in [0, 3, 4, 12, 13, 24, 32, 35] do
    let head := (hexBytes emulatorSplit).extract 0 cut
    check (!fragmentsComplete head) s!"prefix of {cut} bytes is incomplete"
    check (reassemble head).toBool.not s!"prefix of {cut} bytes rejected"
  let rejected : List (String × String) := [
    ("trailing bytes", emulatorSplit ++ "00"),
    ("second fragment changes version",
      "72010008000102030405060772020008" ++ "08090a0b0c0d0e0f720100041011121372010000"),
    ("empty fragment before the last", "72010000" ++ "7201000400010203" ++ "72010000"),
    ("trailer with the wrong version", "720100040001020372020000"),
    ("no protocol id on the second fragment",
      "72010008000102030405060773010008" ++ "08090a0b0c0d0e0f72010000")]
  for (label, hex) in rejected do
    check (reassemble (hexBytes hex)).toBool.not s!"{label} rejected"
  -- A complete frame is a message of one fragment.
  for (label, _, hex) in sessionFrames do
    match decodeFrame (hexBytes hex), reassemble (hexBytes hex) with
    | .ok frame, .ok message => check (frame == message) s!"{label}: frame and reassembly agree"
    | _, _ => throw <| IO.userError s!"{label}: frame or reassembly rejected"

/-- A toy MAC for the framing tests: a 64-bit polynomial hash spread over 32 bytes.
    It is order-sensitive but not secure; the real MAC is HMAC-SHA256 (decision 3). -/
def toyMac : Mac where
  tag message :=
    let hash := message.foldl (fun (acc : UInt64) byte => acc * 1099511628211 + byte.toUInt64) 14695981039346656037
    ((List.range 32).map fun i => (hash >>> (UInt64.ofNat ((i % 8) * 8))).toUInt8 + UInt8.ofNat i).toByteArray
  tag_size message := by simp

def flipByte (data : ByteArray) (position : Nat) : ByteArray :=
  data.set! position (data.get! position ^^^ 0x01)

def testIntegrity : IO Unit := do
  let message := hexBytes "31000004f2000000050000000134000000"
  let sealed := sealV3 toyMac message
  check (match openV3 toyMac sealed with | .ok m => m == message | .error _ => false) "V3 round trip"
  check (sealed.extract 0 2 == bytes #[0x72, 0x03] && sealed[4]! == 0x20) "V3 frame and envelope header"
  -- Any changed byte of the digest or message is refused.
  for position in [5, 20, 36, 37, 40, sealed.size - 5] do
    check (openV3 toyMac (flipByte sealed position)).toBool.not s!"V3 frame with byte {position} changed refused"
  check (openV3 toyMac (encodeFrame .v1 (encodeIntegrityEnvelope (toyMac.tag message) message))).toBool.not
    "V1 frame refused"
  -- Fragmented responses under both chains.
  let pieces := splitData 8 ((List.range 20).map UInt8.ofNat |>.toByteArray)
  let whole := joinFragments pieces
  for (label, sealedPieces, opened, reordered) in [
      ("independent", sealFragments (.independent toyMac) pieces,
        openFragments (.independent toyMac), sealFragments (.independent toyMac) pieces.reverse),
      ("feed-forward", sealFragments (.feedForward toyMac) pieces,
        openFragments (.feedForward toyMac), sealFragments (.feedForward toyMac) pieces.reverse)] do
    check (match opened sealedPieces with | .ok d => d == whole | .error _ => false) s!"{label}: round trip"
    check (opened (flipByte sealedPieces 50)).toBool.not s!"{label}: changed fragment refused"
    check (match opened reordered with | .ok d => d != whole | .error _ => true) s!"{label}: reordering changes the data"
  -- Under feed-forward, a fragment taken out of its chain is refused.
  let ffSealed := sealFragments (.feedForward toyMac) pieces
  match decodeFragments ffSealed with
  | .ok (_, envelopes) =>
    let spliced := encodeFragments .v3 [envelopes[0]!, envelopes[2]!]
    check (openFragments (.feedForward toyMac) spliced).toBool.not "feed-forward: dropped fragment refused"
    let swapped := encodeFragments .v3 [envelopes[0]!, envelopes[2]!, envelopes[1]!]
    check (openFragments (.feedForward toyMac) swapped).toBool.not "feed-forward: swapped fragments refused"
  | .error _ => throw <| IO.userError "feed-forward fragments rejected"

def testIntegrityIds : IO Unit := do
  -- Reads and writes step separate counters.
  let functions : List UInt16 := [0x054c, 0x0542, 0x054c, 0x04bb, 0x04f2, 0x0586]
  let (ids, counters) := ({} : IntegrityCounters).run functions
  check (ids.map (·.2) == [0, 0, 1, 2, 1, 3]) s!"IntegrityIds {ids.map (·.2)}"
  check (counters == { read := 4, write := 2 }) "counters after the run"
  -- The counters wrap modulo 2^32.
  let (id, wrapped) := ({ read := 0xffffffff } : IntegrityCounters).next 0x054c
  check (id == 0xffffffff && wrapped.read == 0) "read counter wraps"
  -- The read and write requests of the CPU 1214C session carry their id before the fill.
  let request ← fixtureMessage "request function 0x054C (client-to-plc)"
  let payload := request.extract 14 request.size
  match decodeReadRequest .vlq true payload with
  | .ok (decoded, some id) =>
    check (insertIntegrityId (decoded.encode none) 4 id == payload) "read request IntegrityId placement"
  | _ => throw <| IO.userError "read request"
  -- Its GetMultiVariables reply carries IntegrityId 7 after the body, before four fill bytes.
  let reply ← fixtureMessage "response function 0x054C (plc-to-client)"
  let replyPayload := reply.extract 10 reply.size
  match decodeReadReply { data := replyPayload } with
  | .ok (_, next) =>
    check (match decodeTrailingIntegrityId 4 next with | .ok id => id == 7 | .error _ => false)
      "trailing IntegrityId of the read reply"
    check (decodeTrailingIntegrityId 3 next).toBool.not "wrong fill length refused"
  | .error _ => throw <| IO.userError "read reply"
  match decodeLeadingIntegrityId (hexBytes "8100aa") with
  | .ok (id, rest) => check (id == 128 && rest == bytes #[0xaa]) "leading IntegrityId"
  | .error _ => throw <| IO.userError "leading IntegrityId"

/-- `hashlib.sha256` of the bytes `(7i + 3) mod 256` for each length. -/
def sha256Vectors : List (Nat × String) := [
  (0, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
  (1, "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5"),
  (3, "6ab0dba1f4f1dfbb37b4f9eeb092c09fca4900ad32bdcd147d8dde35d6c87c35"),
  (55, "e7313d333c272e639f790978283f9eb392e843d0f29b7016828bb1daa4aac70b"),
  (56, "4324d65f3c103567f5589c710bc08f8523f929a9272e3af36fc968e52abc6c27"),
  (57, "35df609437dcfea3279283ab79fd554e2bf78f8f7ae2de532d8ee300b09e8f73"),
  (63, "81c80242132f230c3bd41b3e63bbcff16107339549214a99614ff26664625055"),
  (64, "39e3d7b6b5d075d37d053ad89b24b41bef4f3c29760c84447cab3f3be1882241"),
  (65, "aacca6ff74fdbb296d165a45cecfa04e5127bc008770fbbdd48006f2d2fae95e"),
  (119, "9ce7368e4daf32341631b492e80359dc9f594b48453cd0dd5bf0b19279cc177e"),
  (120, "7836b787757e95e58b3ca5aec90b1b004e8deba1e50e9675af9cabf1a13a04b5"),
  (127, "a8d23e75d936f303d248888d9b165ee543f4cbafcad3c9dd2a79bd84faa11d07"),
  (128, "d2742f1f4ac6bb7ca2b239ee18402ba8b3f9f8e652d2a72973c2b9ba11c08cf6"),
  (129, "307f8fc2c1622b92762e818d39a185d4d667ad49a4b07ceae1f4afa008a93ec4"),
  (1000, "1e9bc38cbf860b9ec31918b065f9b52476c549a782e0e7990bed8ce3868d2371"),
  (4097, "225270fa091dc75bf959a0e3bbcb897fc3ae8e7fa128ae1394cf5614e15505f5")]

/-- `hmac.new(key, data, hashlib.sha256)` with key bytes `(13i + 1) mod 256`: key
    length, data length, tag. -/
def hmacVectors : List (Nat × Nat × String) := [
  (0, 0, "b613679a0814d9ec772f95d778c35fc5ff1697c493715653c6c712144292c5ad"),
  (0, 9, "e124f55f3d07e04717ad7b7db675dbb35ea4fa501b48e9880d6239c0a6899199"),
  (0, 50, "509fa3ceb425b0a43e4e4605364b37201bffc0df9db6af17d8a688bfd31232b9"),
  (0, 200, "bac72a73f232035f31901655f8a5d717056c6e6f02be452ebd700bc1efc44e2f"),
  (1, 0, "2f8738164025afdddbc18665c6e8f37de9498db7fd194873c61ee30c22192a9a"),
  (1, 9, "e2463d8ae37d307f71448a9269ea15f673253aa32343fcc426f544fde86aef9f"),
  (1, 50, "b2347d2d14e0db92428e2603f1eb2daaf4fe46e30152fbe7596bb94dcea81830"),
  (1, 200, "8219a0e1d0344387feb84030c33120d4b547b4b4b933f25b578419b5f691af9b"),
  (20, 0, "758f010fedfb3115e9fc9874376a84d2934c45c3063f4c3fab08d314d01928f7"),
  (20, 9, "9d1f59d932f10f44dd58c2f286ef94c23c4c7c4cf04127c6b72e4121080cc5a5"),
  (20, 50, "2d3b1fbb64e96bcb880ea373bee4676db84986feb6e6f8c4c14964807c001317"),
  (20, 200, "bd4ce02f47c48ccb088224ace8a7188366da31e3639994a1fb1f503601c42b67"),
  (24, 0, "5129bd5a8224b15de4b2a36505f392c21e37e9ffbfa3a229d20c46f0b0bf3938"),
  (24, 9, "c078ec0681ae35a4f4e53e425474d0b236dbc9a2ef94f04316e3ed343f370e2a"),
  (24, 50, "05bdbb71c5aff04aa9889c85e56b3252d8f335e2bb6441e3ce96e29cc478b5c3"),
  (24, 200, "7e84eedbefb78445e4b92b5a581d0f2fbcf7283103fc814ac6757d05a162f8b2"),
  (32, 0, "cdb708c9bfa0038fba5a6852bbadf0371841c2671f7099d522774b649e2b76b5"),
  (32, 9, "b8b7113ca0c88958f8ced4ab4a0317eb991697a8e12e61d37a7c1c3ffbed656c"),
  (32, 50, "599500521c6072a46642a8584848122da0fd505edc05b58f19df6685b8785d8e"),
  (32, 200, "7a50539e45ce1eb34422f27845e35168c8bcabf4b37c5c64c560a9d44d2ae2a9"),
  (64, 0, "0efe5d996e675745a5070d8bb99b04f6746651c3a5e576e8d208ef599ea07c8a"),
  (64, 9, "2685546ea9be0030a5228b7916ab8c43b4058abf795332b8688bd8a303640c9d"),
  (64, 50, "2bb74f06e144e3d005e80db06f249e0a6dff0ae0afb0f50d9bf4a1763566d4a1"),
  (64, 200, "d232dd37f1941d67ade5c2262346bfe9f1962506ad64ce786f4782d96defebe2"),
  (65, 0, "0dc2b3e7b71039add7054f550b7815587ce8097d308e7922c4cbdb90d8d9ab8e"),
  (65, 9, "e6fe26157f83986877fd67659c5d00d1980f42cc4610bbf73477ae1b21ed5402"),
  (65, 50, "b7bfb090e4bb5ca0fa577759b79b96fdffe081739971bbcc0da2ee585ea9340e"),
  (65, 200, "ded968ce3da7484c9efc09be99e613a14ca5c161dd93db054364dcfaf8b6d585"),
  (131, 0, "66382efb3e4e2275d30239770268cff75aa1d9dc6ac2ba77912d2cb51eece9fe"),
  (131, 9, "22294edf0980125a56995add842fffe78e74a0fc66fddfd27cafd448b179a06d"),
  (131, 50, "ace5f8657a3b02599a5d4a2330f587a480bfba2331ea1db9216329a7bb51ac11"),
  (131, 200, "2e2ea52836d230540424956442be701b2a3ebae941052195ad19e6dcf36080fb")]

def vectorData (length : Nat) : ByteArray :=
  ((List.range length).map fun i => UInt8.ofNat ((i * 7 + 3) % 256)).toByteArray

def vectorKey (length : Nat) : ByteArray :=
  ((List.range length).map fun i => UInt8.ofNat ((i * 13 + 1) % 256)).toByteArray

def testSha256 : IO Unit := do
  for (length, hex) in sha256Vectors do
    check (toHex (Sha256.hash (vectorData length)) == hex) s!"SHA-256 of {length} bytes"
  for (keyLength, length, hex) in hmacVectors do
    check (toHex (Hmac.sha256 (vectorKey keyLength) (vectorData length)) == hex)
      s!"HMAC-SHA256 with a {keyLength}-byte key over {length} bytes"
  -- RFC 4231 test case 2.
  check (toHex (Hmac.sha256 "Jefe".toUTF8 "what do ya want for nothing?".toUTF8) ==
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843") "RFC 4231 case 2"

/-- A 40-byte response split into 16-byte fragments under one session key, sealed in
    each dialect: state-resume by the emulator's `_protect_v3_fragments`, the others
    as the Python `FragmentHMACVerifier` checks them. The verifier accepts all three. -/
def dialectVectors : List (String × String) := [
  ("state-resume", "72030031200e321eca8a29d4e737788060959a94d26632a19c5ab0ea2a5e6e13d63b9cb572030a11181f262d343b424950575e656c7203003120c87325f19a252abef1d116f544ae6a8a86ddc4c02f01b8e014b4109ee0adf6e5737a81888f969da4abb2b9c0c7ced5dc72030029208e145dac1e40106573e55d4d4aa5f65457f5891ba6637575692f8ef876fda855e3eaf1f8ff060d1472030000"),
  ("independent", "72030031200e321eca8a29d4e737788060959a94d26632a19c5ab0ea2a5e6e13d63b9cb572030a11181f262d343b424950575e656c72030031203b8655580e14316c5619e0fc190c36d3f6fc6843610c901768567cbca41daa25737a81888f969da4abb2b9c0c7ced5dc720300292025b061a9cc376479ce1c3db251f7dd473f5b5103cdee0cf8828fd688b15dcbcee3eaf1f8ff060d1472030000"),
  ("feed-forward", "72030031200e321eca8a29d4e737788060959a94d26632a19c5ab0ea2a5e6e13d63b9cb572030a11181f262d343b424950575e656c7203003120279f34b2ca8ae57f27d3bc3f23360af16728952637caba6e8759ae95aaf0faee737a81888f969da4abb2b9c0c7ced5dc7203002920f8d2c9ab9fffa45de31742ef2a91f564b1d614d1d8eca8ff00376a2a16ac0d26e3eaf1f8ff060d1472030000")]

def testHmacDialects : IO Unit := do
  let key := ((List.range 32).map fun i => UInt8.ofNat ((i * 5 + 11) % 256)).toByteArray
  let data := vectorData 40
  let pieces := splitData 16 data
  let sealed : List (String × ByteArray × (ByteArray → Bool)) := [
    ("state-resume", sealFragments (.stateResume key) pieces,
      fun m => match openFragments (.stateResume key) m with | .ok d => d == data | .error _ => false),
    ("independent", sealFragments (.independent (.hmacSha256 key)) pieces,
      fun m => match openFragments (.independent (.hmacSha256 key)) m with | .ok d => d == data | .error _ => false),
    ("feed-forward", sealFragments (.feedForward (.hmacSha256 key)) pieces,
      fun m => match openFragments (.feedForward (.hmacSha256 key)) m with | .ok d => d == data | .error _ => false)]
  for ((label, mine, opens), (label', hex)) in sealed.zip dialectVectors do
    check (label == label') "dialect order"
    check (toHex mine == hex) s!"{label}: sealed like the Python implementation"
    check (opens (hexBytes hex)) s!"{label}: Python's frames open"
    check (!opens (flipByte (hexBytes hex) 60)) s!"{label}: changed byte refused"
  -- The state-resume frames are not valid in another dialect.
  check (openFragments (.independent (.hmacSha256 key)) (hexBytes dialectVectors[0]!.2)).toBool.not
    "state-resume frames refused as independent"
  -- A single V3 frame with HMAC-SHA256.
  let message := hexBytes "31000004f2000000050000000134000000"
  check (openV3 (.hmacSha256 key) (sealV3 (.hmacSha256 key) message) |>.toBool) "HMAC-SHA256 V3 frame"

/-- The ISO data units of the s7commplus client's SessionKey session against its
    emulator (`fixtures/emulator-sessionkey-session.json`). -/
def emulatorKeyFrames : List (String × String) := [
  ("client-to-plc", "7201001231000005b30000000000000000300000000072010000"),
  ("plc-to-client", "7201000f32000005b30000000000000000000072010000"),
  ("client-to-plc", "720100b031000004ca0000000100000120360000011d00040000000000a1000000d3821f0000a3816900150a7337636f6d6d706c7573a38221001513313a3a3a362e303a3a7337636f6d6d706c7573a3822800150a7337636f6d6d706c7573a38229001500a3822a00150a7337636f6d6d706c7573a3822b000401a3822c001280c3c901a3822d001500a1000000d3817f0000a38169001515537562736372697074696f6e436f6e7461696e6572a2a20000000072010000"),
  ("plc-to-client", "7201008232000004ca0000000100000101a100000001000000a38231000401a3816900151330313a42443432364230393146303837333141a3822f100214000102030405060708090a0b0c0d0e0f10111213a3823200170000013a823b000401823f00151b313b36455337203231352d31414734302d30584230203b56342e3200a20000000072010000"),
  ("client-to-plc", "7202015831000005420000000200000001340000000102028e268232010017000007088e090004008e0a0002008e0b0017000007218e220005ded0cdb0c8fc90f31a8e23000482108e24000400008e0c0017000007218e220005cbe68592e2ccf08dad8e2300048482018e24000400008e0d0014008134000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200170000013a823b000401823f0015000000000004e88969001200000000896a001300896b0004000000000000000072020000"),
  ("plc-to-client", "7201000d3200000542000000020000000072010000"),
  ("client-to-plc", "72030056209d36c6f3524b8d30e69d56ec312ed3356a85a5f4809e54d4f6daf3f080c5bfaf31000004f200000003000000013400000001018243000205000004e88969001200000000896a001300896b0004000000030000000072030000"),
  ("plc-to-client", "72030029204bef12ab55f513a46ce43b67acfedeaa138b029f6b11199fc1e6f03dc48575e832000004b1000000"),
  ("plc-to-client", "7203002920daf460cdf0e619921f55c3dcf20e355c84e221d620c12192385698cc6aee91e00300008931000000"),
  ("plc-to-client", "7203002220bd87dfc96e19825e7d334e28cab2375b2fd5676f59a0d9a5fb69a36d77a2f1110072030000"),
  ("client-to-plc", "720300562045c55863d45b4f8e92c8a24b1df7ec81485ec44702d72cfeb014f2d3eff69f173100000586000000040000000134000000012004018e32000004e88969001200000000896a001300896b000400000001010000000072030000"),
  ("plc-to-client", "720300292088ed70b270a3bd625bae7017780e7347d2aa7175e15f2085ea1f86250c226e5f3200000586000000"),
  ("plc-to-client", "7203002920b1f1c881d236352e29fa6639373c1fe2c5926d529d5a60ff80e01f661a43d77e0400000010021400"),
  ("plc-to-client", "72030029206ba53c3e817584c453bd2c6113f2a28bfc03e1ba8e1c18cb18e35ce8d137c2ba0102030405060708"),
  ("plc-to-client", "7203002920d47e1043b3ad48866bff4035f6fefbb285ccb68973849a318c93ac75ee5db32c090a0b0c0d0e0f10"),
  ("plc-to-client", "72030025208c4e15464e89da80dc87abb37a161e18006675cc59fe8f6a80d7802658a96f0e1112130072030000"),
  ("client-to-plc", "7203005d20c537cae5a4dab27e6af6b419789210bb978fa6feb3baea76abcaa7d96757931d310000054c0000000500000001340000000001070088d0b88001049376030204000004e88969001200000000896a001300896b00040000020000000072030000"),
  ("plc-to-client", "7203002920a602838a7f2d8ab17a3244475508523d397792dd4296f4b994e38c7a76b0b25f320000054c000000"),
  ("plc-to-client", "72030029209d92bf3ba34a6b93c913ef95baba858382ee8adadb79eb443a87b3446c54ebbc0500000100140004"),
  ("plc-to-client", "720300282092c22c904f04be9784dee3a8e6cc49c14e180f706479d05c2ebfda302cd8441a0203040500000172030000"),
  ("client-to-plc", "7203006520c4f6ef1647dc648d9d2988870d9b1b7cb956df980cbcb66c3b445be1d4114dca31000005420000000600000001340000000001070088d0b880010493760300020100140002aabb00000004e88969001200000000896a001300896b00040000020000000072030000"),
  ("plc-to-client", "72030029201f9bc0e0a6ac1aa8d1152d26d38ac87b4828d7a1b934ed9ccc3935f6316e221b3200000542000000"),
  ("plc-to-client", "7203002720032d3101ef3ce0d85ab395cd96812b10bfa6f58078654cddabe7fb53782c3bf306000100000072030000"),
  ("client-to-plc", "7203005d20bb2280eb432b3ca51a0dbcfebf3e6832ff9837dc3619a24cd352b02e6f604fd8310000054c0000000700000001340000000001070088d0b88001049376030004000004e88969001200000000896a001300896b00040000030000000072030000"),
  ("plc-to-client", "7203002920a602838a7f2d8ab17a3244475508523d397792dd4296f4b994e38c7a76b0b25f320000054c000000"),
  ("plc-to-client", "7203002920861a0ff7120a4bd8240d34b435a7d04fe98502d18c7323d28452d940773a58c40700000100140004"),
  ("plc-to-client", "720300282082b49dcc69345cb1b58a64c56b58b716d117235d9c367e8e3eb32c6e4bec39ecaabb020300000272030000"),
  ("client-to-plc", "7201001231000004d40000000800000001340000000072010000"),
  ("plc-to-client", "7201000832000004d4000000")]

def emulatorFrame (index : Nat) : ByteArray := hexBytes emulatorKeyFrames[index]!.2

/-- The plaintext message of a V3 frame from a fixture, without checking its tag. -/
def v3Message (frame : ByteArray) : IO ByteArray :=
  match decodeFrame frame with
  | .ok (.v3, data) =>
    match decodeIntegrityEnvelope data with
    | .ok (_, message) => pure message
    | .error error => throw <| IO.userError s!"envelope: {repr error}"
  | _ => throw <| IO.userError "not a V3 frame"

def testSessionKeyWire : IO Unit := do
  let testKey := ((List.range 24).map UInt8.ofNat).toByteArray
  let some publicKey := publicKey? "01:BD426B091F08731A" | throw <| IO.userError "public key"
  check (publicKey.size == 40) "public key size"
  check (parseFingerprint "01:bd426b091f08731a" == some (.s71200, "BD426B091F08731A")) "fingerprint"
  -- The real CPU 1214C setup: its SecurityKey decodes, and its public key id is ours.
  let realSetup ← fixtureMessage "SetupSession (client-to-plc)"
  let realPayload := realSetup.extract 14 realSetup.size
  match decodeSecurityKey { data := realPayload, offset := 4 + 1 + 1 + 2 + 2 + 1 } with
  | .error error => throw <| IO.userError s!"real SecurityKey: {repr error}"
  | .ok (key, after) =>
    check (key.publicKey == ⟨keyId publicKey, 0x110⟩) "real public key id and flags"
    check (key.symmetricKey.flags == 0x10101) "real symmetric key flags"
    check (key.blob.size == 180) "real blob size"
    check (realPayload.extract 11 after.offset == key.encode) "real SecurityKey re-encodes"
    let realCreate ← fixtureMessage "CreateObject (plc-to-client)"
    match decodeCreateObjectReply (realCreate.extract 10 realCreate.size) with
    | .ok reply =>
      check (setupSessionKeyPayload reply.sessionId key.encode reply.serverSessionVersion == realPayload)
        "real SessionKey setup payload"
    | .error error => throw <| IO.userError s!"real CreateObject: {repr error}"
  -- The real activation, protection-level read, read and write messages carry the
  -- IntegrityIds of the keyed counters.
  let realSession : Session := { phase := .ready, sessionId := 0x39b, sequence := 3 }
  let keyed := Keyed.install testKey
  let activation ← fixtureMessage "request function 0x04F2 (client-to-plc)"
  check (realSession.keyedMessage .activate 0 == activation) "real activation message"
  let protection ← fixtureMessage "request function 0x0586 (client-to-plc)"
  check ({ realSession with sequence := 4 }.keyedMessage (.getVarSubstreamed 1842) 1 == protection)
    "real protection-level message"
  -- The emulator session, frame by frame.
  match decodeCreateObjectReply ((emulatorFrame 3).extract 14 ((emulatorFrame 3).size - 4)) with
  | .error error => throw <| IO.userError s!"emulator CreateObject: {repr error}"
  | .ok reply =>
    let securityKey := SecurityKey.ofKeys .s71200 publicKey testKey (ByteArray.mk (Array.replicate 180 0))
    let created : Session := { phase := .created, sessionId := reply.sessionId, sequence := 2 }
    let some (setupFrame, _, _) := created.send (.setupSessionKey reply.serverSessionVersion securityKey.encode)
      | throw <| IO.userError "setup not sendable"
    check (setupFrame == emulatorFrame 4) "emulator SessionKey setup frame"
    let ready : Session := { phase := .ready, sessionId := reply.sessionId, sequence := 3 }
    let some (activationFrame, _, ready, keyed) := ready.sendKeyed keyed .activate
      | throw <| IO.userError "activation"
    check (activationFrame == emulatorFrame 6) "emulator activation frame"
    let keyed := keyed.skipAfterLegitimation .s71200
    let some (protectionFrame, _, ready, keyed) := ready.sendKeyed keyed (.getVarSubstreamed 1842)
      | throw <| IO.userError "protection level"
    check (protectionFrame == emulatorFrame 10) "emulator protection-level frame"
    let read : ReadRequest := { addresses := [ItemAddress.db 1 2 4], form := .vlq, keyQualifier := 0 }
    let some (readFrame, _, ready, keyed) := ready.sendKeyed keyed (.read read)
      | throw <| IO.userError "read"
    check (readFrame == emulatorFrame 16) "emulator read frame"
    let write : WriteRequest :=
      { addresses := [ItemAddress.db 1 0 2], values := [.scalar (.blob 0 (bytes #[0xaa, 0xbb]))],
        form := .vlq, keyQualifier := 0 }
    let some (writeFrame, _, ready, keyed) := ready.sendKeyed keyed (.write write)
      | throw <| IO.userError "write"
    check (writeFrame == emulatorFrame 20) "emulator write frame"
    let some (readFrame2, _, _, keyed) := ready.sendKeyed keyed
        (.read { read with addresses := [ItemAddress.db 1 0 4] })
      | throw <| IO.userError "read 2"
    check (readFrame2 == emulatorFrame 23) "emulator second read frame"
    check (keyed.counters == { read := 4, write := 3 }) "counters after the session"
    -- Replies: the data units after each request reassemble and open under the key.
    for (first, last, function) in [(7, 9, errorFunction), (11, 15, FunctionCode.getVarSubstreamed),
        (17, 19, FunctionCode.getMultiVariables), (21, 22, FunctionCode.setMultiVariables),
        (24, 26, FunctionCode.getMultiVariables)] do
      let units := (List.range (last + 1 - first)).foldl (fun acc i => acc ++ emulatorFrame (first + i)) ByteArray.empty
      match keyed.openReply units with
      | .ok message =>
        match decodeResponseHeader { data := message } with
        | .ok (header, _) => check (header.function == function) s!"reply {first}: function"
        | .error _ => throw <| IO.userError s!"reply {first}: header"
      | .error error => throw <| IO.userError s!"reply {first}: {repr error}"
      check (keyed.openReply (flipByte units 40)).toBool.not s!"reply {first}: changed byte refused"

/-- s7commplus `fingerprint_challenge` of 20-byte challenges `(a·i + c) mod 256`: a, c, fingerprint. -/
def fingerprintVectors : List (Nat × Nat × String) := [
  (1, 0, "e2116ffb5d62d807"),
  (0, 0, "5843c81129fe37c7"),
  (0, 255, "e899de63dec873c3"),
  (7, 3, "122d636fd2f000b2"),
  (13, 1, "cb5103022ea35b7d"),
  (31, 200, "2a434083f66f94a0"),
  (97, 17, "f963152377763ce0"),
  (255, 128, "7c2ab9995a0a6efd")]

/-- s7commplus `derive_session_key(key2, challenge)` with key2 `(a·i + c) mod 256` (24 bytes) and challenge `(5i + 2) mod 256`. -/
def sessionKeyVectors : List (Nat × Nat × String) := [
  (1, 0, "3a3a42d2130ef21798e54315c102096703deeed881ce40f7"),
  (3, 7, "eba06813f8ca7c35af6910c3ac3b8578b60fc66f76ac0a25"),
  (11, 99, "2c3ad8249f064439cbd4484e137ccdf538fd3604a26612cf"),
  (0, 0, "6ca3931445434b274ba5030b5415fb140d3f6f3d510e6ec6")]

/-- The other KDFs on the inputs of `kdfInput`. -/
def challengeKeyVector : String := "9742fc36cfd0f91aa87619220c882964"
def seedKeyIvVector : String := "0664fd07b866e69a2b119f5e62b6c781db63dae7f720a0edf5f708af441eab7282347c5bc43bf9a8b1324f84308b2f6a"
def legitimationKeyVector : String := "1a15d5191f0eca23fe0d86a4387ba07d70064f2c841d5477"

/-- s7commplus `derive_key_id` of every bundled public key, as a little-endian number. -/
def publicKeyIdVectors : List (String × UInt64) := [
  ("00:0448ACCBD5A0BFD2", 308686565937299410),
  ("00:181B7B0847D11694", 1737117356776298132),
  ("00:1B580465BB0551B2", 1970329671950487986),
  ("00:2C1DD211E529278D", 3178927886294394765),
  ("00:580B8A122D42D1C0", 6344316310754873792),
  ("00:60CDAAA33E0B5D20", 6975419015964089632),
  ("00:65227E2580029B7F", 7287525846565428095),
  ("00:6BA412F7F1D965AA", 7756345314362615210),
  ("00:99E4632334CC7993", 11089097185353824659),
  ("00:ACD68E9BF9901F8B", 12454298620097732491),
  ("00:C4F47B876DA76D52", 14192104147341765970),
  ("00:D3F9CD55A57FE4EB", 15274465378936284395),
  ("00:E69E7A996524AFAC", 16617854474289196972),
  ("01:A95850575DF7B3DE", 12202591526529250270),
  ("01:AC9BE476CB324E65", 12437785994780102245),
  ("01:BD426B091F08731A", 13637580308550808346),
  ("03:09013727CCBFBF3C", 648860465396432700),
  ("03:4964E2F77A386F64", 5288601414975123300),
  ("03:5A9B6B015F48D284", 6528929738441413252),
  ("03:950840E428F7C7FA", 10738904660148996090),
  ("03:AE5147B429BBA96C", 12560899674832873836),
  ("03:B07654AC9CAA4ACA", 12715443698266688202),
  ("03:CE331E08538A26B9", 14858252616735532729),
  ("03:D61B355B59D711A9", 15427983614953329065),
  ("03:E90B455D3CC46013", 16792591902334803987)]


def seqBytes (count a c : Nat) : ByteArray :=
  ((List.range count).map fun i => UInt8.ofNat ((a * i + c) % 256)).toByteArray

def testKeyDerivation : IO Unit := do
  for (a, c, hex) in fingerprintVectors do
    check (toHex (fingerprintChallenge (seqBytes 20 a c)) == hex) s!"fingerprint of challenge {a}i+{c}"
  for (a, c, hex) in sessionKeyVectors do
    check (toHex (deriveSessionKey (seqBytes 24 a c) (seqBytes 20 5 2)) == hex) s!"session key from key2 {a}i+{c}"
  check (toHex (deriveChallengeEncryptionKey (seqBytes 24 3 1)) == challengeKeyVector) "challenge encryption key"
  check (toHex (deriveSeedEncryptionKeyAndIv (seqBytes 32 5 9) (seqBytes 64 7 4)) == seedKeyIvVector)
    "seed encryption key and IV"
  check (toHex (deriveLegitimationChallengeKey (seqBytes 24 11 6)) == legitimationKeyVector) "legitimation key"
  check (publicKeyIdVectors.length == 25) "every bundled key has a vector"
  for (fingerprint, id) in publicKeyIdVectors do
    let some key := publicKey? fingerprint | throw <| IO.userError s!"{fingerprint}: no key"
    check (keyId key == id) s!"{fingerprint}: key id"

/-- AES-128 (key, plaintext, ciphertext) from Python's `cryptography`; the first is FIPS-197 C.1. -/

def aesVectors : List (String × String × String) := [
  ("000102030405060708090a0b0c0d0e0f", "00112233445566778899aabbccddeeff", "69c4e0d86a7b0430d8cdb78070b4c55a"),
  ("030a11181f262d343b424950575e656c", "05121f2c394653606d7a8794a1aebbc8", "84d256b78088813c27392464829b7081"),
  ("ffffffffffffffffffffffffffffffff", "00000000000000000000000000000000", "a1f6258c877d5fcd8964484538bfc92c"),
  ("116cc7227dd8338ee9449ffa55b00b66", "c8e70625446382a1c0dffe1d3c5b7a99", "ba6c7c7c436137a2d8c27619a6f030a3")]

/-- s7commplus `present.encrypt(block, key)`. -/

def presentVectors : List (Nat × Nat × Nat) := [
  (0x0, 0x0, 0x9ba9d5bf4e8fd5d8),
  (0xffffffffffffffff, 0xffffffffffffffffffff, 0xd6414c64d22f19dc),
  (0x123456789abcdef, 0x1122334455667788aabb, 0x61e70af14a4979f6),
  (0xf5ea1e69cbdf8ef1, 0xa98de7c5164ad032538f, 0xb746c01e6d468034)]

/-- s7commplus `curve.x_multiply(scalar, x)`. -/

def curveVectors : List (Nat × Nat × Nat) := [
  (0x1, 0x7d2ed8e2846e58d74a7a613285471707a39d0c8e, 0x7d2ed8e2846e58d74a7a613285471707a39d0c8e),
  (0x2, 0x7d2ed8e2846e58d74a7a613285471707a39d0c8e, 0x4f6183b684c872fb6b49509f4798a9bd7f7ce96e),
  (0x3039, 0x7d2ed8e2846e58d74a7a613285471707a39d0c8e, 0xb6114803b6330063ea41fbc472506fb301e671d8),
  (0x5445b417fbc8eac913fa812a7386eefb70636e49, 0x7d2ed8e2846e58d74a7a613285471707a39d0c8e, 0x3659aa1d84a552f930f766e035f791f6d3490d97),
  (0x5445b417fbc8eac913fa812a7386eefb70636e49, 0x7b86dbb90a930cbd8986174801f9a35c4af0e1e0, 0xa0fb5384f81f06a5e2a5527eae8029a87e70afdb),
  (0x0, 0x5, 0x0),
  (0x100000000000000000000f368cda5cdb2ebfc69c7, 0x7d2ed8e2846e58d74a7a613285471707a39d0c8e, 0x0)]

/-- s7commplus `checksum.multiply(a, b)`. -/

def checksumVectors : List (Nat × Nat × Nat) := [
  (0x0, 0x5, 0x0),
  (0x1, 0x1, 0x1),
  (0x80000000000000000000000000000000, 0x2, 0x100008005),
  (0x2e2b2825221f1c191613100d0a070401, 0x524d48433e39342f2a25201b16110c07, 0xc7deef78c9be7c60634076070ea4b35c),
  (0xffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffff, 0xaaaaaaaaaaaaaaaaffffffff40005552)]

def preSeedVector : Nat := 0xa05b7f83e3209ad631fc45e4318e66616fc46e04

def blobKeysVector : String × String × Nat := ("2a5aac14ae18fe52e2560222d0bed2ee", "2530fa6fc7c95677040956779b66398b", 0xa94ddd9af2f02e6fce3462b8735b2769)

/-- s7commplus `authenticate_real_plc` with recorded random draws: fingerprint, challenge,
    key1, key2, IV, blinding, ladder input, blob, session key. -/

def blobVectors : List (String × String × String × String × String × String × String × String × String) := [
  ("01:BD426B091F08731A", "000102030405060708090a0b0c0d0e0f10111213", "06080a0c0e10121416181a1c1e20222426282a2c2e303234", "030405060708090a0b0c0d0e0f101112131415161718191a", "090c0f1215181b1e2124272a2d303336", "0c1014181c2024282c3034383c4044484c505458", "0f14191e23282d32373c41464b50555a5f64696e",
    "addee1feb4000000010000000100000012d7a72762e5c78601010000000000001a73081f096b42bd1001000000000000c8eb6aff5fe8e4e23e1b8c0bba9f81b2c092330d99865208595b8f49f213d9e1c7c8b6d4b76c4c810c1014181c2024282c3034383c4044484c505458090c0f1215181b1e2124272a2d30333673d6f22a80df26037a6fcec89d908f04a9178112dc1d26091ba47e6171d2b8375346a220c7e201cdb9440c7f3fa044fc9b8c195bdc807943", "9b9bf35fae6d7a1645bcc144a1e599a91915913a2ccf1ca9"),
  ("00:0448ACCBD5A0BFD2", "052a4f7499bee3082d52779cc1e60b30557a9fc4", "7ea8d2fc26507aa4cef8224c76a0caf41e48729cc6f01a44", "7ba4cdf61f48719ac3ec153e6790b9e20b345d86afd8012a", "81acd7022d5883aed9042f5a85b0db06", "84b0dc0834608cb8e4103c6894c0ec1844709cc8", "87b4e10e3b6895c2ef1c4976a3d0fd2a5784b1de",
    "addee1feb400000001000000010000005246235b52f5b99b0100000000000000d2bfa0d5cbac480410000000000000009ff8ff0b6b6b92f2b6fc1b87026a28ad17f07e8bb17bcddfea11e9c6ed8b8b92f110bfec60e529e984b0dc0834608cb8e4103c6894c0ec1844709cc881acd7022d5883aed9042f5a85b0db0664389caf9c29e1c87cd63ab9f0199ab8de08312583f58db2ba0ec1b60f211b73d891c482c14401e325629e0573cb7354a61191e8cbda4b6f", "936525c66040017dee3884c690de72284a30124837268be9"),
  ("01:A95850575DF7B3DE", "09080706050403020100fffefdfcfbfaf9f8f7f6", "f6489aec3e90e23486d82a7cce2072c41668ba0c5eb00254", "f34495e63788d92a7bcc1d6ebf1061b20354a5f64798e93a", "f94c9ff24598eb3e91e4378add3083d6", "fc50a4f84ca0f4489cf04498ec4094e83c90e438", "ff54a9fe53a8fd52a7fc51a6fb50a5fa4fa4f94e",
    "addee1feb4000000010000000100000069eac649bbc5ab190101000000000000deb3f75d575058a9100100000000000051f06a19648c9a189d9db73f415f3fc2cf82815f2ea5c7a7e4ee4d764464e06557a6ae57abb47f9cfc50a4f84ca0f4489cf04498ec4094e83c90e438f94c9ff24598eb3e91e4378add3083d68e93fcedeb7ed26a4ba11e58beec979d216ee7f07117da567b2e8a0eb0c609ca5c8229ce74df4d667963f0dc9ee3ce7c7799b6ca53c278fb", "1f6c291e179a616fe96270d9d068d01c1df66b1d7029685e")]

def testBlob : IO Unit := do
  for (key, plaintext, ciphertext) in aesVectors do
    check (toHex (Aes.encryptBlock (hexBytes key) (hexBytes plaintext)) == ciphertext) s!"AES-128 under {key}"
  for (block, key, expected) in presentVectors do
    check (Present.encrypt block key == expected) s!"PRESENT {block} under {key}"
  for (scalar, x, expected) in curveVectors do
    check (Curve.xMultiply scalar x == expected) s!"curve {scalar} times {x}"
  for (a, b, expected) in checksumVectors do
    check (Checksum.multiply a b == expected) s!"checksum {a} times {b}"
  check (Seed.preSeed (seqBytes 24 11 4) == preSeedVector) "pre-seed"
  let (challengeKey, checksumKey, hashKey) := Seed.deriveKeys preSeedVector
  check ((toHex challengeKey, toHex checksumKey, hashKey) == blobKeysVector) "blob keys"
  for (fingerprint, challenge, key1, key2, iv, blinding, prng2, blob, sessionKey) in blobVectors do
    let some (family, _) := parseFingerprint fingerprint | throw <| IO.userError s!"{fingerprint}"
    let some publicKey := publicKey? fingerprint | throw <| IO.userError s!"{fingerprint}: no key"
    match buildRealPlcBlob family publicKey (hexBytes challenge) (hexBytes key1) (hexBytes key2) (hexBytes iv)
        (hexBytes blinding) (hexBytes prng2) with
    | some (built, key) =>
      check (built.size == 180) s!"{fingerprint}: blob size"
      check (toHex built == blob) s!"{fingerprint}: blob"
      check (toHex key == sessionKey) s!"{fingerprint}: session key"
    | none => throw <| IO.userError s!"{fingerprint}: no blob"
  -- The real CPU 1214C blob: its header is ours except the key id of key2, which was not
  -- recorded; the IV follows the 48-byte header and the 60-byte seed.
  let realSetup ← fixtureMessage "SetupSession (client-to-plc)"
  let realPayload := realSetup.extract 14 realSetup.size
  match decodeSecurityKey { data := realPayload, offset := 11 } with
  | .ok (key, _) =>
    let some publicKey := publicKey? "01:BD426B091F08731A" | throw <| IO.userError "public key"
    let ours := blobMetadata .s71200 publicKey (ByteArray.mk (Array.replicate 24 0))
    check (key.blob.size == 180) "real blob size"
    check (key.blob.extract 0 16 == ours.extract 0 16) "real blob magic, length and constants"
    check (key.blob.extract 24 48 == ours.extract 24 48) "real blob flags and public key id"
  | .error error => throw <| IO.userError s!"real SecurityKey: {repr error}"

def main : IO Unit := do
  testFrameHeaderBytes
  testFrameVersionBytes
  testUInt32Vectors
  testUInt32Leniency
  testUInt64Vectors
  testInt32Vectors
  testInt32Leniency
  testInt64Vectors
  testPValueVectors
  testPValueRejections
  testSessionFrames
  testCreateObjectTrees
  testSessionHeaders
  testFixtureRead
  testPartialFailureReplies
  testFixtureWrite
  testPartialFailureResults
  testSessionRequests
  testFrameRejections
  testFragments
  testIntegrity
  testIntegrityIds
  testSha256
  testHmacDialects
  testSessionKeyWire
  testKeyDerivation
  testBlob
  IO.println "All lean-s7commplus tests passed."
