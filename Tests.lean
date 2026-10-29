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
  testFrameRejections
  IO.println "All lean-s7commplus tests passed."
