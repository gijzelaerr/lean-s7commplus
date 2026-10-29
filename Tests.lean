import LeanS7CommPlus

open LeanS7 LeanS7CommPlus

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

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

def main : IO Unit := do
  testFrameHeaderBytes
  testFrameVersionBytes
  IO.println "All lean-s7commplus tests passed."
