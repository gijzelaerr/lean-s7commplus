/-!
# S7CommPlus protocol constants

The values are those of the Python reference implementation,
`s7commplus/protocol.py` in https://github.com/gijzelaerr/s7commplus, which cites
the Wireshark S7CommPlus dissector and thomas-v2/S7CommPlusDriver for them.
-/

namespace LeanS7CommPlus

/-- The first byte of every S7CommPlus frame and of its trailer. -/
def protocolId : UInt8 := 0x72

/-- The version byte of a frame. The frame version is not the session version:
    frames of a session with a V1 SessionKey are V3 frames with an HMAC prefix. -/
inductive FrameVersion where
  | v1
  | v2
  | v3
  | systemEvent
  deriving Repr, BEq, DecidableEq

def FrameVersion.toByte : FrameVersion → UInt8
  | .v1 => 0x01
  | .v2 => 0x02
  | .v3 => 0x03
  | .systemEvent => 0xfe

def FrameVersion.ofByte? : UInt8 → Option FrameVersion
  | 0x01 => some .v1
  | 0x02 => some .v2
  | 0x03 => some .v3
  | 0xfe => some .systemEvent
  | _ => none

theorem FrameVersion.ofByte?_toByte (version : FrameVersion) :
    FrameVersion.ofByte? version.toByte = some version := by
  cases version <;> rfl

/-- The first byte after the frame header. -/
def requestOpcode : UInt8 := 0x31
def responseOpcode : UInt8 := 0x32
def notificationOpcode : UInt8 := 0x33

-- Function codes of the requests the Python client sends.
namespace FunctionCode
def explore : UInt16 := 0x04bb
def createObject : UInt16 := 0x04ca
def deleteObject : UInt16 := 0x04d4
def setVariable : UInt16 := 0x04f2
def setMultiVariables : UInt16 := 0x0542
def getMultiVariables : UInt16 := 0x054c
def getVarSubstreamed : UInt16 := 0x0586
def initSsl : UInt16 := 0x05b3
end FunctionCode

end LeanS7CommPlus
