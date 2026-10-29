"""The s7commplus emulator in SessionKey mode, as the integration tests run it.

The emulator writes the ServerSessionVersion struct id as a VLQ (`82 3a`), where a
real CPU 1214C writes a 4-byte word (`00 00 01 3a`, s7commplus#136). Python's client
reads past that, so the order string it should strip is never reached. This subclass
writes the struct the way the real controller does.
"""

import struct

from s7commplus.protocol import DataType, ProtocolVersion
from s7commplus.server import S7CommPlusServer
from s7commplus.vlq import encode_uint32_vlq

FINGERPRINT = "01:BD426B091F08731A"
CHALLENGE = bytes(range(20))
SESSION_KEY = bytes(range(24))


class SessionKeyServer(S7CommPlusServer):
    @staticmethod
    def _build_server_session_version_struct() -> bytes:
        paom = b"1;6ES7 215-1AG40-0XB0 ;V4.2"
        return (
            bytes([0x00, DataType.STRUCT])
            + struct.pack(">I", 314)
            + encode_uint32_vlq(315)
            + bytes([0x00, DataType.UDINT])
            + encode_uint32_vlq(ProtocolVersion.V1)
            + encode_uint32_vlq(319)
            + bytes([0x00, DataType.WSTRING])
            + encode_uint32_vlq(len(paom))
            + paom
            + bytes([0x00])
        )


def make_server(max_response_pdu: int | None = None) -> SessionKeyServer:
    return SessionKeyServer(
        public_key_fingerprint=FINGERPRINT,
        session_challenge=CHALLENGE,
        session_key=SESSION_KEY,
        max_response_pdu=max_response_pdu,
    )
