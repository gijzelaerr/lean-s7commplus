"""Run the Python s7commplus emulator for the Lean client.

Prints the port on the first line, then serves until stdin closes. DB1 holds the
bytes 0..15, DB7 four zero bytes. With MAX_RESPONSE_PDU, the emulator splits every
reply after the session setup into fragments of at most that many bytes. With
`--sessionkey`, it runs in V1 SessionKey mode (integration/sessionkey_emulator.py).

usage: emulator.py [--sessionkey] [MAX_RESPONSE_PDU]
"""

import socket
import sys

from s7commplus.server import S7CommPlusServer
from sessionkey_emulator import make_server


def free_port() -> int:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return int(probe.getsockname()[1])


def main() -> None:
    arguments = sys.argv[1:]
    sessionkey = "--sessionkey" in arguments
    numbers = [argument for argument in arguments if argument != "--sessionkey"]
    max_response_pdu = int(numbers[0]) if numbers else None
    server = make_server(max_response_pdu) if sessionkey else S7CommPlusServer(max_response_pdu=max_response_pdu)
    server.register_raw_db(1, bytearray(range(16)))
    server.register_raw_db(7, bytearray(4))
    port = free_port()
    server.start(port=port)
    print(port, flush=True)
    try:
        sys.stdin.read()
    finally:
        server.stop()


if __name__ == "__main__":
    main()
