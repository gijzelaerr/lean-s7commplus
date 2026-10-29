"""Run the Python s7commplus emulator for the Lean client.

Prints the port on the first line, then serves until stdin closes. DB1 holds the
bytes 0..15, DB7 four zero bytes.

usage: emulator.py
"""

import socket
import sys

from s7commplus.server import S7CommPlusServer


def free_port() -> int:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return int(probe.getsockname()[1])


def main() -> None:
    server = S7CommPlusServer()
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
