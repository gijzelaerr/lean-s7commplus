"""End-to-end test of the Lean client against the Python s7commplus emulator.

Starts integration/emulator.py, runs lean-s7commplus-cli against it, and checks each
result against the emulator's data and against the Python client. The checks run
against whole replies, against replies split into 8-byte fragments, and in a V1
SessionKey session with split replies. In the SessionKey pass both clients get key2
instead of drawing it, so that the session key they derive from key2 and the emulator's
challenge is the one the emulator holds. Each builds a real blob from the other random
draws, but the emulator cannot decrypt a blob and checks only its key ids and flags;
the blob itself is checked by the known-answer tests.

usage: run.py
"""

import os
import subprocess
import sys
from pathlib import Path

from s7commplus import Client

sys.path.insert(0, str(Path(__file__).resolve().parent))
from sessionkey_emulator import KEY2, SESSION_KEY

ROOT = Path(__file__).resolve().parent.parent
CLI = ROOT / ".lake" / "build" / "bin" / ("lean-s7commplus-cli.exe" if os.name == "nt" else "lean-s7commplus-cli")


KEYED = False


def cli(port: int, *args: str) -> subprocess.CompletedProcess[str]:
    prefix = ["--test-key2", KEY2.hex()] if KEYED else []
    return subprocess.run(
        [str(CLI), *prefix, "127.0.0.1", str(port), *args], capture_output=True, text=True, timeout=60, check=False
    )


def patch_python_authenticator() -> None:
    """Give the Python client key2; it builds the blob and derives the session key."""
    from s7commplus.v1_session_key.real_plc import authenticator

    original = authenticator.RealPlcAuthenticator.__init__

    def with_key2(self: authenticator.RealPlcAuthenticator, key1: bytes | None = None, key2: bytes | None = None) -> None:
        original(self, key1, KEY2)

    authenticator.RealPlcAuthenticator.__init__ = with_key2  # type: ignore[method-assign]


def expect(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"FAIL: {message}")
    print(f"ok: {message}")


def run_checks(max_response_pdu: int | None, sessionkey: bool = False) -> None:
    global KEYED
    KEYED = sessionkey
    arguments = ([] if max_response_pdu is None else [str(max_response_pdu)]) + (["--sessionkey"] if sessionkey else [])
    print(f"emulator max_response_pdu={max_response_pdu} sessionkey={sessionkey}")
    emulator = subprocess.Popen(
        [sys.executable, str(ROOT / "integration" / "emulator.py"), *arguments],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        text=True,
    )
    try:
        assert emulator.stdout is not None
        port = int(emulator.stdout.readline())

        read = cli(port, "read", "1", "2", "4")
        expect(read.returncode == 0 and read.stdout.strip() == "02030405", f"read DB1.2..6: {read.stdout!r} {read.stderr!r}")
        whole = cli(port, "read", "1", "0", "16")
        expect(whole.stdout.strip() == bytes(range(16)).hex(), f"read DB1.0..16: {whole.stdout!r} {whole.stderr!r}")

        write = cli(port, "write", "1", "0", "aabb")
        expect(write.returncode == 0, f"write DB1.0..2: {write.stderr!r}")
        after = cli(port, "read", "1", "0", "4")
        expect(after.stdout.strip() == "aabb0203", f"read after write: {after.stdout!r}")

        browse = cli(port, "browse")
        expect(browse.returncode == 0 and browse.stdout.split("\n")[:2] == ["1 DB1", "7 DB7"], f"browse: {browse.stdout!r}")

        missing = cli(port, "read", "99", "0", "1")
        expect(missing.returncode != 0, f"read of a missing DB fails: {missing.stderr.strip()!r}")

        # Differential: the Python client sees the same data the Lean client wrote.
        client = Client()
        client.connect("127.0.0.1", port=port)
        if sessionkey:
            expect(client._connection._session_key == SESSION_KEY, "Python client runs a SessionKey session")
        try:
            expect(client.db_read(1, 0, 4).hex() == after.stdout.strip(), "Python client agrees on DB1.0..4")
            client.db_write(7, 0, b"\x01\x02\x03\x04")
        finally:
            client.disconnect()
        mine = cli(port, "read", "7", "0", "4")
        expect(mine.stdout.strip() == "01020304", f"Lean client reads the Python client's write: {mine.stdout!r}")
    finally:
        if emulator.stdin is not None:
            emulator.stdin.close()
        emulator.wait(timeout=30)


def main() -> None:
    run_checks(None)
    run_checks(8)
    patch_python_authenticator()
    run_checks(8, sessionkey=True)
    print("integration: all checks passed")


if __name__ == "__main__":
    main()
