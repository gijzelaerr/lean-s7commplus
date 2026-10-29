"""End-to-end test of the Lean client against the Python s7commplus emulator.

Starts integration/emulator.py, runs lean-s7commplus-cli against it, and checks each
result against the emulator's data and against the Python client.

usage: run.py
"""

import os
import subprocess
import sys
from pathlib import Path

from s7commplus import Client

ROOT = Path(__file__).resolve().parent.parent
CLI = ROOT / ".lake" / "build" / "bin" / ("lean-s7commplus-cli.exe" if os.name == "nt" else "lean-s7commplus-cli")


def cli(port: int, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(CLI), "127.0.0.1", str(port), *args], capture_output=True, text=True, timeout=60, check=False
    )


def expect(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"FAIL: {message}")
    print(f"ok: {message}")


def main() -> None:
    emulator = subprocess.Popen(
        [sys.executable, str(ROOT / "integration" / "emulator.py")],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        text=True,
    )
    try:
        assert emulator.stdout is not None
        port = int(emulator.stdout.readline())

        read = cli(port, "read", "1", "2", "4")
        expect(read.returncode == 0 and read.stdout.strip() == "02030405", f"read DB1.2..6: {read.stdout!r} {read.stderr!r}")

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
    print("integration: all checks passed")


if __name__ == "__main__":
    main()
