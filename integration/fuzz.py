"""Differential fuzzer: the Lean decoders against the Python reference.

Mutates valid VLQ and PValue encodings (byte changes, truncation, extension), decodes
each input with both, and counts the outcomes. "accept-different" (both accept, but
the value or the bytes consumed differ) must be zero. "lean-rejects" is expected where
the Lean decoders are stricter on purpose: out-of-range VLQs, a continuation flag on
the last VLQ byte, truncated values, arrays and structs.

usage: fuzz.py [SEED]
"""

import os
import random
import struct
import subprocess
import sys
from collections import Counter
from pathlib import Path

from s7commplus import vlq
from s7commplus.codec import decode_pvalue_to_bytes, encode_pvalue_typed
from s7commplus.protocol import DataType

ROOT = Path(__file__).resolve().parent.parent
ORACLE = ROOT / ".lake" / "build" / "bin" / ("lean-s7commplus-decode.exe" if os.name == "nt" else "lean-s7commplus-decode")

PYTHON = {
    "u32": vlq.decode_uint32_vlq,
    "u64": vlq.decode_uint64_vlq,
    "i32": vlq.decode_int32_vlq,
    "i64": vlq.decode_int64_vlq,
    "pvalue": lambda data, offset: (lambda r: (r[0].hex(), r[1]))(decode_pvalue_to_bytes(data, offset)),
}


def seeds() -> list[tuple[str, bytes]]:
    out: list[tuple[str, bytes]] = []
    for value in [0, 1, 63, 64, 127, 128, 16383, 16384, 2**21, 2**28, 2**31, 2**32 - 1]:
        out.append(("u32", vlq.encode_uint32_vlq(value)))
    for value in [0, 1, 2**32, 2**49, 2**56 - 1, 2**56, 2**63, 2**64 - 1]:
        out.append(("u64", vlq.encode_uint64_vlq(value)))
    for value in [0, -1, 63, 64, -64, -65, 8191, -8192, 2**31 - 1, -(2**31)]:
        out.append(("i32", vlq.encode_int32_vlq(value)))
    for value in [0, -1, -64, 2**55 - 1, -(2**55), 2**63 - 1, -(2**63)]:
        out.append(("i64", vlq.encode_int64_vlq(value)))
    typed = [
        (DataType.NULL, b""), (DataType.BOOL, b"\x01"), (DataType.USINT, b"\xab"), (DataType.UINT, b"\x12\x34"),
        (DataType.UDINT, struct.pack(">I", 0x12345678)), (DataType.ULINT, struct.pack(">Q", 2**60)),
        (DataType.SINT, b"\xf0"), (DataType.INT, b"\xff\xfe"), (DataType.DINT, struct.pack(">i", -100000)),
        (DataType.LINT, struct.pack(">q", -(2**60))), (DataType.BYTE, b"\x7f"), (DataType.WORD, b"\xbe\xef"),
        (DataType.DWORD, struct.pack(">I", 0xDEADBEEF)), (DataType.LWORD, struct.pack(">Q", 0x0123456789ABCDEF)),
        (DataType.REAL, struct.pack(">I", 0x3F800000)), (DataType.LREAL, struct.pack(">Q", 0x400921FB54442D18)),
        (DataType.TIMESTAMP, struct.pack(">Q", 0x0123456789ABCDEF)), (DataType.TIMESPAN, struct.pack(">q", -5)),
        (DataType.RID, struct.pack(">I", 0x8A0E0001)), (DataType.AID, struct.pack(">I", 2521)),
        (DataType.BLOB, b"\x01\x02\x03"), (DataType.WSTRING, b"hi"),
    ]
    for datatype, data in typed:
        out.append(("pvalue", encode_pvalue_typed(datatype, data)))
    return out


def mutate(rng: random.Random, data: bytes) -> bytes:
    choice = rng.randrange(4)
    buffer = bytearray(data)
    if choice == 0 and buffer:
        buffer[rng.randrange(len(buffer))] = rng.randrange(256)
    elif choice == 1 and buffer:
        del buffer[rng.randrange(len(buffer)) :]
    elif choice == 2:
        buffer.insert(rng.randrange(len(buffer) + 1), rng.randrange(256))
    elif buffer:
        buffer[rng.randrange(len(buffer))] ^= 1 << rng.randrange(8)
    return bytes(buffer)


def python_decode(kind: str, data: bytes) -> str:
    try:
        value, consumed = PYTHON[kind](data, 0)
    except Exception:
        return "err"
    return f"ok {value} {consumed}"


def main() -> None:
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    inputs: list[tuple[str, bytes]] = []
    for kind, seed in seeds():
        inputs.append((kind, seed))
        for _ in range(60):
            inputs.append((kind, mutate(rng, seed)))
    lean = subprocess.run(
        [str(ORACLE)], input="".join(f"{kind} {data.hex()}\n" for kind, data in inputs),
        capture_output=True, text=True, check=True, timeout=300,
    ).stdout.splitlines()
    if len(lean) != len(inputs):
        raise SystemExit(f"oracle answered {len(lean)} of {len(inputs)} inputs")
    counts: Counter[tuple[str, str]] = Counter()
    different: list[str] = []
    for (kind, data), lean_line in zip(inputs, lean):
        python_line = python_decode(kind, data)
        if lean_line.startswith("ok") and python_line.startswith("ok"):
            outcome = "both-accept-equal" if lean_line == python_line else "accept-different"
            if outcome == "accept-different":
                different.append(f"{kind} {data.hex()}: lean {lean_line} python {python_line}")
        elif lean_line == "err" and python_line == "err":
            outcome = "both-reject"
        elif lean_line == "err":
            outcome = "lean-rejects"
        else:
            outcome = "python-rejects"
        counts[(kind, outcome)] += 1
    print(f"{len(inputs)} inputs")
    for kind in PYTHON:
        row = ", ".join(f"{o} {counts[(kind, o)]}" for o in
                        ("both-accept-equal", "both-reject", "lean-rejects", "python-rejects", "accept-different"))
        print(f"  {kind:7} {row}")
    for line in different[:20]:
        print("  DIFFERENT", line)
    if different:
        raise SystemExit(f"{len(different)} inputs decode differently")


if __name__ == "__main__":
    main()
