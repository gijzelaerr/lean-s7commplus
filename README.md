# lean-s7commplus

An exploratory Lean 4 implementation of the Siemens S7CommPlus protocol, the
protocol used by S7-1200 and S7-1500 controllers for optimized and symbolic
access. It aims for machine-checked properties at the protocol boundaries:
round trips, exact lengths, and canonical decoding.

## Status

Early. The [implementation plan](docs/plans/implementation.md) describes the
layers, the phases, what will be proved, and the open decisions.

Implemented and proved so far:

- **Unsigned VLQ** (`LeanS7CommPlus.Vlq`). `Vlq.decodeUInt32_encodeUInt32` and
  `Vlq.decodeUInt64_encodeUInt64`: decoding the encoding of any value, inside
  arbitrary surrounding bytes, returns it and consumes exactly its encoding.
  `Vlq.encodeUInt32_size` and `Vlq.encodeUInt64_size`: one to five and one to nine
  bytes. `Vlq.decodeUInt32_canonical`: the only non-minimal input the decoder
  accepts is the minimal encoding preceded by `0x80` bytes (leading zero groups).
- **Signed VLQ** (`LeanS7CommPlus.VlqSigned`). `Vlq.decodeInt32_encodeInt32` and
  `Vlq.decodeInt64_encodeInt64`: round trips inside arbitrary surrounding bytes.
  `Vlq.decodeInt32_canonical`: the accepted bytes are exactly the two's-complement
  pattern of the value over the number of groups read; the group count is the only
  freedom.
- **Frames** (`LeanS7CommPlus.Frame`). `decodeFrame_encodeFrame`: round trip.
  `decodeFrame_canonical`: every accepted frame is exactly the encoding of the
  decoded version and data.

Every frame of a real CPU 1214C V4.2.2 session (`fixtures/`) decodes and
re-encodes byte for byte, and the VLQ encoders match the Python reference on
boundary values.

Do not connect this software to production equipment.

## Relation to other projects

- [s7commplus](https://github.com/gijzelaerr/s7commplus): the Python
  implementation. It is the behavioural reference and the test oracle; its
  emulator is the first live target.
- [lean-s7](https://github.com/gijzelaerr/lean-s7): the same approach for classic
  S7comm (S7-300/400, and PUT/GET on S7-1200/1500). S7CommPlus is out of scope
  there.

## Licence

MIT; see [LICENSE](LICENSE). Siemens, S7, SIMATIC and TIA Portal are trademarks of
Siemens AG. This project is not affiliated with or endorsed by Siemens.
