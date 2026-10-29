# lean-s7commplus

An exploratory Lean 4 implementation of the Siemens S7CommPlus protocol, the
protocol used by S7-1200 and S7-1500 controllers for optimized and symbolic
access. It aims for machine-checked properties at the protocol boundaries:
round trips, exact lengths, and canonical decoding.

## Status

Plain V1 is done: codecs, sessions and a client that reads, writes and browses data
blocks on the Python emulator, with whole and with fragmented replies. V3 integrity
framing and IntegrityIds are proved relative to an abstract MAC and run with a
pure-Lean HMAC-SHA256 that matches Python's `hashlib`. The V1 SessionKey handshake is
implemented: the client builds the encrypted blob and derives the session key, and the
session runs live against the emulator. Legitimation (phase 7d), key renewal (7e) and
TLS are still open, and the blob has not yet met a real controller. The
[implementation plan](docs/plans/implementation.md) describes the layers, the phases,
the results, what remains, and the open decisions.

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
- **Scalar PValues** (`LeanS7CommPlus.PValue`): all 22 scalar datatypes, BLOB and
  WSTRING. `decodePValue_encode`: decoding the encoding of any value, inside
  arbitrary surrounding bytes, returns it and consumes exactly its encoding.
- **Object trees** (`LeanS7CommPlus.Tree`): objects, attributes, relations, fixed-size
  arrays and nested structs, read as a flat item sequence with a stack.
  `decodeValue_encode` and `decodeTree_encode`: any well-nested tree, inside arbitrary
  surrounding bytes, decodes to exactly its items. The CreateObject request and reply
  trees of the CPU 1214C session decode and re-encode byte for byte.
- **Message headers and the integrity envelope** (`LeanS7CommPlus.Message`): the
  14-byte request header, the 10-byte response header, and the V3 envelope (`0x20`,
  32-byte digest, message). Round trips (`decodeRequestHeader_encode`,
  `decodeResponseHeader_encode`, `decodeIntegrityEnvelope_encode`) and canonical
  forms: `decodeRequestHeader_canonical` and `decodeResponseHeader_canonical` (only
  the two reserved words are ignored) and `decodeIntegrityEnvelope_canonical`
  (strict). Every frame of the CPU 1214C session decodes to its header.
- **GetMultiVariables** (`LeanS7CommPlus.Access`): item addresses, the object qualifier
  (fixed and VLQ forms), the request payload with an optional IntegrityId before the
  fill, and the reply's value and error lists. `decodeReadRequest_encode` and
  `decodeReadReply_encode`: round trips. The read of the CPU 1214C session and the
  four S7-1500 partial-failure replies decode and re-encode byte for byte.
- **SetMultiVariables and per-item read results** (`LeanS7CommPlus.Write`): the write
  request (addresses, values numbered from 1, qualifier, fill) and reply, with round
  trips `decodeWriteRequest_encode` and `decodeWriteReply_encode`. `ReadReply.results`
  turns a read reply into one value or error per requested item, and
  `ReadReply.results_spec` proves it sound: one result per item, a value only from the
  value list with no error for that item, an error only from the error list.
- **Plain V1 sessions and a client** (`LeanS7CommPlus.Session`, `LeanS7CommPlus.Client`):
  the session requests (InitSSL, CreateObject, SetupSession, reads, writes, EXPLORE),
  byte for byte those of the Python client, and the state machine that orders them.
  `Session.send_spec`, `Session.receive_spec`, `Phase.after_spec` and
  `Session.ready_only_after_setup`: requests go out only in their phase with increasing
  sequence numbers, a reply is accepted only if it answers the outstanding request, and
  data requests need a completed SetupSession. `lean-s7commplus-cli` connects to the
  Python emulator and reads, writes and browses data blocks.
- **SessionKey sessions, wire layer** (`LeanS7CommPlus.SessionKey`,
  `LeanS7CommPlus.KeyedSession`): the SecurityKey struct (`decodeSecurityKey_encode`,
  through the proved tree codec), the SessionKey setup, the activation and the
  protection-level read, and keyed sessions that seal every request with HMAC-SHA256
  and the next IntegrityId of its counter (`Session.sendKeyed_spec`,
  `Session.sendKeyed_opens`, `Session.sendKeyed_counter`) and accept a reply only if it
  is the state-resume sealing of its message (`Keyed.openReply_sound`). The real CPU
  1214C SetupSession, activation and protection-level read re-encode byte for byte;
  against the emulator, every request frame equals the Python client's, tags included.
  The public-key table and key ids derive from HarpoS7 (MIT, `LICENSE-HarpoS7`).
- **SessionKey key derivation** (`LeanS7CommPlus.KeyDerivation`): the challenge
  fingerprint (a 13-round SPN on AES's inverse S-box), the session key
  (`deriveSessionKey`), and the challenge, seed and legitimation keys, ported from
  s7commplus and HarpoS7 and checked against s7commplus on known-answer vectors,
  including the key ids of all 25 bundled public keys.
- **The SessionKey blob** (`LeanS7CommPlus.Aes`, `LeanS7CommPlus.Blob`): AES-128, the
  PRESENT-80 variant, the x-only ladder on the 160-bit curve, the GF(2¹²⁸) checksum,
  and the 180-byte blob of families 00 and 01 as a pure function of the random draws
  (`buildRealPlcBlob`). Three whole blobs equal s7commplus's byte for byte, and the real
  CPU 1214C blob's header matches. `lean-s7commplus-cli --sessionkey` opens a
  SessionKey session with all draws random.
- **Frames** (`LeanS7CommPlus.Frame`). `decodeFrame_encodeFrame`: round trip.
  `decodeFrame_canonical`: every accepted frame is exactly the encoding of the
  decoded version and data.
- **Fragment reassembly** (`LeanS7CommPlus.Fragments`): replies split over several
  fragments, with the trailer after the last only. `decodeFragments_encode` and
  `reassemble_encodeFragments`: round trip, and the reassembled data is the fragments'
  data in order. `decodeFragments_canonical`: every accepted message is exactly the
  encoding of its fragments. `reassemble_bound`: at most `maxFragments` (4096)
  fragments and 65535 bytes per fragment. `reassemble_splitData`: reassembly undoes the
  emulator's split.
- **V3 frames over an abstract MAC** (`LeanS7CommPlus.Integrity`): the HMAC envelope of
  SessionKey sessions, for single frames and for fragmented responses whose tags form
  a chain (`ChainedMac`, with the independent and PLCSIM feed-forward dialects as
  instances). `openV3_sealV3` and `openFragments_sealFragments`: round trips.
  `sealV3_of_openV3` and `openFragments_sound`: an accepted frame or response is
  exactly the seal of the data it yields.
- **SHA-256 and HMAC-SHA256** (`LeanS7CommPlus.Sha256`), checked against Python's
  `hashlib` and `hmac` on 48 known-answer vectors and RFC 4231. `Mac.hmacSha256` is the
  V3 tag, and `ChainedMac.stateResume` the chaining of real S7-1200/1500 firmware.
  All three chaining dialects seal a fragmented response byte for byte as the Python
  emulator and verifier do. `stateResume_first_tag` and
  `sealFragments_stateResume_single`: the chain starts with the standard HMAC. The
  implementation is not proved equal to FIPS 180-4, and is not constant-time.
- **IntegrityIds** (`LeanS7CommPlus.IntegrityId`): separate read and write counters, as
  in the Python client. `IntegrityCounters.next_read` and `IntegrityCounters.next_write`: a request uses
  and steps only its own counter. `IntegrityCounters.ids_consecutive` and `IntegrityCounters.ids_nodup`:
  the requests of one kind get consecutive ids, none repeated within 2³² of them.
  `ReadRequest.encode_insert` and `WriteRequest.encode_insert`: the request encoders
  place the id before the four fill bytes. The response position is a named parameter
  (`ResponseIntegrity`), with round trips for the leading and trailing forms.

Every frame of a real CPU 1214C V4.2.2 session (`fixtures/`) decodes and
re-encodes byte for byte, and the VLQ encoders match the Python reference on
boundary values.

`integration/run.py` runs the Lean client against the Python s7commplus emulator, with
whole and with fragmented replies and in a SessionKey session, and
`integration/fuzz.py` compares the Lean decoders with the Python ones on mutated input.

```console
lake build lean-s7commplus-cli
lake exe lean-s7commplus-cli 127.0.0.1 PORT read 1 0 4
```

`--sessionkey` before the host opens a V1 SessionKey session (families 00 and 01).
`--test-key2 HEX` does the same with a given key2 instead of a random one; it exists
for the emulator, which holds a configured session key and so must see the key2 it was
configured for.

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
