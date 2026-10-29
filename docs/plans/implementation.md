# Plan: a proved S7CommPlus implementation in Lean

Status: phases 0–4 done on 2026-10-29. Phase 2 does not yet cover VLQ arrays, packed
structs or the EXPLORE elements; phase 3 covers reads and writes of DB regions. Decision 3 is taken (plain V1 first);
decision 1 is provisional (lean-s7 pinned to a commit). The other decisions are
open.

## Phase 4 results (plain V1 against the emulator)

- **Session** (`LeanS7CommPlus.Session`): the requests of a plain V1 session, byte for
  byte those of the Python client: InitSSL, CreateObject (the ServerSession object
  tree, built from tree items), SetupSession (SetMultiVariables on the session object,
  in a V2 frame, echoing attribute 306), GetMultiVariables, SetMultiVariables and
  EXPLORE. The emulator sends attribute 306 twice; like the Python client, the last
  one is echoed.
- **State machine.** `Session.send` allows a request only in its phase and stamps it
  with the next sequence number; `Session.receive` accepts a reply only if it answers
  the outstanding request (sequence number, and function or the generic error
  function; InitSSL's function is not checked, as real PLCs answer it with ERROR2).
  Theorems: `Session.send_spec`, `Session.receive_spec`, `Phase.after_spec`,
  `Session.ready_only_after_setup`.
- **Client and CLI** (`LeanS7CommPlus.Client`, `lean-s7commplus-cli`): COTP with the
  S7CommPlus TSAPs (the called TSAP `SIMATIC-ROOT-HMI` needs a connection request
  that lean-s7's 2-byte TSAP encoder cannot express), then lean-s7's TPKT and COTP
  data transport. Connect, read, write and browse data blocks.
- **Integration** (`integration/run.py`, in CI against s7commplus 0.3.0 from PyPI):
  reads, writes, browsing and a missing-DB read against the Python emulator, and a
  cross-check with the Python client in both directions. s7commplus 0.3.0 sends the
  browsed data blocks as consecutive top-level objects, `master` wraps them in
  thePLCProgram; the client reads both.
- **Differential fuzzer** (`integration/fuzz.py`, `lean-s7commplus-decode`): mutated VLQ
  and PValue encodings decoded by both. 3599 inputs: no input that both accept with
  different results, none that only Python rejects; the Lean-only rejections are the
  intended strictness (out-of-range VLQs, truncated values, arrays).
- **Python finding.** The emulator answers the protection-level query
  (GetVarSubstreamed) with a USINT array, and the Python client logs it as malformed
  ("expected a scalar UDInt"). The Lean client does not send that query.

## Phase 3c results (SetMultiVariables and per-item read results)

- **`LeanS7CommPlus.Write`**: the SetMultiVariables request payload (zero word, item
  count, field count, addresses, values numbered from 1 ending with `0x00`, object
  qualifier, fill, with the IntegrityId before the fill) and reply (return value and
  error list). Round trips: `decodeNumberedValues_encode`,
  `decodeWriteRequestBody_encode`, `decodeWriteRequest_encode`, `decodeWriteReply_encode`.
- **Per-item read results.** `ReadReply.results` maps a GetMultiVariables reply to one
  `ItemResult` (value or PLC error) per requested item. It ignores the overall return
  value, counts a NULL value next to an error as that error (the missing-DB answer of
  gijzelaerr/s7commplus#130), and refuses duplicate, out-of-range or unanswered items
  and items with both a non-NULL value and an error. `ReadReply.results_spec` proves it
  sound: exactly one result per item, a value result is that item's value with no error
  for it, an error result is that item's error.
- **Evidence.** The CPU 1214C write request (one byte, value 42, to DB1, which the PLC
  rejected) decodes with IntegrityId 2 and re-encodes byte for byte. The four S7-1500
  partial-failure replies give the per-item results gijzelaerr/s7commplus#129 asks for:
  the good items keep their values despite the nonzero return value.

## Phase 3b results (GetMultiVariables)

- **`LeanS7CommPlus.Access`**: item addresses (symbol CRC, access area, id count,
  sub-area, LIDs), the object qualifier in its fixed (`00 04` + word) and VLQ
  (`00 04` + VLQ + `00`) forms, the GetMultiVariables request payload (zero word,
  item count, field count, addresses, qualifier, fill) with the request IntegrityId
  spliced in before the fill, and the reply (return value, value list, error list).
- **Theorems.** Round trips for VLQ lists, addresses, the qualifier (both forms), the
  request body, the complete request payload with and without an IntegrityId
  (`decodeReadRequest_encode`), and the reply (`decodeReadReply_encode`).
- **Evidence.** The CPU 1214C read request decodes to one address (DB1, offset 0,
  one byte) with IntegrityId 2 and re-encodes byte for byte; it uses the VLQ
  qualifier form although the session is V1, as the Python client does on its data
  paths. Its reply decodes to the value 42 (a BLOB), followed by the PLC's
  IntegrityId and fill. The four S7-1500 partial-failure replies decode with their
  nonzero return value and re-encode exactly; a missing DB is answered with both a
  NULL value and an error for the same item (gijzelaerr/s7commplus#130).
- **Next:** SetMultiVariables, the per-item result semantics of #129 and #130 as
  theorems, and the response IntegrityId position as a per-family parameter.

## Phase 3a results (headers and the integrity envelope)

- **`LeanS7CommPlus.Message`**: the request header (opcode `0x31`, reserved word,
  function, reserved word, sequence, session id, transport flags; 14 bytes), the
  response header (opcode `0x32` or `0x02`, reserved word, function, reserved word,
  sequence, transport flags; 10 bytes, no session id), and the integrity envelope of
  V3 frames (`0x20`, the 32-byte HMAC-SHA256 digest, the message). The digest is
  carried as bytes; computing it stays out of scope (decision 3).
- **Theorems.** Round trips for all three, inside arbitrary surrounding bytes where
  that applies. Canonical forms: the header decoders ignore exactly the two reserved
  words (`decodeRequestHeader_canonical`, `decodeResponseHeader_canonical`), and the
  envelope decoder is strict (`decodeIntegrityEnvelope_canonical`). A reverse lemma
  for big-endian u32 reads (`readUInt32BE_value`) was needed and is not in lean-s7.
- **Evidence.** All 13 frames of the CPU 1214C session decode to the function code
  and sequence number of the capture; the V3 envelopes split and re-encode exactly.
  The PLC answers InitSSL with the ERROR2 function `0x05a9`, as expected on a
  session without TLS.
- **Python finding.** `codec.decode_response_header` decodes a 14-byte layout with a
  session id, but responses have a 10-byte header without one. The client does not
  use the helper (it slices responses at 10 bytes and checks them with
  `_validate_response_header`); only a unit test does.

## Phase 2b results (object trees)

- **`LeanS7CommPlus.Tree`**: attribute values (a scalar PValue or a fixed-size array:
  flags `0x10`, element type, VLQ count, elements), normal structs (struct id,
  `[nonzero VLQ key][value]` members, `0x00` terminator), and the object tree:
  `A1` object start, `A2` end, `A3` attribute, `A4` relation.
- **Design.** The tree is decoded as a flat sequence of items with a stack of open
  objects and structs, so nesting needs no recursive datatype and the proofs are
  plain inductions over lists. `Closes stack items` says a sequence is well nested
  and ends exactly when the outermost object closes.
- **Theorems.** `decodeValue_encode`, `decodeSlot_value`, `decodeSlot_struct`,
  `decodeItem_encode` (all eight item kinds), `decodeItems_encode` and
  `decodeTree_encode`: every well-nested tree, inside arbitrary surrounding bytes,
  decodes to exactly its items and consumes exactly its encoding.
- **Evidence.** The CreateObject request (13 items) and reply (15 items, with the
  USINT-array session challenge and the ServerSessionVersion struct) of the CPU
  1214C session decode and re-encode byte for byte; the four bytes after each
  tree are left unread.
- **Still rejected:** arrays of VLQ element types, packed structs, and the EXPLORE
  elements (`A5`–`AC`). The Python findings from phases 1 and 2a are filed as
  gijzelaerr/s7commplus#146 to #150.

## Phase 2a results (scalar PValues)

- **`LeanS7CommPlus.PValue`**: the PValue type for all 22 scalar datatypes (NULL,
  the fixed-width and VLQ integers, BYTE/WORD/DWORD/LWORD, REAL/LREAL as IEEE
  bits, TIMESTAMP, TIMESPAN, RID, AID), BLOB (root id, length, bytes) and WSTRING
  (length and UTF-8 bytes, kept as bytes). The encoder matches Python's
  `encode_pvalue_typed` byte for byte for every type. `decodePValue_encode` proves
  the round trip inside arbitrary surrounding bytes, built from per-field lemmas
  (`decodePValueBody_encodeBody`, `decodeBytes_encodeBytes`).
- **Not yet:** arrays (flags `0x10`), structs and S7STRING, and a canonical-form
  theorem. The decoder rejects them for now. The canonical form follows the field
  structure: the fixed-width kinds are strict and the VLQ kinds inherit the VLQ
  leniency (overlong encodings).
- **Python findings**, each reproduced against s7commplus `master`:
  1. Arrays of 64-bit VLQ types (ULINT, LINT, TIMESPAN) are read with the 32-bit
     VLQ reader: `decode_pvalue_to_bytes` raises for an element of 2^40, and
     `skip_typed_value` stops one byte short, desynchronising the walk.
  2. `encode_typed_value(BLOB)` omits the BlobRootId that `decode_pvalue_to_bytes`
     and `skip_typed_value` expect; decoding its output returns the wrong bytes.
  3. `encode_pvalue_typed(S7STRING)` produces a value `decode_pvalue_to_bytes`
     rejects ("Unsupported PValue datatype: 0x19").
  4. `skip_typed_value` does not handle packed structs: on a packed struct it stops
     at offset 7 where `decode_pvalue_to_bytes` correctly consumes 19 bytes.

  Arrays and structs wait until their element encodings are pinned with captures,
  because the Python reference cannot serve as the oracle there.

## Phase 1 results (VLQ and frames)

Phase 1 is done: all four VLQ widths and complete frames.

- **Signed 32- and 64-bit VLQ** (`LeanS7CommPlus.VlqSigned`): a signed VLQ of `n`
  groups is the `7n`-bit two's-complement value of its groups (the 64-bit nine-byte
  form is a 64-bit two's-complement value). The encoders reproduce Python byte for
  byte, including its non-minimal choices: Python sizes the encoding from the
  absolute value, so -64 becomes `ff 40` although `40` decodes to -64 too. Theorems:
  round trips for both widths inside arbitrary surrounding bytes, and the int32
  canonical form: the accepted bytes are exactly the two's-complement pattern of
  the value over the number of groups read. The group count is the only freedom,
  which covers both sign extension and Python's non-minimal encodings. The decoders
  reject values outside the type's range, which `decode_int32_vlq` returns.

- **Unsigned 32- and 64-bit VLQ** (`LeanS7CommPlus.Vlq`): encoders that match the
  Python reference byte for byte (known-answer tests on boundary values, including
  the nine-byte 64-bit form for values of 2^56 and above), decoders, and theorems:
  round trip inside arbitrary surrounding bytes for both widths, encoded size
  bounds, and a canonical-form theorem for 32 bits: the only non-minimal input the
  decoder accepts is the minimal encoding preceded by `0x80` bytes.
- **Frames** (`LeanS7CommPlus.Frame`): strict decoding of a complete frame
  (header, data, trailer with the same version and a zero word, nothing after it),
  with a round trip and a canonical-form theorem. All 13 complete frames of the
  CPU 1214C session in `fixtures/` decode and re-encode byte for byte: V1 for
  InitSSL and CreateObject, V2 for SetupSession, V3 for everything after it.
- **Divergences from the Python decoders**, found while porting and kept as
  intended (decision 4 keeps only the overlong-encoding leniency):
  - `decode_uint32_vlq` returns values that do not fit 32 bits: `ff ff ff ff 7f`
    gives 2^35 − 1. The Lean decoder rejects it.
  - `decode_uint32_vlq` stops after five bytes and ignores a continuation flag on
    the fifth: `80 80 80 80 80` gives 0. The Lean decoder rejects it.
  - `decode_int32_vlq` returns values outside the int32 range: `8f ff ff ff 7f`
    gives 4294967295. The Lean decoder rejects it.
- **Effort.** The proof style from lean-s7 carried over unchanged: the cursor
  append lemmas give the round trips by induction over the group list, and the
  reverse-read lemmas give the canonical forms. Each codec took a few build
  iterations, mostly offset arithmetic.

## Phase 0 results

- **Skeleton.** A Lake project on Lean 4.33.1 with lean-s7 as a dependency, pinned
  to lean-s7 `main` at `69dbcb8` until lean-s7 0.3.0 is released. `LeanS7CommPlus.Protocol`
  holds the protocol id, frame versions, opcodes and the function codes the
  Python client sends. CI builds and runs the tests and the axiom audit on Linux
  and macOS; Windows is informational, as in lean-s7.
- **Fixtures.** `fixtures/` holds two captures from real controllers, each with
  device, firmware, source and capturer:
  - a complete V1 SessionKey session on a CPU 1214C FW V4.2.2 (s7commplus#136):
    InitSSL, CreateObject, SetupSession, the session activation, two reads and a
    write the PLC rejects with a SystemEvent. It shows the V2 setup frame and the
    V3/HMAC frames that follow;
  - four GetMultiVariables replies with failing items from a CPU 1512SP-1 FW V2.9
    (s7commplus#129).
- **Decoder classification.** The Python decoders examined so far:

| Python decoder | Class | Ignored or ambiguous input |
| --- | --- | --- |
| `codec.decode_header` | strict | none of the four header bytes; the version byte is passed through unchecked |
| `vlq.decode_{uint,int}{32,64}_vlq` | lenient | overlong encodings: leading zero groups (`80 00` = `00` = 0), and for signed values redundant sign groups (`ff 7f` = `7f` = −1) |
| `codec.decode_response_header` | lenient | the reserved words at offsets 1–2 and 5–6; the opcode is returned but not checked |
| `codec.decode_wstring` | strict, but truncation-lenient | UTF-8 decoding is injective; a field shorter than `length` decodes the shorter string and still reports `length` bytes consumed |
| `codec.decode_pvalue_to_bytes` | lossy | returns only the value bytes, not the flags or datatype; VLQ arrays are re-encoded minimally, which normalises overlong input; fixed-size reads slice and can silently come up short |
| `codec.parse_create_object_session_id` | lenient prefix reader | a missing object-count byte reads as 0; no end-of-input check |
| `codec.parse_create_object_attributes` | scanner | skips elements it does not recognise; stops silently on truncation |
| `client._parse_read_response` | lenient | bytes after the error list (IntegrityId, fill) are unread; a special one-byte S7-1200 scalar shape is accepted |
| `typeinfo`, `subscription`, `alarm`, `values` parsers | to classify | when their layer is ported (phases 2–3) |

  The recurring pattern is **silent truncation**: Python slices return short
  data instead of failing. The Lean decoders will reject truncated input, and the
  differential fuzzer will report those cases as "Lean rejects"; that is an
  intended divergence, not a bug in either.

## Goal

An executable specification of S7CommPlus in Lean 4, with machine-checked
properties at the protocol boundaries, tested differentially against the Python
[s7commplus](https://github.com/gijzelaerr/s7commplus) package. This is the same
role [lean-s7](https://github.com/gijzelaerr/lean-s7) plays for classic S7 and
python-snap7: an independent implementation whose disagreements with the Python
code expose ambiguous assumptions, and whose proofs pin down what the codecs
accept.

Concretely, the end state is:

- pure codecs for every layer the Python client uses, each with a round-trip
  theorem and a canonical-form theorem (or an explicit, proved list of what it
  ignores);
- a client that can connect, read, write and browse against the Python
  `S7CommPlusServer` emulator, then against captures from real PLCs;
- a portable conformance corpus that the Python package can run as well.

## Non-goals

- A production driver. Like lean-s7, this is exploratory and must not be
  connected to production equipment.
- Classic S7comm. That is lean-s7.
- Proving anything about what a PLC *does*. Proofs are about bytes and state
  machines. Controller behaviour comes from captures and hardware runs and is
  recorded as evidence, not as theorems.
- Proving cryptographic algorithms correct. Where crypto is needed, the plan
  treats it as a black box checked against known-answer vectors (see open
  decision 3).

## What S7CommPlus looks like on the wire

Facts below are from the Python implementation and the captures in its issues.
Where the Python docstrings and code disagree, the code wins.

- **Transport.** TPKT (RFC 1006) and COTP class 0, as in classic S7. TLS 1.3 is
  layered on top after an InitSSL exchange for V2 sessions.
- **Frame.** Each S7CommPlus PDU sits in a frame: `0x72`, a version byte, a
  big-endian length, the data, and a trailer `72 vv 00 00`. Large PDUs are split
  over several fragments.
- **Frame version is not the session version.** The session version comes from
  the PLC's CreateObject reply. The frame version depends on the session's
  security: plain V1 sessions use V1 frames; sessions with a V1 SessionKey use
  **V3 frames with an HMAC-SHA256 prefix** (seen in s7commplus#136); the session
  setup write is always a V2 frame. The model must keep the two apart.
- **Versions.** V1: no TLS, optionally the legacy SessionKey (S7-1200 FW V4.2,
  S7-1500 FW V2.6–2.9). V2: TLS plus IntegrityId tracking; the client refuses V2
  without TLS. V3: HMAC-protected frames.
- **Headers.** A request is opcode `0x31`, a reserved word, the function code, a
  reserved word, a sequence number, the session id and transport flags. A
  response mirrors it with opcode `0x32`. With integrity tracking, an IntegrityId
  (a VLQ) follows, and its position differs by key family (PLCSIM puts it after
  the body for set operations).
- **VLQ.** Unsigned and signed 32/64-bit variable-length integers, 7 bits per
  byte with a continuation bit; the signed form uses bit 6 of the first byte as
  the sign; the 64-bit form uses all 8 bits of a ninth byte. **The Python
  decoder accepts overlong encodings**: `80 00` decodes to 0 and `ff 7f` to −1,
  the same values as `00` and `7f`. VLQ decoding is therefore lenient, not
  canonical.
- **PValues.** Typed values: a flags byte, a datatype byte, then the value
  (fixed-width integers, floats, VLQ-encoded integers, WStrings, BLOBs, arrays
  and structs).
- **Object model.** A tagged tree: `A1` start of object (relation id, class id,
  class flags, attribute id), `A3` attribute, `A4` relation, `A2` end of object,
  plus tag descriptions, type info and variable-name lists in EXPLORE replies.
- **Integrity and security.** IntegrityId counters (separate for reads and
  writes), HMAC-SHA256 over V3 frames (fragments chained in two dialects:
  state-resume on real PLCs, feed-forward on PLCSIM), the V1 SessionKey handshake
  (AES-GCM/ECB, key derivation, a 180- or 216-byte blob), and password
  legitimation (legacy SHA-1 XOR, or AES-256-CBC with a TLS-derived key).

## Layer inventory

Each row is a candidate Lean module. "Python source" is the reference for
behaviour and test vectors, not code to translate.

| Layer | Python source | Encode / decode entry points | Proof target |
| --- | --- | --- | --- |
| TPKT / COTP | `transport.py` | connect, data TPDUs | Reuse lean-s7 (open decision 1) |
| Frame and fragments | `codec.py` `encode_header`/`decode_header`, `connection.py` reassembly | frame, trailer, fragment split/join | round trip, exact length, fragment reassembly order and bound |
| VLQ | `vlq.py` (4 encoders, 4 decoders) | `encode_/decode_{uint,int}{32,64}_vlq` | round trip, encoded size, **lenient** canonical form (overlong prefixes) |
| Fixed-width scalars, floats, WString | `codec.py` | `encode_/decode_uint8…float64`, `encode_/decode_wstring` | round trip; floats through bits |
| PValue | `codec.py` | `encode_typed_value`, `encode_pvalue_*`, `decode_pvalue_to_bytes`, `skip_typed_value` | round trip per datatype, extent of `skip_typed_value` |
| Request/response headers | `codec.py` | `encode_request_header`, `decode_response_header` | round trip, reserved-field leniency |
| Object tree | `codec.py`, `object_model.py` | `parse_create_object_*`, EXPLORE builders | balanced start/end, attribute extent, canonical form |
| IntegrityId | `connection.py` | `_strip_response_integrity_id`, `_response_payload` | position by key family as a parameter, counter monotonicity |
| HMAC framing | `connection.py`, `_fragment_hmac.py` | V3 frame build/verify, fragment chaining | composition with a black-box HMAC (open decision 3) |
| SessionKey | `v1_session_key/` | `authenticate_*`, blob metadata, key derivation | blob layout only; crypto per open decision 3 |
| Legitimation | `legitimation.py`, `v1_session_key/legitimation.py` | legacy and new | message layout only |
| Data access | `client.py` | GetMultiVariables, SetMultiVariables builders/parsers | item correlation and per-item errors (cf. s7commplus#129, #130) |
| Browse and typeinfo | `typeinfo.py`, `tag_browser.py`, `catalog.py` | EXPLORE parsing, symbol tree | extent and tree well-formedness |
| Subscriptions and alarms | `subscription.py`, `alarm.py` | CreateObject subscription, notifications | encoding round trip, notification extent |
| Session state machine | `connection.py` | InitSSL → CreateObject → SetupSession → activation → legitimation | legal transitions, as lean-s7's `Lifecycle` |

## Phase 0: skeleton and classification

1. Lake project on the lean-s7 toolchain (Lean 4.33.1), with the same required
   checks: build, tests, an axiom audit that resolves every theorem cited in the
   docs, and Linux/macOS CI (Windows informational, as in lean-s7).
2. Classify every decoder in the inventory as **strict**, **lenient** or
   **lossy** before proving anything about it, as the lean-s7 canonical-decoding
   plan did. Known so far: VLQ is lenient (overlong encodings); request and
   response headers are lenient (reserved words); `decode_pvalue_to_bytes` is
   lossy by design (it returns raw bytes regardless of type).
3. Collect fixtures: frames and replies from real hardware already in the
   s7commplus issues (the CPU 1214C V4.2 session in #136, the four S7-1500
   GetMultiVariables replies in #129, the EXPLORE captures behind #135/#137), with
   CPU, firmware and source recorded for each.

## Phase 1: pilot — VLQ and frames

VLQ and the frame header are small, self-contained and used everywhere. The
pilot measures effort per codec and fixes the proof style.

- `Vlq.encode/decode` for the four widths, with round trip, size bounds
  (1–5 bytes for 32-bit, 1–9 for 64-bit) and a lenient canonical theorem:
  decoding accepts exactly the minimal encoding plus overlong zero-group
  prefixes (or the minimality check of open decision 4).
- Frame header and trailer encode/decode, with round trip and exact length.
- Known-answer tests against the Python encoders for every boundary value.

## Phase 2: values and the object tree

- Scalars, floats, WString, BLOB, PValue with flags and datatype, arrays.
- The object tree as an inductive type with an encoder and a decoder; proofs that
  decoded trees are balanced, that every attribute's extent is exact, and a
  canonical-form theorem.
- `skip_typed_value` extent: it consumes exactly the value `decode` would read.

## Phase 3: messages

- Request and response headers, IntegrityId placement as an explicit parameter
  (`IntegrityLayout` per key family), CreateObject / SetupSession / GetMultiVariables
  / SetMultiVariables / EXPLORE / DeleteObject builders and parsers.
- Per-item result correlation for multi-reads and multi-writes, including the
  partial-failure replies of s7commplus#129 and the duplicate missing-DB answer of
  #130.

## Phase 4: plain V1 against the emulator

The Python `S7CommPlusServer` serves three session paths: plain V1, V1 with a
SessionKey (V3/HMAC frames), and V2 over TLS. The first live milestone is the
only one that needs no crypto: **plain V1**.

- Connect, CreateObject, SetupSession, read, write and browse against
  `python -m s7commplus.server`, driven from a Python harness as lean-s7 does with
  python-snap7.
- A session state machine with proved legal transitions.
- A differential fuzzer: mutate valid replies and compare the Lean decoders with
  the Python ones (accept-equal, both-reject, one-rejects, accept-different).

## Phase 5: integrity and security

Depends on open decision 3.

- HMAC-SHA256 framing for V3 frames and both fragment-chaining dialects, proved
  correct *relative to* an HMAC function; the HMAC itself is checked with
  known-answer vectors.
- IntegrityId counters.
- The V1 SessionKey blob layout and handshake sequence; the cipher steps behind
  the same black-box boundary.
- Live milestone: V1 with a SessionKey against the emulator's `session_key`
  mode.

## Phase 6: TLS (V2)

TLS needs a native library; Lean core has none. Only if open decision 3 chooses
FFI. Otherwise V2 stays out of scope and the plan says so.

## Evidence and hardware boundaries

These are controller facts, not theorems. Each is a named parameter in the Lean
model, with the evidence that fixes its value:

- whether a key family needs the address-323 session activation, and what breaks
  if it is sent (s7commplus#104, #136);
- the IntegrityId position per key family and function code;
- the legitimation mode per family and firmware;
- the multi-item cap per request (50 on an S7-1200);
- frame and fragment sizes per firmware.

A capture qualifies only the conversation it shows, as in lean-s7's H1 gate.

## Provenance and licensing

- This repository is MIT, like lean-s7 and s7commplus.
- `thomas-v2/S7CommPlusDriver` is LGPL-3.0. Do not translate its code. Constants
  and ids may be used with a citation (file and line), as the s7commplus pull
  request template requires.
- The V1 SessionKey algorithm in s7commplus is a port of
  [bonk-dev/HarpoS7](https://github.com/bonk-dev/HarpoS7) (MIT), itself a
  clean-room re-implementation. If any of it is ported here, its licence notice
  and attribution must come with it.
- Siemens, S7, SIMATIC and TIA Portal are trademarks of Siemens AG. This project
  is not affiliated with Siemens.

## Open decisions for the owner

1. **Depend on lean-s7?** *Provisional: yes, pinned to a commit.* A Lake
   dependency reuses `Binary`/`Cursor`, TPKT, COTP and the reverse-read and
   `ByteArray.extract` lemmas from the canonical-decoding work, and ties this repo
   to lean-s7's toolchain. Those lemmas landed after lean-s7 0.2.0, so phase 0
   pins lean-s7 `main` at `69dbcb8`; the pin moves to the 0.3.0 tag once that is
   released. The alternative is copying the few modules needed.
2. **Proof standard.** Require a canonical-form theorem (or proved leniency) for
   every decoder in the same PR that adds it, as lean-s7's plan now asks? That
   keeps the proofs current but slows the first live milestone.
3. **Crypto and TLS.** *Decided 2026-10-29: plain V1 first; crypto is out of
   scope for now.* Lean core has no SHA, HMAC, AES or TLS. Options for later:
   (a) pure-Lean implementations, checked only against known-answer vectors from
   the Python code; (b) FFI to a C library (OpenSSL or mbedTLS), which gives TLS
   too but adds a native dependency; (c) stop at plain V1 and keep crypto out of
   scope for now. Phases 5 and 6 depend on this.
4. **VLQ strictness.** Keep the Python decoder's leniency (overlong encodings
   accepted, proved as such), or decode strictly and record the difference as a
   divergence? Strict decoding could reject something a PLC sends; there is no
   capture showing either way.
5. **Scope of the first release.** Codecs only (phases 1–3), or codecs plus the
   plain V1 client (phase 4)?
