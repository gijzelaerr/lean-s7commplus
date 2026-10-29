# Plan: a proved S7CommPlus implementation in Lean

Status: draft, 2026-10-29. Nothing is implemented yet. The open decisions at the
end need owner review before phase 0 starts.

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

1. **Depend on lean-s7?** A Lake dependency reuses `Binary`/`Cursor`, TPKT, COTP
   and the reverse-read and `ByteArray.extract` lemmas from the canonical-decoding
   work, and ties this repo to lean-s7's toolchain. Those lemmas landed after
   lean-s7 0.2.0, so this either waits for a lean-s7 0.3.0 release or pins a
   commit. The alternative is copying the few modules needed.
2. **Proof standard.** Require a canonical-form theorem (or proved leniency) for
   every decoder in the same PR that adds it, as lean-s7's plan now asks? That
   keeps the proofs current but slows the first live milestone.
3. **Crypto and TLS.** Lean core has no SHA, HMAC, AES or TLS. Options:
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
