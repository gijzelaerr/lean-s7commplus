# lean-s7commplus repository guidance

lean-s7commplus is an exploratory Lean 4 implementation of the Siemens S7CommPlus
protocol with machine-checked codec properties. See
[the implementation plan](docs/plans/implementation.md) for scope, phases and the
owner's decisions.

## Layout

- `LeanS7CommPlus/`: the library. `LeanS7CommPlus.lean` imports every module.
- `Tests.lean`: deterministic unit and fixture tests (`lean-s7commplus-tests`).
- `AxiomAuditMain.lean`: fails if a project theorem depends on anything beyond
  `propext`, `Classical.choice` and `Quot.sound`, or if the README cites a theorem
  that does not exist (`lean-s7commplus-axioms`).
- `CliMain.lean`, `DecodeMain.lean`: the command-line client and the decoder oracle used by
  `integration/run.py` and `integration/fuzz.py`.
- `fixtures/`: frames and replies from real controllers, each file with the
  device, firmware, source URL and who captured it.
- Dependency: [lean-s7](https://github.com/gijzelaerr/lean-s7) for the byte cursor,
  big-endian codecs, TPKT/COTP and the reverse-read lemmas. The toolchain must stay
  identical to lean-s7's.

## Required checks

```console
lake build LeanS7CommPlus lean-s7commplus-tests lean-s7commplus-axioms lean-s7commplus-cli lean-s7commplus-decode
lake exe lean-s7commplus-tests
lake exe lean-s7commplus-axioms
python -m pip install "s7commplus==0.3.0"
python integration/run.py     # the Lean client against the Python emulator
python integration/fuzz.py    # differential fuzzer; accept-different must be 0
```

## Conventions

- Decoders are total `Except` functions over a bounded cursor; no panicking
  `ByteArray` indexing.
- Classify a decoder as strict, lenient or lossy before proving anything about it,
  and add its round-trip and canonical-form (or proved leniency) theorem in the same
  PR that adds it.
- Controller behaviour is evidence, not a theorem: model it as a named parameter
  and cite the capture or hardware run that fixes it.
- The Python [s7commplus](https://github.com/gijzelaerr/s7commplus) package is the
  behavioural reference. Do not translate code from thomas-v2/S7CommPlusDriver
  (LGPL-3.0); constants may be used with a citation. Code derived from
  bonk-dev/HarpoS7 (MIT) must keep its licence notice and attribution.
- Commit messages and PR descriptions follow lean-s7's conventions.
