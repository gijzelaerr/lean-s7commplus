# lean-s7commplus

An exploratory Lean 4 implementation of the Siemens S7CommPlus protocol, the
protocol used by S7-1200 and S7-1500 controllers for optimized and symbolic
access. It aims for machine-checked properties at the protocol boundaries:
round trips, exact lengths, and canonical decoding.

## Status

Planning. There is no code yet. The [implementation plan](docs/plans/implementation.md)
describes the layers, the phases, what will be proved, and the open decisions.

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
