# P10 S1 Axiom Policy

Accepted: declarations for which `#print axioms` reports
`does not depend on any axioms` (no `propext`, no `Quot.sound`, no `Classical.choice`,
no `sorryAx`, no `Lean.ofReduceBool`).

Forbidden in Lean sources: `sorry`, `admit`, `sorryAx`, `native_decide`,
`Lean.ofReduceBool`, `axiom` declarations, `unsafe`, `implemented_by`, `extern`,
`opaque`, `partial`, `@[csimp]`.

Reflection via `decide` (kernel evaluation of a `Decidable` instance or of a `Bool`
checker) is permitted: it is kernel-checked and axiom-free. `decide +kernel` and
`native_decide` are NOT used; `native_decide` would extend the TCB to the Lean compiler
and evaluator.

Elaboration-time metaprograms are limited to `P10/Bytes.lean` (two term elaborators that
produce `List Nat` literals). They are outside the kernel and are declared in
THREAT_MODEL.md.
