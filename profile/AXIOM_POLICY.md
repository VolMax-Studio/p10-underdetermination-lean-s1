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

Elaboration-time metaprograms are limited to `P10/Bytes.lean` (term elaborators that produce
`List Nat` literals). They are outside the kernel and are declared in THREAT_MODEL.md.
`scripts/lint_lean.py` ENFORCES this: `macro`, `macro_rules`, `syntax`, `notation`, `elab`, `run_cmd`,
`initialize`, `unif_hint`, `import Lean`, `open Lean`, `addDecl`, `setBool`, `withOptions`, kernel/debug
options, attributes and any `set_option` other than `maxRecDepth` are refused everywhere else, and
certificate modules (`P10/Certs/*.lean`) may contain only `import P10.*`, `set_option maxRecDepth`,
`namespace`, `end`, `open`, `def`, `theorem`.

The lint is a denylist and therefore only DEFENSE IN DEPTH. The boundaries are (1) kernel replay by the
toolchain's `leanchecker` over every module of the P10 library and the checker-owned modules (a
`#print axioms` line proves nothing about declarations added with the kernel skipped), and (2) the
checker-owned target being compiled in a separate Lean process before the certificate is loaded.
