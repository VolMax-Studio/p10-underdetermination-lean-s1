import P10.Wire
import P10.Sha256

/-!
# P10.Bound — digest-bound statement

`Bound b d` says: the byte string `b` has SHA-256 digest `d` (checked by the Lean kernel via
`P10.Sha256`), AND `Holds b` (it decodes canonically to an instance that is `Underdetermined`).

The checker-owned proposition for a signed statement is
`Bound (filebytes% "<instance path>") (hex% "<instance sha256 stated in the statement>")`,
so the digest that appears in the statement is *kernel-verified* to be the digest of the very bytes
whose decoded proposition was proved. This closes the "proved proposition ≠ stated proposition"
gap for the instance bytes without trusting an external hashing script for that link.
-/

namespace P10

open P10.Wire P10.Sha256

/-- A `structure` (not a `def`) on purpose: two `Bound` propositions are compared by their
arguments only, so a certificate for other bytes/digest is rejected by a fast, clean type
mismatch instead of the elaborator trying to evaluate SHA-256 during unification. -/
structure Bound (b d : List Nat) : Prop where
  digest : sha256 b = d
  holds : Holds b

theorem bound_of_check {b d : List Nat} (hc : check b = true)
    (hd : listEq (sha256 b) d = true) : Bound b d :=
  ⟨listEq_sound hd, holds_of_check hc⟩

end P10
