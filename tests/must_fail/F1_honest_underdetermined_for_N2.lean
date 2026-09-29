import P10

/-! MUST FAIL (F1 regression, M34): N2 (named witness w10 is incompatible) certified via the other pair (w00,w01).
The evidence/claim ARE `Underdetermined` through a different pair, but `Holds` now demands
`CertificateTargetV0` for the witnesses NAMED IN THE BYTES, so this proof term is ill-typed. -/
open P10 P10.S1 P10.Wire
set_option maxRecDepth 100000

def b : List Nat := filebytes% "vectors/negative/n2_incompatible.json"
theorem dec : decode b = some ⟨.secondBit, .obs false none, .w01, .w10⟩ := by decide
theorem ud : Underdetermined profile eU c0 :=
  ⟨.w00, .w01, rfl, rfl, rfl, rfl, by change evalB c0 .w00 ≠ evalB c0 .w01; decide⟩

theorem bad : Holds b := (holds_iff dec).2 ⟨listEq_sound (by decide), ud⟩
