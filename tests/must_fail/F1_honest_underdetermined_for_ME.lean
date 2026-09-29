import P10

/-! MUST FAIL (F1 regression, M34): M-E (evidence outside Eπ) certified without any Eπ membership.
The evidence/claim ARE `Underdetermined` through a different pair, but `Holds` now demands
`CertificateTargetV0` for the witnesses NAMED IN THE BYTES, so this proof term is ill-typed. -/
open P10 P10.S1 P10.Wire
set_option maxRecDepth 100000

def b : List Nat := filebytes% "vectors/negative/m_outside_evidence.json"
theorem dec : decode b = some ⟨.secondBit, .outside, .w00, .w01⟩ := by decide
theorem ud : Underdetermined profile .outside c0 :=
  ⟨.w00, .w01, rfl, rfl, rfl, rfl, by change evalB c0 .w00 ≠ evalB c0 .w01; decide⟩

theorem bad : Holds b := (holds_iff dec).2 ⟨listEq_sound (by decide), ud⟩
