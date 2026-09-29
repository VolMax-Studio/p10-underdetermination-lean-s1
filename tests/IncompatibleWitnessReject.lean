import P10

/-!
N2 — one witness is not Compatible: rejected. (Also M3: a witness outside Wπ, and
evidence outside Eπ.) Each vector is otherwise "perfect": the values differ.
-/

open P10 P10.S1 P10.Wire

def n2 : List Nat := filebytes% "vectors/negative/n2_incompatible.json"
def m3 : List Nat := filebytes% "vectors/negative/m3_outside_world.json"
def mE : List Nat := filebytes% "vectors/negative/m_outside_evidence.json"

/-- In N2 the values genuinely differ; only compatibility fails. -/
theorem n2_values_differ : evalB c0 World.w01 ≠ evalB c0 World.w10 := by decide
theorem n2_w10_incompatible : compatB eU World.w10 = false := by decide
theorem n2_target_refuted : ¬ CertificateTargetV0 profile eU c0 .w10 .w01 :=
  n2_incompatible_rejected
theorem n2_wire_rejected : check n2 = false := by decide

/-- M3: `wOut` is compatible with `eU` and diverges, but is not in `Wπ`. -/
theorem m3_compatible_and_divergent :
    compatB eU World.wOut = true ∧ evalB c0 World.w00 ≠ evalB c0 World.wOut :=
  m3_outside_world_diverges_and_compatible
theorem m3_target_refuted : ¬ CertificateTargetV0 profile eU c0 .w00 .wOut := m3_outside_world_rejected
theorem m3_wire_rejected : check m3 = false := by decide

/-- Evidence outside Eπ. -/
theorem mE_wire_rejected : check mE = false := by decide

/-! Proposition-level rejection (F1 regression). Each vector is refuted for the witnesses NAMED IN
ITS BYTES, even though `Underdetermined` still holds for the same evidence/claim through a
DIFFERENT pair (`w00`,`w01`). -/
theorem n2_decodes : decode n2 = some ⟨.secondBit, .obs false none, .w01, .w10⟩ := by decide
theorem m3_decodes : decode m3 = some ⟨.secondBit, .obs false none, .w00, .wOut⟩ := by decide
theorem mE_decodes : decode mE = some ⟨.secondBit, .outside, .w00, .w01⟩ := by decide

theorem n2_not_holds : ¬ Holds n2 := not_holds_of_not_target n2_decodes n2_vector_target_refuted
theorem m3_not_holds : ¬ Holds m3 := not_holds_of_not_target m3_decodes m3_outside_world_rejected
theorem mE_not_holds : ¬ Holds mE :=
  not_holds_of_not_target mE_decodes (outside_evidence_rejected _ _)

/-- ... and the weaker fact is still true, which is exactly why `Holds` must not be weaker. -/
theorem weaker_fact_still_true : Underdetermined profile eU c0 := p1_pass
theorem mE_target_refuted (w0 w1 : World) :
    ¬ CertificateTargetV0 profile Evidence.outside c0 w0 w1 := outside_evidence_rejected w0 w1

#print axioms n2_wire_rejected
#print axioms m3_wire_rejected
#print axioms mE_wire_rejected
#print axioms n2_not_holds
#print axioms m3_not_holds
#print axioms mE_not_holds
