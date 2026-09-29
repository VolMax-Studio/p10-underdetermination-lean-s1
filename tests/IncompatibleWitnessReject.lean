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
theorem mE_target_refuted (w0 w1 : World) :
    ¬ CertificateTargetV0 profile Evidence.outside c0 w0 w1 := outside_evidence_rejected w0 w1

#print axioms n2_wire_rejected
#print axioms m3_wire_rejected
#print axioms mE_wire_rejected
