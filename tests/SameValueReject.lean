import P10

/-!
N3 — both witnesses are in Wπ, distinct, and Compatible with the same evidence, but
`Eval` agrees: rejected. Here the claim `firstBit` is determined by the observed first bit.
-/

open P10 P10.S1 P10.Wire

def n3 : List Nat := filebytes% "vectors/negative/n3_same_value.json"

theorem n3_both_compatible_and_distinct :
    compatB eU World.w00 = true ∧ compatB eU World.w01 = true ∧ World.w00 ≠ World.w01 :=
  n3_witnesses_compatible_and_distinct
theorem n3_target_refuted : ¬ CertificateTargetV0 profile eU c1 .w00 .w01 := n3_same_value_rejected
theorem n3_wire_rejected : check n3 = false := by decide
/-- The evidence is in fact determinate for this claim. -/
theorem n3_evidence_determinate : Determinate profile eU c1 := eU_determinate_for_firstBit

#print axioms n3_wire_rejected
#print axioms n3_evidence_determinate
