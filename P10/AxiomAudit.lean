import P10.Certs.P1
import P10.Bound
import P10.Sha256
import P10.Fixtures

/-!
# Axiom audit

Every declaration below must print `does not depend on any axioms`
(no `propext`, no `Classical.choice`, no `Quot.sound`, no `sorryAx`, no
`Lean.ofReduceBool`). `scripts/verify.sh` fails if any line differs, and fails if the
number of audited declarations differs from the number of `#print axioms` lines here.
-/

#print axioms P10.certificate_sound
#print axioms P10.underdetermined_has_certificate
#print axioms P10.underdetermined_iff_certificate
#print axioms P10.determinate_not_underdetermined
#print axioms P10.underdetermined_not_determinate
#print axioms P10.underdetermined_nonempty_compatible
#print axioms P10.empty_compatible_neither
#print axioms P10.no_certificate_does_not_imply_determinate
#print axioms P10.FormallyUnderdeterminationCapable.profileAdmissible
#print axioms P10.worlds_distinct_of_values_differ
#print axioms P10.UnderdeterminationCertificate.target
#print axioms P10.UnderdeterminationCertificate.ofTarget
#print axioms P10.S1.checkTarget_sound
#print axioms P10.S1.determinate_of_check
#print axioms P10.S1.fuc
#print axioms P10.S1.profileAdmissible
#print axioms P10.S1.p1Certificate
#print axioms P10.S1.p1_pass
#print axioms P10.S1.n1_determined_no_certificate
#print axioms P10.S1.n1_determined_no_target
#print axioms P10.S1.n2_incompatible_rejected
#print axioms P10.S1.n2_incompatible_rejected'
#print axioms P10.S1.n3_same_value_rejected
#print axioms P10.S1.n3_witnesses_compatible_and_distinct
#print axioms P10.S1.eU_determinate_for_firstBit
#print axioms P10.S1.n3_same_world_rejected
#print axioms P10.S1.m3_outside_world_rejected
#print axioms P10.S1.m3_outside_world_diverges_and_compatible
#print axioms P10.S1.outside_evidence_rejected
#print axioms P10.S1.n4_inconsistent_neither
#print axioms P10.S1.n4_no_certificate_not_determinate
#print axioms P10.S1.firstPair_sound
#print axioms P10.S1.findWitness_sound
#print axioms P10.S1.none_does_not_decide_determinacy
#print axioms P10.Wire.decode_encode
#print axioms P10.Wire.listEq_sound
#print axioms P10.Wire.holds_of_check
#print axioms P10.Wire.holds_iff
#print axioms P10.Wire.not_holds_of_decode_none
#print axioms P10.Sha256.sha256
#print axioms P10.bound_of_check
#print axioms P10.Bound.holds
#print axioms P10.Bound.digest
#print axioms P10.Certs.P1.digest
#print axioms P10.Certs.P1.holds
#print axioms P10.Certs.P1.decoded
#print axioms P10.Certs.P1.canonical
#print axioms P10.Certs.P1.cert
#print axioms P10.Certs.P1.underdetermined
