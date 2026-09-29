import P10

/-!
N4 — no witness found ⟹ no certificate ⟹ NOT `Determinate`.
Search is not a theorem: absence of a certificate is compatible with both a determined
and an empty-compatible evidence, and the latter is not `Determinate` (profile §2.1
requires `NonemptyCompatibleπ`).
-/

open P10 P10.S1 P10.Wire

def n4 : List Nat := filebytes% "vectors/negative/n4_empty_compatible.json"

/-- Generic schema (any profile): a countermodel with no certificate and no determinacy. -/
theorem schema :
    ∃ (π : Profile) (e : π.Evidence) (c : π.Claim),
      ¬ Nonempty (UnderdeterminationCertificate π e c) ∧ ¬ Determinate π e c :=
  no_certificate_does_not_imply_determinate

/-- Concrete S1: empty-compatible evidence is neither underdetermined nor determinate. -/
theorem n4_neither :
    ¬ Underdetermined profile .inconsistent c0 ∧ ¬ Determinate profile .inconsistent c0 :=
  n4_inconsistent_neither

theorem n4_search_failure_not_determinate :
    ¬ Nonempty (UnderdeterminationCertificate profile .inconsistent c0) ∧
    ¬ Determinate profile .inconsistent c0 :=
  P10.S1.n4_no_certificate_not_determinate

/-- The exhaustive search returns `none` for BOTH a determinate and a non-determinate
evidence, so `none` carries no information about determinacy. -/
theorem search_none_is_uninformative :
    findWitness eD c0 = none ∧ findWitness .inconsistent c0 = none ∧
    Determinate profile eD c0 ∧ ¬ Determinate profile .inconsistent c0 :=
  none_does_not_decide_determinacy

theorem n4_wire_rejected : check n4 = false := by decide

#print axioms schema
#print axioms n4_neither
#print axioms search_none_is_uninformative
#print axioms n4_wire_rejected
