import P10.Certificate

/-!
# P10.Fixtures — the S1 reference profile (toy, finite, fully decidable)

`S1.profile` is a *test* profile: five worlds, seven evidence values, one claim.
It exists to exercise the certificate machinery. It is NOT a concrete P10 profile
for any real claim and makes no adequacy statement (profile §7.2: profile-adequacy
review is a separate gate).

World semantics: a world is two bits (first, second). `w00 w01 w10 w11` are in `Wπ`.
`wOut` is deliberately OUTSIDE `Wπ` although it would be compatible with some
evidence and would diverge on the claim (test for profile mutation M3).
Evidence `obs f s` reports the first bit and optionally the second.
`inconsistent` is in `Eπ` and compatible with no world. `outside` is NOT in `Eπ`.
-/

namespace P10.S1

inductive World where
  | w00 | w01 | w10 | w11 | wOut
  deriving DecidableEq, Repr

inductive Evidence where
  | obs (first : Bool) (second : Option Bool)
  | inconsistent
  | outside
  deriving DecidableEq, Repr

inductive Claim where
  | secondBit
  | firstBit
  deriving DecidableEq, Repr

def firstBit : World → Bool
  | .w00 | .w01 | .wOut => false
  | .w10 | .w11 => true

def secondBitOf : World → Bool
  | .w00 | .w10 => false
  | .w01 | .w11 | .wOut => true

-- NOTE: matches below list every constructor explicitly. Wildcard patterns over
-- enumeration types compile through `ctorIdx` lemmas that depend on `propext`,
-- which would break the zero-axiom policy (see AXIOM_POLICY.md).
def inWB : World → Bool
  | .w00 => true | .w01 => true | .w10 => true | .w11 => true | .wOut => false

def inEB : Evidence → Bool
  | .obs _ _ => true | .inconsistent => true | .outside => false

def obsCompat (f : Bool) (s : Option Bool) (w : World) : Bool :=
  (f == firstBit w) &&
    match s with
    | none => true
    | some b => b == secondBitOf w

def compatB : Evidence → World → Bool
  | .obs f s, w => obsCompat f s w
  | .inconsistent, .w00 => false | .inconsistent, .w01 => false
  | .inconsistent, .w10 => false | .inconsistent, .w11 => false
  | .inconsistent, .wOut => false
  | .outside, w => obsCompat false none w

def evalB : Claim → World → Bool
  | .secondBit, w => secondBitOf w
  | .firstBit, w => firstBit w

/-- The frozen S1 profile. Every relation is the `= true` reading of a `Bool` function. -/
def profile : P10.Profile where
  World := World
  Evidence := Evidence
  Claim := Claim
  Value := Bool
  inW := fun w => inWB w = true
  inE := fun e => inEB e = true
  compatible := fun e w => compatB e w = true
  eval := evalB

/-! ### Axiom-free Bool reflection helpers (no `simp`, no `Bool.and_eq_true`) -/

theorem and_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem bne_split {a b : Bool} (h : (a != b) = true) : a ≠ b := by
  cases a <;> cases b <;> first | exact absurd h (by decide) | exact fun e => Bool.noConfusion e

/-- Decision procedure for `CertificateTargetV0` on the S1 profile. -/
def checkTarget (e : Evidence) (c : Claim) (w0 w1 : World) : Bool :=
  inEB e && inWB w0 && inWB w1 && compatB e w0 && compatB e w1 &&
    (evalB c w0 != evalB c w1)

theorem checkTarget_sound {e : Evidence} {c : Claim} {w0 w1 : World}
    (h : checkTarget e c w0 w1 = true) :
    CertificateTargetV0 profile e c w0 w1 := by
  obtain ⟨h5, hd⟩ := and_split h
  obtain ⟨h4, c1⟩ := and_split h5
  obtain ⟨h3, c0⟩ := and_split h4
  obtain ⟨h2, i1⟩ := and_split h3
  obtain ⟨hE, i0⟩ := and_split h2
  exact ⟨hE, i0, i1, c0, c1, bne_split hd⟩

/-- Per-pair check for `Determinateπ` on the S1 profile: if both worlds are in `Wπ` and
compatible then the claim values agree. Encoded as a `Bool` implication. -/
def detPair (e : Evidence) (c : Claim) (w0 w1 : World) : Bool :=
  !(inWB w0 && inWB w1 && compatB e w0 && compatB e w1) || (evalB c w0 == evalB c w1)

theorem imp_split {p q : Bool} (h : (!p || q) = true) (hp : p = true) : q = true := by
  cases p <;> cases q <;> first | rfl | exact absurd h (by decide) | exact absurd hp (by decide)

theorem beq_split {a b : Bool} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Reflection lemma: a nonempty-compatible witness plus an all-pairs `detPair` check
yields `Determinateπ`. -/
theorem determinate_of_check {e : Evidence} {c : Claim} {w : World}
    (hw : inWB w = true) (hc : compatB e w = true)
    (hpairs : ∀ w0 w1, detPair e c w0 w1 = true) : Determinate profile e c := by
  refine ⟨⟨w, hw, hc⟩, ?_⟩
  intro w0 w1 h0 h1 hh
  have hp : (inWB w0 && inWB w1 && compatB e w0 && compatB e w1) = true := by
    obtain ⟨c0, c1⟩ := hh
    have h0' : inWB w0 = true := h0
    have h1' : inWB w1 = true := h1
    have c0' : compatB e w0 = true := c0
    have c1' : compatB e w1 = true := c1
    rw [h0', h1', c0', c1']
    rfl
  exact beq_split (imp_split (hpairs w0 w1) hp)

/-! ## Named fixtures -/

/-- `e_u`: first bit observed, second hidden. The claim is underdetermined. -/
def eU : Evidence := .obs false none
/-- `e_d`: both bits observed. The claim is determined. -/
def eD : Evidence := .obs false (some false)
/-- Claim under test: the second bit. -/
def c0 : Claim := .secondBit
/-- Claim `firstBit`: determined by `eU`. -/
def c1 : Claim := .firstBit

/-- The S1 profile is formally underdetermination-capable for `c0`
(profile §2.1): `eU` underdetermines, `eD` determines. -/
theorem fuc : FormallyUnderdeterminationCapable profile c0 :=
  ⟨eU, eD, rfl, rfl,
    ⟨.w00, .w01, rfl, rfl, rfl, rfl,
      by change evalB c0 .w00 ≠ evalB c0 .w01; decide⟩,
    determinate_of_check (w := .w00) rfl rfl (by intro w0 w1; cases w0 <;> cases w1 <;> rfl)⟩

theorem profileAdmissible : ProfileAdmissible profile c0 :=
  fuc.profileAdmissible

/-- **P1 (positive fixture).** Same evidence `eU`, both witnesses compatible,
claim values differ: the certificate is constructed and `Underdetermined` follows. -/
def p1Certificate : UnderdeterminationCertificate profile eU c0 :=
  UnderdeterminationCertificate.ofTarget (w₀ := .w00) (w₁ := .w01)
    (checkTarget_sound (by decide))

theorem p1_pass : Underdetermined profile eU c0 := certificate_sound p1Certificate

/-- **N1.** Evidence that determines the claim admits no certificate, for any
witness pair (kill-test N1). -/
theorem n1_determined_no_certificate :
    ¬ Nonempty (UnderdeterminationCertificate profile eD c0) := by
  intro ⟨k⟩
  exact determinate_not_underdetermined (determinate_of_check (w := .w00) rfl rfl (by intro w0 w1; cases w0 <;> cases w1 <;> rfl))
    (certificate_sound k)

/-- **N1 (target form).** No witness pair satisfies `CertificateTargetV0` for `eD`. -/
theorem n1_determined_no_target (w0 w1 : World) :
    ¬ CertificateTargetV0 profile eD c0 w0 w1 := by
  intro h
  exact n1_determined_no_certificate ⟨UnderdeterminationCertificate.ofTarget h⟩

/-- **N2.** `w10` is not compatible with `eU`, so the pair `(w00, w10)` is not a target
even though the claim values differ... (values are equal here; the incompatible pair
`(w10, w01)` has differing values and is still rejected). -/
theorem n2_incompatible_rejected :
    ¬ CertificateTargetV0 profile eU c0 .w10 .w01 := by
  intro h
  have : compatB eU World.w10 = true := h.2.2.2.1
  exact absurd this (by decide)

/-- **N2 (second witness).** Symmetric case. -/
theorem n2_incompatible_rejected' :
    ¬ CertificateTargetV0 profile eU c0 .w00 .w11 := by
  intro h
  have : compatB eU World.w11 = true := h.2.2.2.2.1
  exact absurd this (by decide)

/-- **N3.** Both witnesses are in `Wπ` and compatible with `eU`, they are distinct
worlds, but `Eval` is identical: for the claim `firstBit`, `eU` observes the first bit,
so `w00` and `w01` agree. Rejected (and in fact `eU` is `Determinate` for `c1`). -/
theorem n3_same_value_rejected :
    ¬ CertificateTargetV0 profile eU c1 .w00 .w01 := by
  intro h
  exact h.2.2.2.2.2 rfl

theorem n3_witnesses_compatible_and_distinct :
    compatB eU World.w00 = true ∧ compatB eU World.w01 = true ∧
    World.w00 ≠ World.w01 := by
  decide

/-- Claim-relativity: the same evidence `eU` is determinate for `firstBit`. -/
theorem eU_determinate_for_firstBit : Determinate profile eU c1 :=
  determinate_of_check (w := .w00) rfl rfl (by intro w0 w1; cases w0 <;> cases w1 <;> rfl)

/-- Same value on the same world twice is likewise rejected. -/
theorem n3_same_world_rejected :
    ¬ CertificateTargetV0 profile eU c0 .w00 .w00 := by
  intro h
  exact h.2.2.2.2.2 rfl

/-- **M3.** `wOut` is compatible with `eU` and diverges from `w00` on `c0`,
but `wOut ∉ Wπ`: rejected. -/
theorem m3_outside_world_rejected :
    ¬ CertificateTargetV0 profile eU c0 .w00 .wOut := by
  intro h
  have : inWB World.wOut = true := h.2.2.1
  exact absurd this (by decide)

theorem m3_outside_world_diverges_and_compatible :
    compatB eU World.wOut = true ∧ evalB c0 World.w00 ≠ evalB c0 World.wOut := by
  decide

/-- **e ∉ Eπ.** Evidence outside `Eπ` is rejected even with a divergent compatible pair. -/
theorem outside_evidence_rejected (w0 w1 : World) :
    ¬ CertificateTargetV0 profile Evidence.outside c0 w0 w1 := by
  intro h
  have : inEB Evidence.outside = true := h.1
  exact absurd this (by decide)

/-- **N4.** Empty-compatible evidence: no certificate exists, AND `Determinate` fails.
Failure to produce a certificate is therefore not determinacy. -/
theorem n4_inconsistent_neither :
    ¬ Underdetermined profile .inconsistent c0 ∧
    ¬ Determinate profile .inconsistent c0 := by
  apply empty_compatible_neither
  intro ⟨w, _, hc⟩
  have hc' : compatB Evidence.inconsistent w = true := hc
  cases w <;> exact absurd hc' (by decide)

theorem n4_no_certificate_not_determinate :
    ¬ Nonempty (UnderdeterminationCertificate profile .inconsistent c0) ∧
    ¬ Determinate profile .inconsistent c0 :=
  ⟨fun ⟨k⟩ => n4_inconsistent_neither.1 (certificate_sound k), n4_inconsistent_neither.2⟩

/-! ### A concrete witness search, and why its failure is uninformative -/

def allPairs : List (World × World) :=
  [(.w00,.w00),(.w00,.w01),(.w00,.w10),(.w00,.w11),(.w00,.wOut),
   (.w01,.w00),(.w01,.w01),(.w01,.w10),(.w01,.w11),(.w01,.wOut),
   (.w10,.w00),(.w10,.w01),(.w10,.w10),(.w10,.w11),(.w10,.wOut),
   (.w11,.w00),(.w11,.w01),(.w11,.w10),(.w11,.w11),(.w11,.wOut),
   (.wOut,.w00),(.wOut,.w01),(.wOut,.w10),(.wOut,.w11),(.wOut,.wOut)]

/-- First pair in the list satisfying the certificate-target check. -/
def firstPair (e : Evidence) (c : Claim) : List (World × World) → Option (World × World)
  | [] => none
  | p :: ps =>
    match checkTarget e c p.1 p.2 with
    | true => some p
    | false => firstPair e c ps

/-- A (deliberately naive, exhaustive) witness search over pairs of worlds. -/
def findWitness (e : Evidence) (c : Claim) : Option (World × World) :=
  firstPair e c allPairs

/-- Search is sound: `some` yields a certificate target. (No completeness is claimed or
needed: `none` is never used to conclude anything.) -/
theorem firstPair_sound {e : Evidence} {c : Claim} :
    ∀ {l : List (World × World)} {p : World × World},
      firstPair e c l = some p → CertificateTargetV0 profile e c p.1 p.2
  | [], _, h => by cases h
  | q :: qs, p, h => by
    unfold firstPair at h
    cases hc : checkTarget e c q.1 q.2 with
    | true =>
      rw [hc] at h
      have hq : q = p := Option.some.inj h
      subst hq
      exact checkTarget_sound hc
    | false =>
      rw [hc] at h
      exact firstPair_sound h

theorem findWitness_sound {e : Evidence} {c : Claim} {p : World × World}
    (h : findWitness e c = some p) : CertificateTargetV0 profile e c p.1 p.2 :=
  firstPair_sound h

/-- **E (concrete).** `findWitness = none` holds for BOTH a determined evidence and an
empty-compatible evidence; only the former is `Determinate`. So `none` does not decide
determinacy. -/
theorem none_does_not_decide_determinacy :
    findWitness eD c0 = none ∧ findWitness .inconsistent c0 = none ∧
    Determinate profile eD c0 ∧ ¬ Determinate profile .inconsistent c0 :=
  ⟨by decide, by decide,
   determinate_of_check (w := .w00) rfl rfl (by intro w0 w1; cases w0 <;> cases w1 <;> rfl),
   n4_inconsistent_neither.2⟩

end P10.S1
