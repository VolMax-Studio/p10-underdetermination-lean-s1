import P10.Core

/-!
# P10.Certificate — witness-carrying certificate and its meta-theorems

The certificate carries the two witness worlds and the proof obligations of
`CertificateTargetV0` (profile §2.2). It does not search for witnesses:
producing them is the generator's job, checking them is Lean's job.
A missing certificate is never evidence of determinacy (theorem E below).
-/

namespace P10

/-- A witness-carrying underdetermination certificate for `(π, e, c)`. -/
structure UnderdeterminationCertificate (π : Profile) (e : π.Evidence)
    (c : π.Claim) where
  w0 : π.World
  w1 : π.World
  evidence_mem  : π.inE e
  w0_mem        : π.inW w0
  w1_mem        : π.inW w1
  compatible_w0 : Compatible π e w0
  compatible_w1 : Compatible π e w1
  divergent     : Eval π c w0 ≠ Eval π c w1

namespace UnderdeterminationCertificate

variable {π : Profile} {e : π.Evidence} {c : π.Claim}

/-- The certificate's fields assemble exactly `CertificateTargetV0`. -/
theorem target (k : UnderdeterminationCertificate π e c) :
    CertificateTargetV0 π e c k.w0 k.w1 :=
  ⟨k.evidence_mem, k.w0_mem, k.w1_mem, k.compatible_w0, k.compatible_w1, k.divergent⟩

/-- Build a certificate from a proof of the checker-owned target. -/
def ofTarget {w₀ w₁ : π.World} (h : CertificateTargetV0 π e c w₀ w₁) :
    UnderdeterminationCertificate π e c :=
  ⟨w₀, w₁, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem worlds_distinct (k : UnderdeterminationCertificate π e c) : k.w0 ≠ k.w1 :=
  worlds_distinct_of_values_differ k.divergent

end UnderdeterminationCertificate

/-- **A. Soundness.** A valid certificate implies `Underdeterminedπ(e,c)`. -/
theorem certificate_sound {π : Profile} {e : π.Evidence} {c : π.Claim}
    (k : UnderdeterminationCertificate π e c) : Underdetermined π e c :=
  ⟨k.w0, k.w1, k.w0_mem, k.w1_mem, k.compatible_w0, k.compatible_w1, k.divergent⟩

/-- **B. Extraction (no choice principle).** For `e ∈ Eπ`, `Underdeterminedπ(e,c)`
implies that a certificate exists. Stated with `Nonempty` (a `Prop`), so that no
`Classical.choice` is needed: the witnesses are eliminated into a `Prop`. -/
theorem underdetermined_has_certificate {π : Profile} {e : π.Evidence}
    {c : π.Claim} (hE : π.inE e) (h : Underdetermined π e c) :
    Nonempty (UnderdeterminationCertificate π e c) := by
  obtain ⟨w₀, w₁, h0, h1, c0, c1, hd⟩ := h
  exact ⟨⟨w₀, w₁, hE, h0, h1, c0, c1, hd⟩⟩

/-- B, as an equivalence for evidence in `Eπ`. -/
theorem underdetermined_iff_certificate {π : Profile} {e : π.Evidence}
    {c : π.Claim} (hE : π.inE e) :
    Underdetermined π e c ↔ Nonempty (UnderdeterminationCertificate π e c) :=
  ⟨underdetermined_has_certificate hE, fun ⟨k⟩ => certificate_sound k⟩

/-- **C.** `Determinateπ(e,c) → ¬Underdeterminedπ(e,c)`. -/
theorem determinate_not_underdetermined {π : Profile} {e : π.Evidence}
    {c : π.Claim} (hD : Determinate π e c) : ¬ Underdetermined π e c := by
  intro hU
  obtain ⟨w₀, w₁, h0, h1, c0, c1, hd⟩ := hU
  exact hd (hD.2 w₀ w₁ h0 h1 ⟨c0, c1⟩)

/-- **D.** `Underdeterminedπ(e,c) → ¬Determinateπ(e,c)`. -/
theorem underdetermined_not_determinate {π : Profile} {e : π.Evidence}
    {c : π.Claim} (hU : Underdetermined π e c) : ¬ Determinate π e c :=
  fun hD => determinate_not_underdetermined hD hU

/-- `Underdeterminedπ` entails `NonemptyCompatibleπ`. -/
theorem underdetermined_nonempty_compatible {π : Profile} {e : π.Evidence}
    {c : π.Claim} (h : Underdetermined π e c) : NonemptyCompatible π e := by
  obtain ⟨w₀, _, h0, _, c0, _, _⟩ := h
  exact ⟨w₀, h0, c0⟩

/-- Empty-compatible evidence (profile §2.1: `Determinateπ` requires
`NonemptyCompatibleπ`) is neither underdetermined nor determinate. -/
theorem empty_compatible_neither {π : Profile} {e : π.Evidence} {c : π.Claim}
    (h : ¬ NonemptyCompatible π e) :
    ¬ Underdetermined π e c ∧ ¬ Determinate π e c :=
  ⟨fun hU => h (underdetermined_nonempty_compatible hU), fun hD => h hD.1⟩

/-- **E (schema).** Absence of a certificate does not imply `Determinateπ`:
there is a profile, evidence and claim with no certificate and no determinacy.
The witness is the empty-compatible model. -/
theorem no_certificate_does_not_imply_determinate :
    ∃ (π : Profile) (e : π.Evidence) (c : π.Claim),
      ¬ Nonempty (UnderdeterminationCertificate π e c) ∧ ¬ Determinate π e c := by
  let π : Profile :=
    { World := Unit, Evidence := Unit, Claim := Unit, Value := Bool
      inW := fun _ => True, inE := fun _ => True
      compatible := fun _ _ => False, eval := fun _ _ => true }
  have hne : ¬ NonemptyCompatible π () := by
    intro ⟨_, _, hc⟩
    exact hc
  refine ⟨π, (), (), ?_, ?_⟩
  · intro ⟨k⟩
    exact (empty_compatible_neither (c := ()) hne).1 (certificate_sound k)
  · exact (empty_compatible_neither (c := ()) hne).2

end P10
