/-!
# P10.Core — formal core of the P10 Underdetermination Profile

Normative source: `P10_Underdetermination_Profile_v0.1.1.md`, §2.1 (definitions)
and §2.2 (`CertificateTargetV0`). Exact section mapping: `profile/IMPLEMENTATION_BINDING.md`.

This file is a formal realization of the ratified profile. It is NOT a new
normative definition; where this file and the profile disagree, the profile wins
and the disagreement is a bug in this file.

Representation choice (recorded in IMPLEMENTATION_BINDING.md): the profile's sets
`Wπ` and `Eπ` are modelled as *membership predicates* `inW`, `inE` over ambient
types, so that "w ∈ Wπ" and "e ∈ Eπ" appear literally in every definition.
-/

namespace P10

/-- The executable-semantics surface of a profile π (profile §2.1, §2.2).
`inW`/`inE` are membership in `Wπ`/`Eπ`; `compatible`/`eval` are
`Compatibleπ`/`Evalπ`. -/
structure Profile where
  World    : Type
  Evidence : Type
  Claim    : Type
  Value    : Type
  inW        : World → Prop
  inE        : Evidence → Prop
  compatible : Evidence → World → Prop
  eval       : Claim → World → Value

/-- `Compatibleπ : Evidence → World → Prop`. -/
def Compatible (π : Profile) (e : π.Evidence) (w : π.World) : Prop :=
  π.compatible e w

/-- `Evalπ : Claim → World → Value`. -/
def Eval (π : Profile) (c : π.Claim) (w : π.World) : π.Value :=
  π.eval c w

/-- Profile §2.1: `NonemptyCompatibleπ(e) := ∃ w ∈ Wπ, Compatibleπ(e, w)`. -/
def NonemptyCompatible (π : Profile) (e : π.Evidence) : Prop :=
  ∃ w, π.inW w ∧ Compatible π e w

/-- Profile §2.1:
`Determinateπ(e,c) := NonemptyCompatibleπ(e) ∧ ∀ w₀ w₁ ∈ Wπ,
   Compatibleπ(e,w₀) ∧ Compatibleπ(e,w₁) → Evalπ(c,w₀) = Evalπ(c,w₁)`. -/
def Determinate (π : Profile) (e : π.Evidence) (c : π.Claim) : Prop :=
  NonemptyCompatible π e ∧
  ∀ w₀ w₁, π.inW w₀ → π.inW w₁ →
    Compatible π e w₀ ∧ Compatible π e w₁ →
    Eval π c w₀ = Eval π c w₁

/-- Profile §2.1:
`Underdeterminedπ(e,c) := ∃ w₀ w₁ ∈ Wπ, Compatibleπ(e,w₀) ∧ Compatibleπ(e,w₁) ∧
   Evalπ(c,w₀) ≠ Evalπ(c,w₁)`. -/
def Underdetermined (π : Profile) (e : π.Evidence) (c : π.Claim) : Prop :=
  ∃ w₀ w₁, π.inW w₀ ∧ π.inW w₁ ∧
    Compatible π e w₀ ∧ Compatible π e w₁ ∧
    Eval π c w₀ ≠ Eval π c w₁

/-- Profile §2.1: `ProfileAdmissible(π,c) := ∃ eD ∈ Eπ, Determinateπ(eD,c)`. -/
def ProfileAdmissible (π : Profile) (c : π.Claim) : Prop :=
  ∃ eD, π.inE eD ∧ Determinate π eD c

/-- Profile §2.1:
`FormallyUnderdeterminationCapable(π,c) := ∃ eU eD ∈ Eπ,
   Underdeterminedπ(eU,c) ∧ Determinateπ(eD,c)`. -/
def FormallyUnderdeterminationCapable (π : Profile) (c : π.Claim) : Prop :=
  ∃ eU eD, π.inE eU ∧ π.inE eD ∧
    Underdetermined π eU c ∧ Determinate π eD c

/-- Profile §2.2:
`CertificateTargetV0(π,e,c,w₀,w₁) := e ∈ Eπ ∧ w₀ ∈ Wπ ∧ w₁ ∈ Wπ ∧
   Compatibleπ(e,w₀) ∧ Compatibleπ(e,w₁) ∧ Evalπ(c,w₀) ≠ Evalπ(c,w₁)`.
The conjunct order is the profile's order. The checker constructs this
proposition from committed inputs; a certificate never supplies it. -/
def CertificateTargetV0 (π : Profile) (e : π.Evidence) (c : π.Claim)
    (w₀ w₁ : π.World) : Prop :=
  π.inE e ∧ π.inW w₀ ∧ π.inW w₁ ∧
  Compatible π e w₀ ∧ Compatible π e w₁ ∧
  Eval π c w₀ ≠ Eval π c w₁

/-! ### Immediate consequences stated in the profile's notes (§2.1) -/

/-- Profile §2.1 note: `FormallyUnderdeterminationCapable → ProfileAdmissible`. -/
theorem FormallyUnderdeterminationCapable.profileAdmissible {π : Profile}
    {c : π.Claim} (h : FormallyUnderdeterminationCapable π c) :
    ProfileAdmissible π c := by
  obtain ⟨_, eD, _, hE, _, hD⟩ := h
  exact ⟨eD, hE, hD⟩

/-- Profile §2.1 note: differing claim values entail semantically distinct worlds. -/
theorem worlds_distinct_of_values_differ {π : Profile} {c : π.Claim}
    {w₀ w₁ : π.World} (h : Eval π c w₀ ≠ Eval π c w₁) : w₀ ≠ w₁ := by
  intro hEq
  apply h
  rw [hEq]

/-- `CertificateTargetV0` implies `Underdeterminedπ` (drop the two membership facts about `e`, forget nothing
else). The converse is false in general: `Underdeterminedπ` does not name the witnesses. -/
theorem CertificateTargetV0.underdetermined {π : Profile} {e : π.Evidence} {c : π.Claim}
    {w₀ w₁ : π.World} (h : CertificateTargetV0 π e c w₀ w₁) : Underdetermined π e c :=
  ⟨w₀, w₁, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end P10
