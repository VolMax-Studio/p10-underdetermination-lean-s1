import P10.Fixtures
import P10.Bytes

/-!
# P10.Wire — minimal deterministic wire format and decoder (S1 layer 2)

Wire = the JCS (RFC 8785) serialization of a flat JSON object whose keys are all
ASCII, in sorted order, and whose values are strings over `[A-Za-z0-9_.:-]`
(no escapes are ever required, no whitespace, no trailing newline):

    {"claim":C,"evidence":E,"kind":K,"profile":P,"spec":S,"w0":A,"w1":B}

The decoder accepts EXACTLY this shape (one normal form). Anything else, including
reordered keys, whitespace, escapes, unknown tokens, duplicate keys, trailing bytes,
is rejected (`none`). This is a strict subset of JCS, chosen so that decoding can be
run by the Lean kernel (`decide`) with no `native_decide`.

Bytes are `List Nat` (see `P10.Bytes`). The committed file is read with
`filebytes%`, so the statement proved in Lean is *literally about the committed bytes*.
-/

namespace P10.Wire

open P10.S1

/-- Wire-level identifiers. Changing any of these changes the decoded language. -/
def kindTok : List Nat := bytes% "p10-s1-instance-v0"
def profileTok : List Nat := bytes% "p10-s1-toy-v0"
/-- SHA-256 of the normative profile artifact this implementation targets.
Equality of this literal with the real file hash is checked by `scripts/verify.sh`
(hashing is NOT formalized in Lean here). -/
def specTok : List Nat :=
  bytes% "sha256:b92c0d689b9f16f2184ba2addb8653ed881595cc3a0117c62cadadf5c6dc6558"

structure Instance where
  claim    : Claim
  evidence : Evidence
  w0       : World
  w1       : World
  deriving DecidableEq, Repr

def isTokChar (n : Nat) : Bool :=
  (Nat.ble 48 n && Nat.ble n 57) || (Nat.ble 65 n && Nat.ble n 90) ||
  (Nat.ble 97 n && Nat.ble n 122) ||
  Nat.beq n 95 || Nat.beq n 46 || Nat.beq n 58 || Nat.beq n 45

/-- Consume the literal `pre` from the front of the input. -/
def expect : List Nat → List Nat → Option (List Nat)
  | [], s => some s
  | _ :: _, [] => none
  | a :: as, b :: bs =>
    match Nat.beq a b with
    | true => expect as bs
    | false => none

/-- Read a token up to (and consuming) the closing quote (byte 34). -/
def readTok : List Nat → Option (List Nat × List Nat)
  | [] => none
  | c :: cs =>
    match Nat.beq c 34 with
    | true => some ([], cs)
    | false =>
      match isTokChar c with
      | false => none
      | true => (readTok cs).bind fun tr => some (c :: tr.1, tr.2)

def worldOfTok (t : List Nat) : Option World :=
  if t == bytes% "w00" then some .w00
  else if t == bytes% "w01" then some .w01
  else if t == bytes% "w10" then some .w10
  else if t == bytes% "w11" then some .w11
  else if t == bytes% "wOut" then some .wOut
  else none

def worldTok : World → List Nat
  | .w00 => bytes% "w00" | .w01 => bytes% "w01" | .w10 => bytes% "w10" | .w11 => bytes% "w11" | .wOut => bytes% "wOut"

def claimOfTok (t : List Nat) : Option Claim :=
  if t == bytes% "secondBit" then some .secondBit
  else if t == bytes% "firstBit" then some .firstBit
  else none

def claimTok : Claim → List Nat
  | .secondBit => bytes% "secondBit" | .firstBit => bytes% "firstBit"

def evidenceOfTok (t : List Nat) : Option Evidence :=
  if t == bytes% "f0s_" then some (.obs false none)
  else if t == bytes% "f0s0" then some (.obs false (some false))
  else if t == bytes% "f0s1" then some (.obs false (some true))
  else if t == bytes% "f1s_" then some (.obs true none)
  else if t == bytes% "f1s0" then some (.obs true (some false))
  else if t == bytes% "f1s1" then some (.obs true (some true))
  else if t == bytes% "inconsistent" then some .inconsistent
  else if t == bytes% "outside" then some .outside
  else none

def evidenceTok : Evidence → List Nat
  | .obs false none => bytes% "f0s_" | .obs false (some false) => bytes% "f0s0"
  | .obs false (some true) => bytes% "f0s1" | .obs true none => bytes% "f1s_"
  | .obs true (some false) => bytes% "f1s0" | .obs true (some true) => bytes% "f1s1"
  | .inconsistent => bytes% "inconsistent" | .outside => bytes% "outside"

def kClaim    : List Nat := bytes% "{\"claim\":\""
def kEvidence : List Nat := bytes% ",\"evidence\":\""
def kKind     : List Nat := bytes% ",\"kind\":\""
def kProfile  : List Nat := bytes% ",\"profile\":\""
def kSpec     : List Nat := bytes% ",\"spec\":\""
def kW0       : List Nat := bytes% ",\"w0\":\""
def kW1       : List Nat := bytes% ",\"w1\":\""

/-- Read `,"key":"` then a token. -/
def field (key : List Nat) (r : List Nat) : Option (List Nat × List Nat) :=
  (expect key r).bind readTok

/-- Require the remaining input to be exactly `}`. -/
def closing (r : List Nat) : Option Unit :=
  (expect (bytes% "}") r).bind fun rest =>
    match rest with
    | [] => some ()
    | _ :: _ => none

/-- Strict decoder. `none` = reject. Written with `bind` only (no overlapping
wildcard matches, which compile through `propext`-dependent lemmas). -/
def decode (b : List Nat) : Option Instance :=
  (field kClaim b).bind fun c =>
  (field kEvidence c.2).bind fun e =>
  (field kKind e.2).bind fun k =>
  (field kProfile k.2).bind fun p =>
  (field kSpec p.2).bind fun sp =>
  (field kW0 sp.2).bind fun a =>
  (field kW1 a.2).bind fun z =>
  (closing z.2).bind fun _ =>
  match k.1 == kindTok && p.1 == profileTok && sp.1 == specTok with
  | false => none
  | true =>
    (claimOfTok c.1).bind fun cl =>
    (evidenceOfTok e.1).bind fun ev =>
    (worldOfTok a.1).bind fun w0 =>
    (worldOfTok z.1).bind fun w1 => some ⟨cl, ev, w0, w1⟩

/-- Canonical encoder (the unique normal form). Right-associated so that each field is
`key ++ (token ++ 34 :: rest)`, the exact shape `field` consumes. -/
def encode (i : Instance) : List Nat :=
  kClaim ++ (claimTok i.claim ++ 34 :: (
  kEvidence ++ (evidenceTok i.evidence ++ 34 :: (
  kKind ++ (kindTok ++ 34 :: (
  kProfile ++ (profileTok ++ 34 :: (
  kSpec ++ (specTok ++ 34 :: (
  kW0 ++ (worldTok i.w0 ++ 34 :: (
  kW1 ++ (worldTok i.w1 ++ 34 :: bytes% "}")))))))))))))

/-! ### Round trip: `decode ∘ encode = id` on every instance (profile §2.7)

Proved structurally (no `decide` over the 175 instances, no `simp`): each field is
`key ++ (token ++ 34 :: rest)` and `field` consumes exactly that shape. -/

open P10.S1 (and_split)

def allTok : List Nat → Bool
  | [] => true
  | n :: ns => isTokChar n && allTok ns

theorem allTok_mem : ∀ {t : List Nat}, allTok t = true → ∀ n, n ∈ t → isTokChar n = true
  | [], _, _, hn => nomatch hn
  | _ :: _, h, n, hn => by
    obtain ⟨ha, has⟩ := and_split h
    cases hn with
    | head => exact ha
    | tail _ hm => exact allTok_mem has n hm

theorem beq_refl' : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_refl' n

theorem expect_append : ∀ (p r : List Nat), expect p (p ++ r) = some r
  | [], _ => rfl
  | a :: as, r => by
    have h := beq_refl' a
    show (match Nat.beq a a with | true => expect as (as ++ r) | false => none) = some r
    rw [h]
    exact expect_append as r

theorem readTok_append : ∀ (t r : List Nat), allTok t = true →
    readTok (t ++ 34 :: r) = some (t, r)
  | [], _, _ => rfl
  | a :: as, r, h => by
    obtain ⟨ha, has⟩ := and_split h
    have hne : Nat.beq a 34 = false := by
      cases hb : Nat.beq a 34
      · rfl
      · have e := Nat.eq_of_beq_eq_true hb
        subst e
        exact absurd ha (by decide)
    have ih := readTok_append as r has
    show (match Nat.beq a 34 with
      | true => some ([], as ++ 34 :: r)
      | false =>
        match isTokChar a with
        | false => none
        | true => (readTok (as ++ 34 :: r)).bind fun tr => some (a :: tr.1, tr.2)) =
      some (a :: as, r)
    rw [hne, ha, ih]
    rfl

theorem field_encode (k t r : List Nat) (h : allTok t = true) :
    field k (k ++ (t ++ 34 :: r)) = some (t, r) := by
  show (expect k (k ++ (t ++ 34 :: r))).bind readTok = _
  rw [expect_append]
  exact readTok_append t r h

theorem allTok_claim (c : Claim) : allTok (claimTok c) = true := by cases c <;> rfl
theorem allTok_world (w : World) : allTok (worldTok w) = true := by cases w <;> rfl
theorem allTok_evidence (e : Evidence) : allTok (evidenceTok e) = true := by
  rcases e with ⟨f, s⟩ | _ | _
  · cases f <;> (cases s <;> (try rename_i b; cases b) <;> rfl)
  · rfl
  · rfl
theorem allTok_kind : allTok kindTok = true := rfl
theorem allTok_profile : allTok profileTok = true := rfl
theorem allTok_spec : allTok specTok = true := rfl

theorem claim_roundtrip (c : Claim) : claimOfTok (claimTok c) = some c := by cases c <;> rfl
theorem world_roundtrip (w : World) : worldOfTok (worldTok w) = some w := by cases w <;> rfl
theorem evidence_roundtrip (e : Evidence) : evidenceOfTok (evidenceTok e) = some e := by
  rcases e with ⟨f, s⟩ | _ | _
  · cases f <;> (cases s <;> (try rename_i b; cases b) <;> rfl)
  · rfl
  · rfl

theorem closing_encode : closing (bytes% "}") = some () := rfl

theorem decode_encode (i : Instance) : decode (encode i) = some i := by
  obtain ⟨c, e, w0, w1⟩ := i
  unfold decode encode
  dsimp only
  rw [field_encode _ _ _ (allTok_claim c)]; dsimp only [Option.bind]
  rw [field_encode _ _ _ (allTok_evidence e)]; dsimp only [Option.bind]
  rw [field_encode _ _ _ allTok_kind]; dsimp only [Option.bind]
  rw [field_encode _ _ _ allTok_profile]; dsimp only [Option.bind]
  rw [field_encode _ _ _ allTok_spec]; dsimp only [Option.bind]
  rw [field_encode _ _ _ (allTok_world w0)]; dsimp only [Option.bind]
  rw [field_encode _ _ _ (allTok_world w1)]; dsimp only [Option.bind]
  rw [closing_encode]; dsimp only [Option.bind]
  have hk : (kindTok == kindTok && profileTok == profileTok && specTok == specTok) = true := by
    decide
  rw [hk]
  rw [claim_roundtrip, evidence_roundtrip, world_roundtrip, world_roundtrip]

/-! ### The statement layer

`Holds b` is the proposition a wire statement asserts, defined ONLY from the bytes:
`b` must decode, must be the canonical encoding of what it decodes to (unique normal
form, profile §2.7), and the decoded instance must satisfy the profile's
`CertificateTargetV0(π, e, c, w₀, w₁)` (§2.2) for the evidence `e`, claim `c` AND the
witnesses `w₀`, `w₁` NAMED IN THE BYTES. (An earlier draft asserted only `Underdeterminedπ(e,c)`,
i.e. "some pair exists"; that was weaker than §2.2 / M34 and is fixed here.) -/

/-- Byte-list equality by `Nat.beq` (used instead of `==` so the soundness proof
needs no `LawfulBEq` machinery). -/
def listEq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    match Nat.beq a b with
    | true => listEq as bs
    | false => false

theorem listEq_sound : ∀ {a b : List Nat}, listEq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: as, b :: bs, h => by
    have h' : (match Nat.beq a b with | true => listEq as bs | false => false) = true := h
    cases hb : Nat.beq a b with
    | false => rw [hb] at h'; exact nomatch h'
    | true =>
      rw [hb] at h'
      have e := Nat.eq_of_beq_eq_true hb
      have es := listEq_sound h'
      subst e; subst es; rfl

/-- Proposition asserted for a decoded instance `o` of the bytes `b`. -/
def holdsOpt (b : List Nat) : Option Instance → Prop
  | some i => encode i = b ∧ CertificateTargetV0 profile i.evidence i.claim i.w0 i.w1
  | none => False

/-- Checker on a decoded instance: canonical form and the `CertificateTargetV0`
decision procedure. -/
def checkOpt (b : List Nat) : Option Instance → Bool
  | some i => listEq (encode i) b && checkTarget i.evidence i.claim i.w0 i.w1
  | none => false

/-- **The proposition a wire statement asserts.** -/
def Holds (b : List Nat) : Prop := holdsOpt b (decode b)

/-- The reflective checker. -/
def check (b : List Nat) : Bool := checkOpt b (decode b)

theorem holdsOpt_of_checkOpt (b : List Nat) :
    ∀ (o : Option Instance), checkOpt b o = true → holdsOpt b o
  | none, h => nomatch h
  | some _, h =>
    ⟨listEq_sound (and_split h).1, checkTarget_sound (and_split h).2⟩

/-- Soundness of the checker: `check b = true → Holds b`. -/
theorem holds_of_check {b : List Nat} (h : check b = true) : Holds b :=
  holdsOpt_of_checkOpt b (decode b) h

/-- `Holds b` is exactly (canonical form ∧ `CertificateTargetV0` for the *decoded instance,
including its named witnesses*); no other proposition is ever proved by a vector certificate. -/
theorem holds_iff {b : List Nat} {i : Instance} (h : decode b = some i) :
    Holds b ↔ (encode i = b ∧ CertificateTargetV0 profile i.evidence i.claim i.w0 i.w1) :=
  Eq.subst (motive := fun o => holdsOpt b o ↔
      (encode i = b ∧ CertificateTargetV0 profile i.evidence i.claim i.w0 i.w1))
    h.symm Iff.rfl

/-- What a `Holds` proof yields for the decoded instance: `Underdeterminedπ(e,c)`. -/
theorem holds_underdetermined {b : List Nat} {i : Instance} (h : decode b = some i)
    (hh : Holds b) : Underdetermined profile i.evidence i.claim :=
  ((holds_iff h).1 hh).2.underdetermined

/-- Proposition-level rejection: if the decoded instance's NAMED witnesses do not form a
`CertificateTargetV0` then `Holds b` is false — whatever other pair might exist for the
same evidence and claim (kill-test for the "some other good pair" weakening, M34). -/
theorem not_holds_of_not_target {b : List Nat} {i : Instance} (h : decode b = some i)
    (hn : ¬ CertificateTargetV0 profile i.evidence i.claim i.w0 i.w1) : ¬ Holds b :=
  fun hh => hn ((holds_iff h).1 hh).2

/-- Undecodable bytes never satisfy `Holds`. -/
theorem not_holds_of_decode_none {b : List Nat} (h : decode b = none) : ¬ Holds b :=
  Eq.subst (motive := fun o => ¬ holdsOpt b o) h.symm (fun x => x)

/-- If the checker rejects, no `Holds` proof can come from `holds_of_check` (the checker is
complete on this finite profile only for the decidable target; see `check_false_iff`). -/
theorem check_eq_false_of_decode_none {b : List Nat} (h : decode b = none) :
    check b = false :=
  Eq.subst (motive := fun o => checkOpt b o = false) h.symm rfl

end P10.Wire
