import P10

/-!
Decoder partition (M8 and profile-identity mutations), kernel-checked.
Non-canonical / foreign encodings are rejected by the decoder (`none`); semantically bad but
well-formed instances decode (`some`) and are then rejected by the checker.
`scripts/mutation_suite.py` asserts that the independent Python decoder induces the same
partition on the same files.
-/

open P10 P10.S1 P10.Wire

def f (x : List Nat) : Bool := (decode x).isNone
def g (x : List Nat) : Bool := (decode x).isSome

def m8ws  : List Nat := filebytes% "vectors/negative/m8_whitespace.json"
def m8ko  : List Nat := filebytes% "vectors/negative/m8_key_order.json"
def m8nl  : List Nat := filebytes% "vectors/negative/m8_trailing_newline.json"
def m8ut  : List Nat := filebytes% "vectors/negative/m8_unknown_token.json"
def m8esc : List Nat := filebytes% "vectors/negative/m8_escape.json"
def m32   : List Nat := filebytes% "vectors/negative/m32_wrong_spec.json"
def mkind : List Nat := filebytes% "vectors/negative/m_wrong_kind.json"
def mprof : List Nat := filebytes% "vectors/negative/m_wrong_profile.json"

theorem m8_whitespace_rejected : f m8ws = true := by decide
theorem m8_key_order_rejected : f m8ko = true := by decide
theorem m8_trailing_newline_rejected : f m8nl = true := by decide
theorem m8_unknown_token_rejected : f m8ut = true := by decide
theorem m8_escape_rejected : f m8esc = true := by decide
theorem m32_wrong_spec_rejected : f m32 = true := by decide
theorem wrong_kind_rejected : f mkind = true := by decide
theorem wrong_profile_rejected : f mprof = true := by decide

def n1 : List Nat := filebytes% "vectors/negative/n1_determined.json"
def n2 : List Nat := filebytes% "vectors/negative/n2_incompatible.json"
def n3 : List Nat := filebytes% "vectors/negative/n3_same_value.json"
def n4 : List Nat := filebytes% "vectors/negative/n4_empty_compatible.json"
def m3 : List Nat := filebytes% "vectors/negative/m3_outside_world.json"
def mE : List Nat := filebytes% "vectors/negative/m_outside_evidence.json"

theorem semantic_negatives_decode :
    g n1 = true ∧ g n2 = true ∧ g n3 = true ∧ g n4 = true ∧ g m3 = true ∧ g mE = true := by
  decide

theorem semantic_negatives_rejected_by_checker :
    check n1 = false ∧ check n2 = false ∧ check n3 = false ∧ check n4 = false ∧
    check m3 = false ∧ check mE = false := by
  decide

/-- `encode ∘ decode` is the identity on every accepted negative vector as well
(they are canonical; they fail for semantic reasons only). -/
theorem semantic_negatives_canonical :
    (match decode n2 with | some i => listEq (encode i) n2 | none => false) = true := by
  decide

#print axioms m8_whitespace_rejected
#print axioms m8_key_order_rejected
#print axioms m8_trailing_newline_rejected
#print axioms m8_unknown_token_rejected
#print axioms m8_escape_rejected
#print axioms m32_wrong_spec_rejected
#print axioms wrong_kind_rejected
#print axioms wrong_profile_rejected
#print axioms semantic_negatives_decode
#print axioms semantic_negatives_rejected_by_checker
