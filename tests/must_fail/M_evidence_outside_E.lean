import P10

/-! MUST FAIL: a certificate for `m_outside_evidence` cannot be constructed (reflection by `decide` evaluates to false). -/
set_option maxRecDepth 100000
theorem bad : P10.Wire.Holds (filebytes% "vectors/negative/m_outside_evidence.json") :=
  P10.Wire.holds_of_check (by decide)
