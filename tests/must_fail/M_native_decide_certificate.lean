import P10

/-! MUST FAIL policy check: `native_decide` extends the TCB (`Lean.ofReduceBool`) and is refused.
The axiom gate must observe `Lean.ofReduceBool` in this file's output. -/
set_option maxRecDepth 100000
theorem bad : P10.Wire.Holds (filebytes% "vectors/p1.instance.json") :=
  P10.Wire.holds_of_check (by native_decide)
#print axioms bad
