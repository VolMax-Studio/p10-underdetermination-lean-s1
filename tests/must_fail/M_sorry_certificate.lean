import P10

/-! MUST FAIL policy check: `sorry` certificates are refused (the axiom line lists `sorryAx`).
Elaboration itself succeeds with a warning, so this file is checked by the *axiom* gate:
see scripts/verify.sh (it requires the output to contain `sorryAx`, i.e. to be rejectable). -/
set_option maxRecDepth 100000
theorem bad : P10.Wire.Holds (filebytes% "vectors/negative/n1_determined.json") := sorry
#print axioms bad
