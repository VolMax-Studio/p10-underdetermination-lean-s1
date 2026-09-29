import Lean

/-!
Trusted helper (hashed in the verifier manifest). Reads a compiled module's `.olean` WITHOUT importing
it — so none of its syntax extensions, macros or attributes are activated — and checks that a named
constant exists, is a theorem, and that its type is EXACTLY `Expr.const <expected> []`.

Usage: lean --run scripts/CheckModule.lean <file.olean> <constant> <expected-type-constant>
Exit: 0 ok, 1 mismatch/absent, 2 usage.
-/
open Lean

def main (args : List String) : IO UInt32 := do
  match args with
  | [olean, cname, expected] =>
    let (md, _) ← readModuleData olean
    let n := cname.toName
    let some idx := md.constNames.findIdx? (· == n)
      | IO.eprintln s!"constant {cname} not found in {olean}"; return 1
    let ci := md.constants[idx]!
    unless ci.isTheorem do
      IO.eprintln s!"{cname} is not a theorem"; return 1
    unless ci.levelParams.isEmpty do
      IO.eprintln s!"{cname} has universe parameters"; return 1
    if ci.type == Expr.const expected.toName [] then
      IO.println s!"type-ok {cname} : {expected}"
      return 0
    else
      IO.eprintln s!"type of {cname} is not {expected}: {ci.type}"
      return 1
  | _ =>
    IO.eprintln "usage: CheckModule <olean> <constant> <expected type constant>"
    return 2
