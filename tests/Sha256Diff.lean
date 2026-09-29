import P10

/-! Differential test driver: prints `<length> <hex digest>` for deterministic messages of many
lengths using the interpreter on the SAME definitions the kernel checks. Compared against
`hashlib.sha256` by `scripts/verify.sh`. Run: `lake env lean --run tests/Sha256Diff.lean`. -/

open P10.Sha256

def msg (n : Nat) : List Nat := (List.range n).map fun i => (i * 7 + 3) % 256

def hexOf (bs : List Nat) : String :=
  String.join (bs.map fun b =>
    let s := Nat.toDigits 16 b
    String.ofList (if s.length == 1 then '0' :: s else s))

def main : IO Unit := do
  for n in [0, 1, 3, 55, 56, 57, 63, 64, 65, 119, 120, 121, 127, 128, 196, 200, 1000] do
    IO.println s!"{n} {hexOf (sha256 (msg n))}"
