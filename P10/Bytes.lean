import Lean

/-!
# P10.Bytes — elaboration-time byte literals

Lean 4.33 strings are UTF-8 byte arrays whose `toList` goes through well-founded
decoding; that path is slow in the kernel and pulls in `propext`/`Classical.choice`.
To keep the kernel-checked statement axiom-free, wire bytes are `List Nat`.

Two term elaborators (meta code, NOT kernel-checked; part of the elaboration-time TCB,
see THREAT_MODEL.md) turn text into `List Nat` literals:

* `bytes% "abc"`         — the UTF-8 bytes of a string literal.
* `filebytes% "path"`    — the raw bytes of a file, path relative to the working
                           directory (the repository root; canonical invocation is
                           from the root).

Both expand to fully explicit `[n₀, n₁, …] : List Nat` terms, so the statement the
kernel checks contains the literal bytes; `scripts/verify.sh` independently dumps the
elaborated statement and compares its bytes with the committed file.
-/

open Lean Elab Term

namespace P10.Bytes

def natListLit (bs : List Nat) : Expr :=
  let nat := Lean.mkConst ``Nat
  bs.foldr (fun n acc => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) nat (mkNatLit n) acc)
    (mkApp (Lean.mkConst ``List.nil [Level.zero]) nat)

end P10.Bytes

elab "bytes%" s:str : term =>
  return P10.Bytes.natListLit (s.getString.toUTF8.toList.map (·.toNat))

elab "filebytes%" p:str : term => do
  let bs ← IO.FS.readBinFile (System.FilePath.mk p.getString)
  return P10.Bytes.natListLit (bs.toList.map (·.toNat))

/-- `hex% "0a1b…"` — a byte list from a hexadecimal string literal (even length, lowercase or
uppercase), expanded at elaboration time. -/
elab "hex%" s:str : term => do
  let str := s.getString
  let cs := str.toList
  if cs.length % 2 != 0 then throwError "hex%: odd length"
  let digit (c : Char) : Nat :=
    if c.toNat >= 48 && c.toNat <= 57 then c.toNat - 48
    else if c.toNat >= 97 && c.toNat <= 102 then c.toNat - 87
    else if c.toNat >= 65 && c.toNat <= 70 then c.toNat - 55
    else 16
  let rec go : List Char → List Nat
    | a :: b :: rest => (digit a * 16 + digit b) :: go rest
    | _ => []
  let bs := go cs
  if cs.any (fun c => digit c == 16) then throwError "hex%: non-hex character"
  return P10.Bytes.natListLit bs
