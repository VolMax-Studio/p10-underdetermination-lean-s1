/-!
# P10.Sha256 — SHA-256 (FIPS 180-4) over `List Nat` bytes, kernel-evaluable

Purpose: let the Lean kernel itself check `sha256 bytes = digest`, so that the certificate
theorem binds the *digest that appears in the signed statement* to the *bytes that the proved
proposition is about*, without relying on an external hashing script for that link.

This implementation is NOT proved correct in Lean. Its correctness is established by
(a) kernel-checked FIPS 180-4 test vectors in `tests/Sha256Vectors.lean` and
(b) differential testing against `hashlib` in `scripts/verify.sh`.
It is therefore part of the TCB (see THREAT_MODEL.md).

Only Nat arithmetic (`+ - * / % >>>`, kernel-accelerated) and structural recursion are used;
bitwise operations are built from them (see `bitop`).
-/

namespace P10.Sha256

def M : Nat := 4294967296

/-- Bitwise operations on 32-bit words, built from `/ % + *` only. (`Nat.land/lor/xor` are
defined by well-founded recursion and depend on `propext`, which the zero-axiom policy forbids.)
Written with `Nat.rec` directly: kernel evaluation of a `Nat.rec` on a literal is far cheaper
than the `brecOn` encoding of structural recursion (measured: see BENCHMARKS in README). -/
def bxor (x y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih x y => Nat.add (Nat.mod (Nat.add (Nat.mod x 2) (Nat.mod y 2)) 2)
      (Nat.mul 2 (ih (Nat.div x 2) (Nat.div y 2)))) 32 x y

def band (x y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih x y => Nat.add (Nat.mul (Nat.mod x 2) (Nat.mod y 2))
      (Nat.mul 2 (ih (Nat.div x 2) (Nat.div y 2)))) 32 x y

def add32 (x y : Nat) : Nat := Nat.mod (Nat.add x y) 4294967296
def rotr (x n : Nat) : Nat :=
  Nat.add (Nat.div x (Nat.pow 2 n)) (Nat.mul (Nat.mod x (Nat.pow 2 n)) (Nat.pow 2 (Nat.sub 32 n)))
def notw (x : Nat) : Nat := Nat.sub 4294967295 x

def ch (e f g : Nat) : Nat := bxor (band e f) (band (notw e) g)
def maj (a b c : Nat) : Nat := bxor (bxor (band a b) (band a c)) (band b c)
def bsig0 (x : Nat) : Nat := bxor (bxor (rotr x 2) (rotr x 13)) (rotr x 22)
def bsig1 (x : Nat) : Nat := bxor (bxor (rotr x 6) (rotr x 11)) (rotr x 25)
def ssig0 (x : Nat) : Nat := bxor (bxor (rotr x 7) (rotr x 18)) (Nat.div x 8)
def ssig1 (x : Nat) : Nat := bxor (bxor (rotr x 17) (rotr x 19)) (Nat.div x 1024)

/-- `l[i]` or 0 (own definition: core `List.getD` pulls in `propext`). -/
def nth : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, i + 1 => nth as i

def take16 : Nat → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, a :: as => a :: take16 n as

def drop16 : Nat → List Nat → List Nat
  | 0, l => l
  | _ + 1, [] => []
  | n + 1, _ :: as => drop16 n as

def K : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def H0 : List Nat := [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

structure St where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  h : Nat

def round (k w : Nat) (s : St) : St :=
  let t1 := add32 (add32 (add32 (add32 s.h (bsig1 s.e)) (ch s.e s.f s.g)) k) w
  let t2 := add32 (bsig0 s.a) (maj s.a s.b s.c)
  ⟨add32 t1 t2, s.a, s.b, s.c, add32 s.d t1, s.e, s.f, s.g⟩

def rounds : List Nat → List Nat → St → St
  | k :: ks, w :: ws, s => rounds ks ws (round k w s)
  | [], _, s => s
  | _ :: _, [], s => s

/-- Extend a message schedule kept newest-first (`rev[0] = w[t-1]`). -/
def extendW : Nat → List Nat → List Nat
  | 0, rev => rev
  | n + 1, rev =>
    extendW n (add32 (add32 (ssig1 (nth rev 1)) (nth rev 6))
                 (add32 (ssig0 (nth rev 14)) (nth rev 15)) :: rev)

def schedule (block : List Nat) : List Nat := (extendW 48 block.reverse).reverse

def compress (hs : List Nat) (block : List Nat) : List Nat :=
  let s0 : St := ⟨nth hs 0, nth hs 1, nth hs 2, nth hs 3,
                  nth hs 4, nth hs 5, nth hs 6, nth hs 7⟩
  let s := rounds K (schedule block) s0
  [add32 (nth hs 0) s.a, add32 (nth hs 1) s.b, add32 (nth hs 2) s.c,
   add32 (nth hs 3) s.d, add32 (nth hs 4) s.e, add32 (nth hs 5) s.f,
   add32 (nth hs 6) s.g, add32 (nth hs 7) s.h]

def bytesToWords : List Nat → List Nat
  | a :: b :: c :: d :: rest => (a * 16777216 + b * 65536 + c * 256 + d) :: bytesToWords rest
  | [] => []
  | [_] => []
  | [_, _] => []
  | [_, _, _] => []

def lenBytes (bits : Nat) : List Nat :=
  [(bits >>> 56) % 256, (bits >>> 48) % 256, (bits >>> 40) % 256, (bits >>> 32) % 256,
   (bits >>> 24) % 256, (bits >>> 16) % 256, (bits >>> 8) % 256, bits % 256]

def zeros : Nat → List Nat
  | 0 => []
  | n + 1 => 0 :: zeros n

/-- Message padding per FIPS 180-4 §5.1.1. -/
def pad (msg : List Nat) : List Nat :=
  msg ++ (128 :: zeros ((55 + 64 - msg.length % 64) % 64)) ++ lenBytes (msg.length * 8)

def processBlocks : Nat → List Nat → List Nat → List Nat
  | 0, hs, _ => hs
  | n + 1, hs, ws =>
    match ws with
    | [] => hs
    | _ :: _ => processBlocks n (compress hs (take16 16 ws)) (drop16 16 ws)

def wordsToBytes : List Nat → List Nat
  | [] => []
  | w :: ws => (w >>> 24) % 256 :: (w >>> 16) % 256 :: (w >>> 8) % 256 :: w % 256 :: wordsToBytes ws

/-- SHA-256 of a byte list, as 32 bytes. -/
def sha256 (msg : List Nat) : List Nat :=
  let ws := bytesToWords (pad msg)
  wordsToBytes (processBlocks (ws.length / 16 + 1) H0 ws)

end P10.Sha256
