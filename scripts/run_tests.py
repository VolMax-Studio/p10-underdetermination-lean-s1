#!/usr/bin/env python3
"""Run the Lean test suite. Fail-closed: any unexpected outcome is a failure.

positive   tests/*.lean           must compile (exit 0) and print ONLY axiom-free `#print axioms`
                                  lines (no warnings, no errors, no other output).
must_fail  tests/must_fail/*.lean must be REJECTED by Lean for the intended reason:
             - files whose name starts with N/M and are not `*_certificate`: exit != 0 and the output
               contains `Type mismatch` or `proved that the proposition` (decide evaluated to false);
             - `*_certificate` files (sorry / native_decide): must elaborate but their `#print axioms`
               output MUST list an axiom dependency, i.e. the axiom gate would reject them.
sha256     tests/Sha256Diff.lean  interpreter output compared with hashlib for many lengths.
Run from the repository root with `lake`/`lean` on PATH.
"""
import glob
import hashlib
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)


def lean(*args, timeout=1800):
    p = subprocess.run(["lake", "env", "lean", *args], capture_output=True, timeout=timeout)
    return p.returncode, (p.stdout + p.stderr).decode("utf-8", "replace")


fails, passed = [], 0


def check(name, cond, detail=""):
    global passed
    if cond:
        passed += 1
        print(f"  ok   {name}")
    else:
        fails.append(name)
        print(f"  FAIL {name}\n{detail[-1500:]}")


print("== positive tests")
for f in sorted(glob.glob("tests/*.lean")):
    if f.endswith("Sha256Diff.lean"):
        continue
    rc, out = lean(f)
    n_audit = sum(1 for l in open(f) if l.startswith("#print axioms "))
    lines = [l for l in out.splitlines() if l.strip()]
    ok_lines = [l for l in lines if l.endswith("does not depend on any axioms")]
    check(f, rc == 0 and n_audit >= 1 and len(ok_lines) == n_audit == len(lines), out)

print("== must-fail tests")
for f in sorted(glob.glob("tests/must_fail/*.lean")):
    rc, out = lean(f)
    if f.endswith("_certificate.lean"):
        dep = re.search(r"depends on axioms: \[", out) is not None
        check(f + " (axiom gate must reject)", rc == 0 and dep, out)
    else:
        why = ("Type mismatch" in out) or ("proved that the proposition" in out)
        check(f, rc != 0 and why, out)

print("== sha256 differential (interpreter vs hashlib)")
p = subprocess.run(["lake", "env", "lean", "--run", "tests/Sha256Diff.lean"], capture_output=True, timeout=1800)
out = p.stdout.decode()
rows = [l.split() for l in out.splitlines() if l.strip()]
good = p.returncode == 0 and len(rows) >= 10
for n, h in rows:
    m = bytes((i * 7 + 3) % 256 for i in range(int(n)))
    good = good and hashlib.sha256(m).hexdigest() == h
check(f"tests/Sha256Diff.lean ({len(rows)} lengths)", good, out + p.stderr.decode())

print(f"\nrun_tests: {passed} passed, {len(fails)} failed")
sys.exit(1 if fails else 0)
