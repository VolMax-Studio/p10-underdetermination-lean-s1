#!/usr/bin/env python3
"""Forbidden-construct scan for Lean sources (part of the TCB gate; see profile/AXIOM_POLICY.md).

Comments (`-- ...` and nested `/- ... -/`) are stripped first, so prose may mention the forbidden
words; string literals are kept (a forbidden word inside a string is still flagged, conservatively).
Exit codes: 0 clean, 1 forbidden construct found, 2 usage/IO error (never treated as clean).
Usage: lint_lean.py FILE_OR_DIR...   (tests/must_fail is scanned only when named explicitly)
"""
import os
import re
import sys

FORBIDDEN = [
    r"\bsorry\b", r"\badmit\b", r"\bsorryAx\b", r"\bnative_decide\b", r"\bLean\.ofReduceBool\b",
    r"\bofReduceBool\b", r"\baxiom\b", r"\bunsafe\b", r"\bimplemented_by\b", r"\bextern\b",
    r"\bopaque\b", r"\bpartial\b", r"\bcsimp\b", r"\bdecide\s*\+\s*kernel\b", r"\bdecide!\b",
    r"\bset_option\s+debug\.", r"\bunsafeCast\b", r"\bunsafeBaseIO\b", r"\bunsafeIO\b",
    r"\bReflectionCheck\b", r"\bskip_check\b", r"\bsimprocs\b",
]
FORBIDDEN_RE = [re.compile(p) for p in FORBIDDEN]


def strip_comments(s: str) -> str:
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if s.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and s.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if s[i] == "\n" else " ")
            i += 1
        elif s.startswith("--", i):
            while i < n and s[i] != "\n":
                i += 1
        else:
            out.append(s[i])
            i += 1
    if depth:
        raise ValueError("unterminated block comment")
    return "".join(out)


def scan(path: str) -> list[str]:
    with open(path, encoding="utf-8") as f:
        code = strip_comments(f.read())
    hits = []
    for ln, line in enumerate(code.splitlines(), 1):
        for rx in FORBIDDEN_RE:
            if rx.search(line):
                hits.append(f"{path}:{ln}: forbidden construct {rx.pattern!r}: {line.strip()}")
    return hits


def gather(arg: str) -> list[str]:
    if os.path.isfile(arg):
        return [arg]
    files = []
    for dp, dns, fns in os.walk(arg):
        dns[:] = [d for d in dns if d not in (".lake", ".git", ".venv", ".toolchain", "must_fail")]
        files += [os.path.join(dp, f) for f in fns if f.endswith(".lean")]
    return sorted(files)


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    hits, n = [], 0
    try:
        for a in sys.argv[1:]:
            if not os.path.exists(a):
                print(f"error: no such path {a}", file=sys.stderr)
                return 2
            for f in gather(a):
                n += 1
                hits += scan(f)
    except (OSError, ValueError, UnicodeDecodeError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    if n == 0:
        print("error: no Lean files scanned", file=sys.stderr)
        return 2
    for h in hits:
        print(h)
    print(f"lint_lean: scanned {n} files, {len(hits)} forbidden constructs")
    return 1 if hits else 0


if __name__ == "__main__":
    sys.exit(main())
