#!/usr/bin/env python3
"""Source-policy gate for Lean sources (part of the TCB gate; see profile/AXIOM_POLICY.md).

This is DEFENSE IN DEPTH. The security boundary is kernel replay (`leanchecker`, run by
`scripts/p10tool.py`) plus the precompiled checker-owned target; a denylist can never be complete.

Rules (applied to comment-stripped text, over the WHOLE file, so line splitting cannot evade them):
 1. Proof-escape constructs are forbidden everywhere (sorry, admit, native_decide, axiom, unsafe,
    implemented_by, extern, opaque, partial, decide +kernel, kernel/debug options, ...).
 2. Metaprogramming is forbidden everywhere EXCEPT the allowlisted file(s) META_ALLOWLIST
    (currently only `P10/Bytes.lean`): macro, macro_rules, syntax, notation, elab, elab_rules,
    run_cmd, run_elab, run_meta, initialize, unif_hint, `import Lean`, `open Lean`, addDecl,
    setBool, withOptions, ...
 3. `set_option` may only set `maxRecDepth`.
 4. Certificate modules (any file under a `Certs` directory) are STRICT: only these top-level
    commands are allowed, each starting in column 0: import (of P10.* modules only), set_option
    maxRecDepth, namespace, end, open, def, theorem. No attributes, instances, sections, variables,
    local/scoped/private/protected declarations.

Comments (`-- ...` and nested `/- ... -/`) are stripped first, so prose may mention forbidden words;
string literals are kept (a forbidden word inside a string is flagged, conservatively).
Exit codes: 0 clean, 1 policy violation, 2 usage/IO error (never treated as clean).
Usage: lint_lean.py FILE_OR_DIR...   (tests/must_fail is skipped when walking a directory)
"""
import os
import re
import sys

META_ALLOWLIST = ("P10/Bytes.lean",)

ESCAPE = [
    r"\bsorry\b", r"\badmit\b", r"\bsorryAx\b", r"\bnative_decide\b", r"\bLean\.ofReduceBool\b",
    r"\bofReduceBool\b", r"\baxiom\b", r"\bunsafe\b", r"\bimplemented_by\b", r"\bextern\b",
    r"\bopaque\b", r"\bpartial\b", r"\bcsimp\b", r"\bdecide\s*\+\s*kernel\b", r"\bdecide!\b",
    r"\bdebug\.[A-Za-z]", r"\bskipKernelTC\b", r"\bunsafeCast\b", r"\bunsafeBaseIO\b", r"\bunsafeIO\b",
    r"\bskip_check\b", r"\bsimprocs\b", r"\bReflectionCheck\b",
]
META = [
    r"\bmacro_rules\b", r"\bmacro\b", r"\bsyntax\b", r"\bnotation\b", r"\binfixl?\b", r"\binfixr\b",
    r"\bprefix\b", r"\bpostfix\b", r"\belab_rules\b", r"\belab\b", r"\brun_cmd\b", r"\brun_elab\b",
    r"\brun_meta\b", r"\binitialize\b", r"\bbuiltin_initialize\b", r"\bunif_hint\b",
    r"\bimport\s+Lean\b", r"\bopen\s+Lean\b", r"\baddDecl\b", r"\baddAndCompile\b", r"\bsetBool\b",
    r"\bsetOptionFromString\b", r"\bwithOptions\b", r"\bmodifyEnv\b", r"\bsetEnv\b",
    r"\bregisterBuiltin\w*", r"\bregister_\w+", r"\bdeclare_syntax_cat\b", r"\bmkSimpAttr\b",
    r"\battribute\s*\[", r"\bopen\s+\w[\w.]*\s+in\b(?=\s*\n?\s*(?:run_cmd|elab|macro))",
]
ESCAPE_RE = [re.compile(p) for p in ESCAPE]
META_RE = [re.compile(p) for p in META]

SET_OPTION_RE = re.compile(r"\bset_option\s+([A-Za-z_][\w.]*)")
CERT_TOP_OK = re.compile(r"^(import|set_option|namespace|end|open|def|theorem)\b")
CERT_IMPORT_OK = re.compile(r"^import\s+P10(\.[A-Za-z0-9_]+)+\s*$")


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


def lineno(code: str, pos: int) -> int:
    return code.count("\n", 0, pos) + 1


def scan(path: str) -> list[str]:
    with open(path, encoding="utf-8") as f:
        code = strip_comments(f.read())
    norm = os.path.normpath(path).replace(os.sep, "/")
    meta_ok = any(norm == a or norm.endswith("/" + a) for a in META_ALLOWLIST)
    is_cert = "/Certs/" in "/" + norm
    hits = []
    for rx in ESCAPE_RE:
        for m in rx.finditer(code):
            hits.append(f"{path}:{lineno(code, m.start())}: forbidden construct {rx.pattern!r}")
    if not meta_ok:
        for rx in META_RE:
            for m in rx.finditer(code):
                hits.append(f"{path}:{lineno(code, m.start())}: metaprogramming/kernel-adjacent construct "
                            f"{m.group(0).strip()!r} outside the allowlist {META_ALLOWLIST}")
    for m in SET_OPTION_RE.finditer(code):
        if m.group(1) != "maxRecDepth":
            hits.append(f"{path}:{lineno(code, m.start())}: set_option {m.group(1)} is not allowed "
                        "(only maxRecDepth)")
    if is_cert:
        for ln, line in enumerate(code.splitlines(), 1):
            if not line.strip():
                continue
            if line[0] in " \t":
                continue  # continuation of a command
            if not CERT_TOP_OK.match(line):
                hits.append(f"{path}:{ln}: certificate modules may only contain "
                            f"import/set_option/namespace/end/open/def/theorem at top level: {line.strip()!r}")
            elif line.startswith("import") and not CERT_IMPORT_OK.match(line):
                hits.append(f"{path}:{ln}: certificate modules may only import P10.* modules: {line.strip()!r}")
            elif line.startswith("open") and re.search(r"\bLean\b", line):
                hits.append(f"{path}:{ln}: certificate modules may not open Lean namespaces")
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
    print(f"lint_lean: scanned {n} files, {len(hits)} policy violations")
    return 1 if hits else 0


if __name__ == "__main__":
    sys.exit(main())
