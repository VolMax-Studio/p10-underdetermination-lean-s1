#!/usr/bin/env python3
"""Fail-closed Python environment check: EVERY package pinned in the lock file must be installed at
exactly the pinned version. No exemptions (the former `cryptography` exemption was removed).

Exit 0: all pins match. Exit 1: any mismatch, missing package, malformed/unpinned lock line, or empty lock.
Usage: check_env.py [LOCKFILE]   (default: requirements.lock next to the repository root)"""
import os
import re
import sys
from importlib import metadata

HERE = os.path.dirname(os.path.abspath(__file__))


def norm(n: str) -> str:
    return re.sub(r"[-_.]+", "-", n).lower()


def main() -> int:
    lock = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(HERE), "requirements.lock")
    try:
        lines = [l.strip() for l in open(lock, encoding="utf-8") if l.strip() and not l.lstrip().startswith("#")]
    except OSError as e:
        print(f"check_env: cannot read {lock}: {e}", file=sys.stderr)
        return 1
    if not lines:
        print("check_env: lock file has no pins", file=sys.stderr)
        return 1
    bad = []
    for l in lines:
        m = re.fullmatch(r"([A-Za-z0-9][A-Za-z0-9._-]*)==([A-Za-z0-9][A-Za-z0-9._+!-]*)", l)
        if not m:
            bad.append(f"malformed/unpinned lock line: {l!r}")
            continue
        name, want = m.groups()
        try:
            have = metadata.version(norm(name))
        except metadata.PackageNotFoundError:
            bad.append(f"{name}: not installed (pinned {want})")
            continue
        if have != want:
            bad.append(f"{name}: installed {have}, pinned {want}")
        else:
            print(f"  {name} {have} (pinned)")
    for b in bad:
        print(f"check_env: MISMATCH {b}", file=sys.stderr)
    if bad:
        return 1
    print(f"  check_env: {len(lines)} pinned packages match exactly")
    return 0


if __name__ == "__main__":
    sys.exit(main())
