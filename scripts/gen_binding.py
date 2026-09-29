#!/usr/bin/env python3
"""Fill `{{sha:PATH}}` placeholders in profile/IMPLEMENTATION_BINDING.md.in with real file digests."""
import hashlib, re, sys
src = open("profile/IMPLEMENTATION_BINDING.md.in", encoding="utf-8").read()
def sub(m):
    with open(m.group(1), "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()
out = re.sub(r"\{\{sha:([^}]+)\}\}", sub, src)
assert "{{" not in out
open("profile/IMPLEMENTATION_BINDING.md", "w", encoding="utf-8").write(out)
