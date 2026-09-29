# Release checklist (S1 → a future human-decided release)

Nothing in this repo is ratified. This list is for a maintainer; no step here was performed by the drafting agent.

- [ ] Independent human review of `profile/IMPLEMENTATION_BINDING.md` against the profile text (the only route to the words
      "independently validated").
- [ ] Re-run canonical `./scripts/verify.sh` on a clean machine; compare `SHA256SUMS`, manifest and statement digests.
- [ ] Decide the Lean version policy (profile kernel uses 4.34.0; S1 pins 4.33.0) and re-pin, then `scripts/regen.sh`.
- [ ] Decide whether to keep the S1 wire subset or move to full JCS worlds (S2).
- [ ] Replace CI action tags with commit SHAs.
- [ ] Publish the pinned manifest digest out-of-band (README, profile InstanceCommitment) — never only in-tree.
- [ ] Only then: human-signed tag/ratification (not done here; the drafting agent never used a human signing key).
