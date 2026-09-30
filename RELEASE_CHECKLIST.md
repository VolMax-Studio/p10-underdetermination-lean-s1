# Release record — S1 v0.1.0-s1-ratified

The frozen S1 release is the human-signed annotated tag `v0.1.0-s1-ratified`, tag object
`7c3df437de454466b932a5d0dc889b3287c64e05`, peeled to commit
`e4db3747eaeeb1a07227bb9029f9a9c3b566cdb1`.

Later documentation-only commits on `main` are **not** part of that frozen snapshot unless separately ratified.

- [ ] Independent external human/organizational review of `profile/IMPLEMENTATION_BINDING.md` against the profile text
      (required before using the words "independently validated").
- [x] Canonical verification completed in GitHub Actions on the frozen implementation commit; post-merge main CI PASS,
      including `SHA256SUMS`/manifest/statement checks, axiom audit, tests, kernel replay and mutation suite.
- [x] Lean version policy decided for S1: the exact digest-pinned conda-forge Lean 4.33.0 build is authoritative for
      the frozen artifact. Equivalence to the upstream v4.33.0 tag is not claimed.
- [x] S1 keeps its strict wire-codec subset; full/general JCS handling is deferred beyond S1.
- [x] CI actions pinned to commit SHAs (SHAs taken from CI run #2 log; re-check against action repositories when convenient).
- [x] Human ratification completed with signed tag `v0.1.0-s1-ratified`.
- [x] The signed ratification tag publishes the authorized verifier-manifest digest
      `06bf9129bf480c79ed5281ec2e944ac5613d1c340552ce5a415f5bf4c8965907` external to the committed tree;
      consumers must verify the tag signature/public-key trust before using it as the S1 pin.
- [ ] Protocol-level/independent-channel anchoring via P10 `InstanceCommitment`, transparency registration or SCITT
      remains S2/S3 work and is not demonstrated by S1.
