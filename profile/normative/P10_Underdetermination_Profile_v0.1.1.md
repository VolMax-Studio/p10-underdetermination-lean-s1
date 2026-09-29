# P10 Underdetermination Profile v0.1.1

**Document status:** versioned specification artifact; independent-review and release status are recorded separately and bound to this artifact by SHA-256.
**Version:** 0.1.1
**Publication-candidate date:** 2026‑09‑27
**Hard deadline (outside this document):** IETF 127 I‑D cutoff 2026‑11‑02 23:59 UTC (confirmed on the IETF Datatracker).

---

The key words **MUST**, **MUST NOT**, **REQUIRED**, **SHALL**, **SHALL NOT**, **SHOULD**, **SHOULD NOT**, **RECOMMENDED**, **NOT RECOMMENDED**, **MAY**, and **OPTIONAL** in this document are to be interpreted as described in BCP 14 when, and only when, they appear in all capitals, as specified by RFC 2119 and RFC 8174.

## 1. Claim of record

> The proposed P10 Underdetermination Profile defines a third-party-verifiable binding for `NotDemonstrated(reason=underdetermined)`. Issuance is permitted only when:
> (1) the world class, admissible-evidence-bundle space and item-admission rules, frozen bundle constructor, compatibility relation, claim interpretation, evidence scope and coverage rules, canonicalization, world codec, committed log identity, leaf encoding, lifecycle/admitter authorization, and verifier were committed in a profile and an identified `InstanceCommitment` before the first evidence admission for that instance;
> (2) within the committed transparency log `L`, exactly one profile and claim are bound to the `(issuer_id, request_id)` subject, and an `EvidenceClosure` plus checkpoint-bounded `CoverageProof` binds every valid, registered, in-scope admission made by a frozen authorized admitter through `S_R`;
> (3) the receipt carries two semantically distinct worlds from that frozen world class, represented in the profile's frozen canonical serialization;
> (4) the frozen verifier establishes that both witnesses are compatible with that same closed evidence set and assign different values to the same frozen claim; and
> (5) the instance commitment, profile, claim, closed evidence set, witnesses, proof, verifier and mandatory limitations are SHA-256-bound in a SCITT Transparent Statement whose payload is an in-toto Statement v1 containing the P10 predicate, with complete VDS-prefix replay and registration/coverage verification satisfying §§2.4–2.6.
> The result establishes underdetermination only relative to the declared profile and does not identify the actual world or establish either claim value as true.

**Nature of the contribution:** profile-and-binding contribution. It is not a new mathematical theorem.

---

## 2. Formal core

### 2.1 Definitions

```text
NonemptyCompatibleπ(e) :=
  ∃ w ∈ Wπ, Compatibleπ(e, w)

Determinateπ(e, c) :=
  NonemptyCompatibleπ(e) ∧
  ∀ w₀ w₁ ∈ Wπ,
    Compatibleπ(e, w₀) ∧ Compatibleπ(e, w₁)
    → Evalπ(c, w₀) = Evalπ(c, w₁)

Underdeterminedπ(e, c) :=
  ∃ w₀ w₁ ∈ Wπ,
    Compatibleπ(e, w₀) ∧ Compatibleπ(e, w₁) ∧
    Evalπ(c, w₀) ≠ Evalπ(c, w₁)

ProfileAdmissible(π, c) :=
  ∃ eᵈ ∈ Eπ, Determinateπ(eᵈ, c)

FormallyUnderdeterminationCapable(π, c) :=
  ∃ eᵘ eᵈ ∈ Eπ,
    Underdeterminedπ(eᵘ, c) ∧ Determinateπ(eᵈ, c)
```

Notes:
- `Evalπ(c, w₀) ≠ Evalπ(c, w₁)` entails the semantic distinctness of w₀ and w₁. Canonical serialization (§2.7) prevents the same world from appearing twice.
- `FormallyUnderdeterminationCapable(π, c) → ProfileAdmissible(π, c)`. Both tests remain in preflight for clearer diagnostics.
- `FormallyUnderdeterminationCapable` is a formal property of the frozen profile. It says nothing about operational adequacy (§3, AP1).

### 2.2 Issuance conditions

In the formal core, `e` denotes a canonically closed evidence bundle. An individual admission object is denoted by `a`; the frozen `Bundleπ` function derives `e` from ordered valid admissions, and the closure proof establishes `e ∈ Eπ`.

```text
InstanceCommittedBeforeEvidence(ι, π, c)       -- §2.3
ProfileRegisteredBeforeEvidence(π, ι)          -- §2.4, via replay transcript
ActiveProfileBindingV0(ι, R)                   -- exact profile/verifier resolution below
CoverageClosedThroughCheckpoint(ι, e, S_R)     -- §2.6
FormallyUnderdeterminationCapable(π, c)        -- preflight
e ∈ Eπ
w₀, w₁ ∈ Wπ  (canonical form, §2.7)
Compatibleπ(e, w₀)
Compatibleπ(e, w₁)
Evalπ(c, w₀) ≠ Evalπ(c, w₁)
```

**Frozen and digested before evidence admission:**
- `Wπ`, `Compatibleπ`, `Evalπ`, and claim semantics
- `Eπ` (the space of permitted closed evidence bundles), `AdmissibleItemπ`, `Bundleπ`, and admission rules
- evidence scope, coverage rules, and the rule for forming the closed evidence set
- `LogIdentityV0`, `LeafEncodeV0`, checkpoint key/VDS algorithm, and lifecycle/admitter authorization
- evidence canonicalization and the canonical world codec (§2.7)
- `eᵈ` and `eᵘ`, with membership proofs for `Eπ` and proofs of `Determinateπ(eᵈ, c)` and `Underdeterminedπ(eᵘ, c)`
- `VerifierManifestV0` and its digest, including the exact checker and Lean toolchain artifacts defined below

```text
VerifierManifestV0 binds:
  lean_toolchain_identifier
  lean_toolchain_artifact_digest
  checker_source_tree_digest
  dependency_lock_digest
  build_manifest_digest
  checker_olean_digest_set
  axiom_policy_digest
  acceptance_command_digest

profile.verifier_manifest_ref resolves VerifierManifestV0
profile.verifier_manifest_digest := digest(canonical VerifierManifestV0)

profile_digest binds profile.verifier_manifest_ref and
  profile.verifier_manifest_digest

CertificateTargetV0(π, e, c, w₀, w₁) :=
  e ∈ Eπ                                      ∧
  w₀ ∈ Wπ                                     ∧
  w₁ ∈ Wπ                                     ∧
  Compatibleπ(e, w₀)                          ∧
  Compatibleπ(e, w₁)                          ∧
  Evalπ(c, w₀) ≠ Evalπ(c, w₁)

ActiveProfileBindingV0(ι, R) holds only if:
  FullPrefixReplay finds exactly one valid InstanceCommitment for the
    committed instance tuple                                      ∧
  digest(resolve(R.profile_commitment_ref).canonical_profile_bytes)
    = InstanceCommitment.profile_digest                           ∧
  digest(resolve(profile.verifier_manifest_ref).canonical_manifest_bytes)
    = profile.verifier_manifest_digest                            ∧
  R.verifier_digest = profile.verifier_manifest_digest            ∧
  R.claim_digest = InstanceCommitment.claim_digest                ∧
  every checker source, dependency lock, build manifest, `.olean`
    artifact, axiom policy, acceptance command, and Lean toolchain
    artifact used during verification matches VerifierManifestV0 ∧
  Wπ, Eπ, Compatibleπ, Evalπ, the codecs, and the checker are
    obtained exclusively from that resolved profile               ∧
  certificate.type = CertificateTargetV0(π, e, c, w₀, w₁)         ∧
  the submitted certificate type-checks under exactly those
    resolved profile, verifier, and toolchain artifacts.
```

The resolved checker MUST construct `CertificateTargetV0` exclusively from the committed profile, closed evidence set, committed claim, and canonical receipt witnesses. The certificate MUST NOT supply or select its own target proposition.

Every artifact digest above binds both the exact bytes and its frozen artifact identifier or path and format. An unavailable required profile, manifest, checker, build, dependency, `.olean`, axiom-policy, acceptance-command, or toolchain artifact yields `HALT`, with no epistemic verdict. A digest mismatch, substitution, or certificate checked under any other profile, checker, build, axiom policy, or toolchain yields `REJECT`.

**Preflight rule:**

```text
¬ProfileAdmissible(π, c)                   → preflight HALT, no verdict
¬FormallyUnderdeterminationCapable(π, c)   → profile MUST NOT issue an underdetermination receipt
```

For infinite `Wπ`, `Underdeterminedπ` is still checked with a concrete witness pair and decidable `Compatibleπ` and `Evalπ`. `Determinateπ(eᵈ, c)` is a universal claim: the verifier accepts a Lean proof term, but generation of such a proof is not guaranteed. If no proof term is available, preflight MUST return `HALT`, not an epistemic verdict.

`UnfalsifiableAsStated` is not derived from profile failure. It requires a separate semantic obligation over the claim wording, relativized to the declared world class and evidence language. That obligation is outside this profile.

### 2.3 `InstanceCommitment` and subject

The identified adjudication instance is a subject derived from the issuer/request pair, not a freely chosen `instance_id`:

```text
instance_subject := SubjectDeriveV0(issuer_id, request_id)
```

`SubjectDeriveV0` uses frozen, domain-separated canonical encoding and returns a text string (`tstr`) for CWT `sub`. Its digest is bound by the commitment. Before the first evidence admission, the following MUST be registered:

```text
InstanceCommitment(ι) binds:
  request_id
  issuer_id
  instance_subject
  instance_owner_iss
  log_identity_digest
  leaf_encoding_profile_digest
  claim_digest
  profile_digest
  evidence_scope_digest
  admission_rule_digest
  coverage_rule_digest
  authorized_admitter_set_digest
  subject_derivation_digest
```

- `instance_owner_iss = issuer_id` in the same frozen canonical representation, and the commitment MUST carry a valid owner signature with that protected `iss`.
- Uniqueness is checked **within committed L** by `(instance_owner_iss, request_id, instance_subject)`, where `instance_subject` MUST be the result of `SubjectDeriveV0(issuer_id, request_id)`.
- Full replay MUST find exactly one valid `InstanceCommitment` for that tuple, containing exactly one `profile_digest` and `claim_digest`. Zero commitments yields `HALT`; two or more, or conflicting digests, yield `REJECT`.
- `authorized_admitter_set_digest` binds the exact frozen set of permitted CWT `iss` values.
- All lifecycle statements — profile, commitment, admission, closure, and final P10 adjudication Signed Statement — carry the same **protected CWT `sub`**, equal to `instance_subject`.
- The profile-selection commitment, `InstanceCommitment`, `EvidenceClosure`, and final P10 Signed Statement are valid only with an `instance_owner_iss` signature. Evidence admissions use the separate frozen admitter set. A matching-`sub` lifecycle entry from another `iss` is not valid and is excluded from counts.
- A semantically equivalent natural-language request opened under another `request_id` remains outside the proven completeness scope.

### 2.4 `FullPrefixReplay` and registration order

**Registration order** and checkpoint-bounded coverage are proven by replaying the append-only log, not by timestamps or selected inclusion proofs alone.

```text
LogIdentityV0(L) := CanonicalDigest(
  ts_iss,
  checkpoint_verification_key_fingerprint,
  vds_algorithm,
  leaf_encoding_profile_digest)

LeafEncodeV0(x) := frozen mapping from the exact registered Signed Statement
  bytes and their format/media-type identifier to RFC9162 leaf input
```

“The same L” means the same `LogIdentityV0`: the same TS `iss`, checkpoint verification key, VDS algorithm, and leaf-encoding profile. The commitment's `log_identity_digest` MUST match the L identified by the outer receipt; a mismatch yields `REJECT`.

```text
FullPrefixReplay(L, S_R) :=
  fetch every leaf's exact registered bytes and protected header
    at indices [0, size(S_R))                                ∧
  decode protected sub for SubjectView candidates            ∧
  fetch payload bytes for every SubjectView candidate needed
    to classify lifecycle/admission validity                  ∧
  reconstruct the RFC9162_SHA256 VDS root using LeafEncodeV0 ∧
  reconstructed_root = root(S_R)                            ∧
  verify signed_checkpoint(S_R)
```

The verifier MUST have authorized read access to the leaf bytes and protected headers of the entire Statement Sequence through `S_R`, as well as all payload bytes of subject-view candidates needed for classification under the frozen rules. Payloads for unrelated subjects are not required. Trust in the commitment-bound checkpoint key, VDS algorithm, and `LeafEncodeV0` is an explicit premise. If the complete prefix or a required subject payload is unavailable, the result is `HALT`, with no epistemic verdict.

Replay verifies that the profile and unique commitment were registered before the first relevant admission, that exactly one valid owner-signed closure precedes the final receipt, and that all those entries are in committed L. An entry or proof from another log identity yields `REJECT`; a separate parallel log is outside the claim and MUST be disclosed by the limitation. P10 v0 uses `RFC9162_SHA256` (VDS alg `1`). Inclusion and consistency proofs may accompany the transcript, but do not by themselves prove the absence of other entries.

An RFC 9943 Registration Policy can change, and its rejection of new entries is only defense in depth; it is not a soundness premise of P10 coverage.

### 2.5 `EvidenceAdmission`

```text
AuthorizedAdmitters(ι) := exact CWT iss set committed by
  authorized_admitter_set_digest

AuthorizedLifecycleIssuer(ι) := instance_owner_iss = issuer_id

EvidenceAdmission(a) :=
  registration in L of an authenticated statement binding the canonical
  form of a and proof AdmissibleItemπ(a) under the frozen admission rules:
  a SCITT Signed Statement whose payload is an in-toto Statement v1
  containing the P10 evidence-admission predicate, with
    protected sub = instance_subject                         ∧
    protected iss ∈ AuthorizedAdmitters(ι)                  ∧
    a valid signature for that iss                          ∧
    accessible payload bytes satisfying the frozen rules.
```

A matching `sub` from an unauthorized `iss` is not an admission. If the closure nevertheless cites it, the result is `REJECT`.

For a non-admission lifecycle predicate, a matching-`sub` entry is valid only if it has a valid `AuthorizedLifecycleIssuer(ι)` signature and the expected predicate type. An unauthorized lifecycle entry is excluded from uniqueness counts; if a valid object cites it as a commitment, profile, or closure, the result is `REJECT`.

**Definition-level limitation:** admission is a protocol registration event. Registration order proves that the profile was locked before protocol registration of the evidence; it does not prove when the evidence was created or issued, or that the profile author had not previously seen public data.

### 2.6 `EvidenceClosure` and checkpoint-bounded `CoverageProof`

```text
SubjectView(L, S_R, instance_subject) :=
  every replayed statement at leaf_index < size(S_R)
  whose protected CWT sub = instance_subject

ClosureTranscriptViewπ(L, S_R, ι) :=
  the subsequence of SubjectView containing only:
    valid owner-signed lifecycle entries for ι, or
    RelevantAdmissionπ entries for ι

RelevantAdmissionπ(x, ι) :=
  x ∈ SubjectView(L, S_R, instance_subject)                 ∧
  x is a valid EvidenceAdmission predicate                  ∧
  x.protected_iss ∈ AuthorizedAdmitters(ι)                  ∧
  signature_valid(x)                                       ∧
  payload_accessible(x)                                    ∧
  AdmissibleItemπ(x.payload)

EvidenceClosure(ι) binds:
  instance_subject
  terminal = true
  ordered_admission_refs
  closed_evidence_set_digest
  checkpoint_preclosure_transcript_digest

CoverageProofπ(ι, S_R) verifies:
  FullPrefixReplay(L, S_R)                                  ∧
  exactly one valid InstanceCommitment for the instance tuple ∧
  exactly one valid owner-signed EvidenceClosure for instance_subject ∧
  ordered_admission_refs are in strictly ascending leaf order ∧
  ordered_admission_refs contain no duplicates              ∧
  each ref identifies a RelevantAdmissionπ                  ∧
  every RelevantAdmissionπ before the closure appears exactly once ∧
  no RelevantAdmissionπ occurs after closure and before size(S_R) ∧
  e = Bundleπ(ordered_admission_refs) ∈ Eπ                  ∧
  receipt.evidence_digest = digest(e)
```

- No closure, replay, or required payload bytes → `HALT`, with no epistemic verdict. A conflicting commitment/closure, or an omitted, duplicated, misordered, unauthorized, or post-closure relevant admission → `REJECT`.
- `checkpoint_preclosure_transcript_digest` MUST describe the uninterrupted `ClosureTranscriptViewπ` subsequence immediately before the closure leaf. Entries for other subjects and unauthorized matching-`sub` entries do not invalidate closure. If a valid owner-signed lifecycle entry or `RelevantAdmissionπ` lands between transcript preparation and closure registration, that closure candidate is invalid (fail-closed). The issuer MUST replay the subject view, rebuild the references, and register a new closure; the invalid attempt is not counted as a valid closure.
- The leaf index assigned by committed L is the authoritative total registration order, including entries received in the same batch. `Bundleπ` uses that strictly increasing order; the TS cannot present a different order for the same checkpoint without violating VDS integrity.
- The receipt is computed over closed `e`, not an arbitrarily selected admission. The claim holds only through signed checkpoint `S_R`; a later entry does not retroactively change the historical claim and supports no claim of future absence.
- To avoid a post-registration hash cycle, the issuer-signed payload binds `S_C`, ordered references, and the pre-closure transcript. The outer SCITT Receipt supplies `S_R`; `S_R`, the final replay transcript, and the coverage-verification result are not fields in the issuer-signed payload. Full-prefix replay occurs after receipt acquisition.

### 2.7 Canonical codec

- P10 v0 uses UTF-8 JSON Canonicalization Scheme (JCS, RFC 8785) for claims, structured evidence objects, worlds, and the P10 predicate. The codec digest is part of the profile (§1(1)) and receipt.
- Integers outside the safely interoperable JCS/JSON range, rational numbers, and exact decimal values are encoded as canonical strings under the frozen exact-number schema; they are not emitted as JSON numbers.
- A **unique normal form** applies: `decode ∘ encode = id` on `Wπ`, with exactly one JCS form per decoded world. `Compatibleπ` and `Evalπ` operate on decoded semantic objects; the verifier rejects noncanonical witnesses.
- A structured P10 `*_digest` uses SHA-256 over the corresponding JCS bytes. Binary artifacts are digested over raw bytes together with the frozen format/media-type identifier, not over a JCS reinterpretation. Noncryptographic or merely immutable identifiers are insufficient.

---

## 3. Semantic bridges and declared limitations

Lean checks only the result of executing frozen, executable relations and functions over canonical objects. It checks nothing about the real world.

| Bridge | What Lean checks | What remains an oracle / limitation |
|---|---|---|
| `Compatibleπ` | The frozen relation returns `true` for (e, w₀) and (e, w₁) | Whether the relation faithfully represents real-world compatibility |
| `Evalπ` | The frozen function returns different values on w₀ and w₁ | Whether `Evalπ` faithfully translates the natural-language claim; this is P10 `R_sem` unless the claim is already formal |
| `Eπ` and admission | `e ∈ Eπ` under the frozen rules | Whether `Eπ` realistically covers obtainable evidence |
| Profile adequacy (AP1) | `FormallyUnderdeterminationCapable(π, c)` | Whether the determining evidence fixture is practically obtainable and representative (limitation below) |
| Canonicalization / codec | SHA-256 digest and JCS canonical form match | Whether canonicalization loses claim-relevant information |
| Replay/order | The complete VDS prefix of committed L reconstructs `S_R` and registration order (§2.4) | Authorized access to all leaf/protected-header data and required subject payloads; registration order is not issuance order; other logs are outside the claim |
| Within-batch order | Committed leaf indices define one total registration order | The TS chooses within-batch leaf order; an order-sensitive `Bundleπ` therefore treats that TS choice as an explicit trust assumption |
| Pre-evidence commitment | Profile and instance were registered before protocol admission (§§2.3–2.5) | Does not prove author ignorance of public data or absence of other instances |
| Active profile/verifier | `ActiveProfileBindingV0` resolves the unique instance-bound profile and verifies the certificate using only the checker, build, axiom policy, codecs, dependencies, `.olean` files, and Lean toolchain transitively bound by that profile | Establishes verifier-time recomputation under the committed adjudication profile; it does not establish that a downstream action was governed by the verdict |
| Coverage | `EvidenceClosure` and `CoverageProof` close all valid, registered, in-scope admissions by authorized admitters through `S_R` (§2.6) | Does not prove absence of unregistered/out-of-scope evidence, another `request_id`, or future entries |
| Cryptography | Digests and signatures match | Digest collision resistance, signature unforgeability, and log non-equivocation/integrity |
| Verifier | Kernel type-check plus `#print axioms` audit; the permitted axiom set is explicit in the profile | Trust in the Lean kernel and declared axioms; `sorryAx`, `Lean.ofReduceBool`, and `native_decide` are forbidden |

**AP1 limitation (verbatim, mandatory in the receipt):**

> `FormallyUnderdeterminationCapable` does not establish that the determining evidence fixture is practically obtainable, representative, or likely to occur under the deployed acquisition process. A formally valid profile may remain operationally abstention-biased.

**Coverage/instance limitation (verbatim, mandatory in the receipt):**

> This receipt establishes completeness only within the committed transparency log `L`, for valid, registered, in-scope admissions made by the frozen authorized admitters for the identified `(issuer, request)` subject through the signed checkpoint `S_R`. It does not establish that no commitment or admission for the same `request_id` exists in another transparency log, that no unregistered or out-of-scope evidence exists, that no semantically equivalent request was opened under a different `request_id`, or that no later statement was registered after `S_R`. Verification requires complete VDS-prefix replay of committed `L` and access to all subject payload bytes needed by the frozen admission rules. This receipt establishes uniqueness only for the identified instance tuple within committed `L` through `S_R`. It does not establish that the issuer did not create other instances for the same `claim_digest` under different `request_id` values, bind those instances to different profiles or world classes, or select the presented instance after observing evidence or outcomes.

Where sibling `InstanceCommitment` payloads are accessible, a verifier SHOULD report the number visible through `S_R` for the same `(instance_owner_iss, claim_digest)`. Version 0.1.1 assigns no acceptance or rejection semantics to that count. This recommendation does not expand the payload-availability requirement of `FullPrefixReplay`; mandatory sibling counting requires a future profile with an additional availability or indexing rule.

Introducing a `Reachableπ(e)` predicate does not solve AP1. Lean would check frozen `Reachableπ(eᵈ)`, but not whether that relation faithfully represents physical or practical availability. It would merely move the oracle boundary.

Every row of this table is included in the receipt's `limitations` field. The P10 predicate specification marks `limitations` as a mandatory **must-understand** field: a P10 verifier MUST reject a predicate without it, even though generic in-toto v1 rules otherwise require unknown fields to be ignored.

---

## 4. Issuer-signed fields and post-registration verifier output (outline)

**Inside the issuer-signed P10 payload:**

```text
instance_commitment_ref       -- §2.3, before the first admission
profile_commitment_ref        -- profile registration in L + checkpoint S₁
evidence_admission_refs       -- all instance admissions covered by the closure
evidence_closure_ref          -- §2.6
preclosure_transcript_digest  -- §2.6; independent of S_R
instance_subject              -- protected CWT sub
log_identity_digest           -- committed L, §2.4
claim_digest
evidence_digest               -- over the JCS form of the closed set
codec_digest                  -- §2.7
witness_0_digest, witness_1_digest   -- canonical form
capability_proof_digest       -- eᵈ, eᵘ, and proofs from §2.2
proof_digest                  -- Lean object + axiom audit
verifier_digest               -- equals profile.verifier_manifest_digest
limitations_digest            -- includes verbatim AP1 and coverage/instance text
limitations                   -- mandatory must-understand P10 field
outcome = NotDemonstrated(reason=underdetermined)
```

**Outside the issuer-signed payload, obtained only after registration:**

```text
receipt_checkpoint_ref                 -- SCITT Receipt in COSE unprotected label 394
S_R                                    -- verified checkpoint from the receipt
order_and_coverage_transcript_digest   -- FullPrefixReplay through S_R
coverage_verification_result           -- ACCEPT / REJECT / HALT + diagnostics
```

These post-registration values are P10 verifier output over the Transparent Statement. They may be serialized in a separate verification report, but are not part of the issuer-signed P10 predicate and do not enter its digest. The standard SCITT Receipt remains in COSE unprotected-header label `394`, avoiding a hash cycle.

Before accepting the epistemic outcome, the verifier MUST establish `ActiveProfileBindingV0`. Registration order proves when the committed object entered `L`; it is not by itself evidence that the object was used. P10 establishes verifier-time use by independently resolving the unique instance-bound profile and its `VerifierManifestV0`, matching every required artifact, constructing `CertificateTargetV0` from the committed inputs, and type-checking the submitted certificate against that target under exactly that resolved combination.

**The only v0 envelope:** a SCITT Signed Statement (`COSE_Sign1`) whose payload is an in-toto Statement v1 with the P10 predicate. After registration and attachment of a SCITT Receipt, it becomes a Transparent Statement. Profile commitment, instance commitment, evidence admissions, evidence closure, and final P10 adjudication statement use the same pattern, the same L, and the same protected CWT `sub`. A bare in-toto predicate, standalone signed in-toto envelope, or SCITT Statement without the required Receipt is insufficient. No new wire format is introduced.

---

## 5. Prior art

The following sources were inspected directly on 2026-09-23 unless otherwise stated. The two Internet-Drafts marked 2026-09-27 were added by the v0.1.1 pre-publication prior-art sweep.

| Work / system | Existing coverage | What it does not cover relative to §1 |
|---|---|---|
| **Koomullil, arXiv 2605.16407 v1** | **Paper-reported (per the source snapshot):** the paper defines Supported/Contradicted/Contested/Unknown; `Unknown` is computed using thresholds `θg, θc` (§5.2). The paper-reported Universal Assurance Card has Certified/Partial/Residue/Abstain verdicts; `Abstain` requires nonempty reasons and `residue_coverage = 0` (§§10.2–10.3). Paper-reported Thm 6.3(v) claims evidence anti-monotonicity of MCR under a monotone evidence-to-constraints map. | No concrete P10 world-witness pair bound to the same closed evidence set. The inspected `MCR.lean` contains neither paper-level maximality nor an evidence anti-monotonicity theorem; those claims are therefore not attributed to the verifiable Lean artifact. |
| Ascendr, Inc. | **Company-affiliated research actor confirmed; commercial product deployment not demonstrated.** | — |
| **Pramāṇa (arXiv 2605.20312 v1)** | Typed `ClaimAttestation`; `verify(claim, source)` returns VERIFIED/REJECTED/UNVERIFIABLE; a deterministic theorem prover may be an oracle for `InferenceClaim`; A2A/MCP wire extension and source-byte digest. | Does not freeze a pre-evidence world class or compatibility semantics. UNVERIFIABLE is an outcome label without a concrete divergent witness pair. |
| **ClaimReceipt (arXiv 2609.01992 v1)** | Claim sufficiency is defined over executions: identical retained evidence must imply an identical claim value (§2.1, Eq. 1). It explicitly describes the identification boundary/divergent executions, distinguishes contract and evidential abstention (`I_C`, `I_E`, §5.1), freezes the specification before implementation (§4.1), and places a signed manifest and assignment matrix with an OpenTimestamps proof before prospective ingress (§3.3). Coverage is a set property and requires manifest/ingress commitment before outcome. | P10 closure/reconciliation follows the same broad prospective-ingress/terminal-reconciliation pattern; generic coverage is not novel to P10. The narrower remainder is that ClaimReceipt does not freeze an explicit world class with executable `Compatibleπ`, nor does INCONCLUSIVE carry a concrete divergent witness pair checked by the Lean kernel and registration-order-bound to the profile/instance. |
| **Independent Determinability of Agent Actions (`draft-wadkins-agentproto-action-determinability-00`)** — inspected 2026-09-27 | Defines mechanism-independent determinability requirements for agent transitions. DET-2 requires the specific governing-condition revision to have governed the transition at decision time; prior signing or registration, or availability among multiple compatible candidates, is insufficient. Its candidates are governing-condition sets or policy revisions, not possible worlds assigning different values to an evidential claim. It also requires omission detection or an explicit result that completeness cannot be established when completeness is material. | Defines no evidence format, token, audit system, registry, or transparency service. It does not specify a pre-evidence world class with executable `Compatibleπ` and `Evalπ`, a receipt-carried divergent-world pair, Lean certificate checking, or P10-style checkpoint-bounded evidence closure. P10 does not equate its verifier-time recomputation with Wadkins's claim that governing conditions controlled a downstream transition at decision time. |
| **The `verification.*` Constraint Family (`draft-krausz-verification-state-02`)** — inspected 2026-09-27 | Defines signed claim/ruleset/evidence-bound JWS receipts; `verified`, `contradicted`, `indeterminate`, and `not_evaluated` states; content-addressed evidence sets; local recomputation; immutable content-addressed mapping resolution with digest verification before use and fail-closed mismatch handling; and SCITT-compatible transport. It explicitly states that a pinned evidence set records what the issuer listed but cannot prove disclosure completeness or detect an omission. | Does not establish checkpoint-complete evidence coverage and does not require a pre-evidence committed `Wπ` with executable `Compatibleπ` and `Evalπ`, a concrete divergent-world pair, or a Lean proof that both worlds remain compatible with the same closed evidence set while assigning different claim values. P10's narrower remainder is instance-unique profile resolution plus transitive verifier-toolchain/build binding, not digest-checked ruleset resolution as such. |
| SCITT Agent Action Capsule (draft-mih-…-02) | SCITT receipt with disposition vocabulary | Action disposition, not epistemic underdetermination |
| AWS Automated Reasoning checks | Formal verdicts (VALID/INVALID/SATISFIABLE/IMPOSSIBLE/TRANSLATION_AMBIGUOUS) | No third-party-verifiable receipt or witness pair |
| Supervaluationism, version spaces, partial identification | “True in all admissible models” and monotone narrowing | Not receipt/binding systems |

**Provenance for the Koomullil row:** the complete arXiv HTML v1 was inspected through §§1–17 and the appendices; `gkoomullil/proof-carrying-certificates` was inspected read-only at full commit `8e5b718c4fc1a53678f1da9a94499df3b311d065` (commit timestamp `2026-05-12T18:19:05Z`). `README.txt`, `lean_artifact/EmbeddingSensitivity/MCR.lean` (blob `096f15d486f7190d7018317002a3ba2d137eadab`), and `lean_artifact/EmbeddingSensitivity/AxiomAudit.lean` (blob `83899399f1157d99f06bcc611466186bf26d77b9`) were opened directly. The paper reports threshold-based `Unknown`, Theorem 6.3(v), and the `Abstain` condition. However, the inspected `MCR.lean` has no `p_maximal_over_all` field, maximality theorem, or evidence anti-monotonicity theorem; the last of its three theorems merely repeats `p_residue_cert`. This is a mismatch between paper-level claims and the inspected artifact, not artifact confirmation of those claims. `lake build` was not independently run.

**Narrow differentiation after the v0.1.1 sweep:** P10 claims no novelty for independent determinability, decision-time or pre-evidence binding as a general idea, an `indeterminate` receipt, claim/ruleset/evidence binding, content-addressed evidence, local recomputation, SCITT transport, or the need for coverage and omission controls. The remaining claimed profile-level combination is a concrete divergent-world pair from a pre-evidence committed model class, checked under executable `Compatibleπ` and `Evalπ` semantics by Lean and bound to a unique, instance-specific pre-evidence commitment whose exact profile and verifier-manifest digests are independently resolved and used by the P10 certificate verifier, with registration-order and checkpoint-bounded coverage verification.

---

## 6. Explicit non-claims

- That “two compatible models ⇒ underdetermination” is novel.
- That the receipt identifies the actual world or establishes either claim value as true.
- That `Compatibleπ`, `Evalπ`, or `Eπ` faithfully represents reality (§3).
- That `FormallyUnderdeterminationCapable` means the profile is operationally adequate or unbiased toward abstention (AP1).
- That registration order represents issuance, creation, or first-observation order (§§2.4–2.5).
- That the issuer did not open a semantically equivalent request under another `request_id` (§2.3).
- That the issuer did not create sibling instances for the same `claim_digest` under different `request_id` values, bind them to different profiles or world classes, or select the presented instance after observing evidence or outcomes (§3).
- That no parallel commitment or admission for the same `request_id` exists in another transparency log; the claim is relative only to committed L (§§2.3–2.6).
- That no unregistered or evidence-scope-excluded external evidence exists, or that no entry exists after `S_R`; coverage applies only to frozen admitters and the identified subject through `S_R` (§2.6).
- That profile failure says anything about claim falsifiability (§2.2).
- That P10 is first to use Lean certificates, abstention, or a per-call card (Koomullil, §5).
- That P10 originated independent determinability or the rule against selecting one of several evidence-compatible candidates (`draft-wadkins-agentproto-action-determinability-00`, §5).
- That decision-time or pre-evidence binding is novel as a general idea (Wadkins and ClaimReceipt, §5).
- That an `indeterminate` receipt or reason-coded indeterminate state is novel (`draft-krausz-verification-state-02`, §5).
- That binding a claim, ruleset, or evidence set into a signed receipt is novel (`draft-krausz-verification-state-02`, §5).
- That content-addressed evidence or local receipt recomputation is novel (`draft-krausz-verification-state-02`, §5).
- That SCITT transport for a verification receipt is novel (`draft-krausz-verification-state-02` and existing SCITT profiles, §5).
- That the general need for evidence-coverage or omission controls is novel (Wadkins, ClaimReceipt, and `draft-krausz-verification-state-02`, §5).
- That any downstream action was governed by the receipt's verdict. P10 establishes only that the certificate verifies under the uniquely committed profile and its transitively bound verifier artifacts.
- Anything about market or commercial priority.

---

## 7. Conformance and independent-review criteria

### 7.1 Mutation tests (MUST yield REJECT or the stated outcome)

| # | Mutation | Expected |
|---|---|---|
| M1 | Change `W`, `Compatible`, `Eval`, `Eπ`, `AdmissibleItemπ`, `Bundleπ`, evidence scope, admission/coverage rules, codec, or canonicalization after instance commitment | REJECT |
| M2 | `Compatible := fun _ _ => true` | Fails `FormallyUnderdeterminationCapable`: constant `Evalπ` gives no `eᵘ`; nonconstant `Evalπ` gives no `eᵈ`. Empty `Wπ` makes `Determinateπ` false via `NonemptyCompatibleπ`. No case yields an underdetermination receipt. |
| M3 | Witness outside frozen `Wπ` | REJECT |
| M4 | Two witnesses with the same claim value | REJECT |
| M5 | Receipt without an earlier profile-registration entry | REJECT |
| M6 | Change `limitations` or witness bytes without changing the digest | REJECT |
| M7 | Profile/instance and admission are in different logs, or replay shows admission before commitment | REJECT |
| M8 | Same world in two serializations; noncanonical witness | REJECT |
| M9 | Profile without a determinability witness | Preflight HALT, no adjudication verdict. **Not** `UnfalsifiableAsStated`. |
| M10 | `eᵈ` or `eᵘ` added or replaced after admission | REJECT |
| M11 | Bare in-toto predicate, standalone signed in-toto envelope, or SCITT Statement without the required Receipt | REJECT |
| M12 | Receipt derived from self-reported timestamps instead of §2.4 | REJECT |
| M13 | Claim `c` was not bound by `InstanceCommitment` before first admission, or was replaced afterward | REJECT |
| M14 | No pre-evidence `InstanceCommitment` | Preflight HALT, no adjudication verdict |
| M15 | Within committed L, another `profile_digest` or `claim_digest` exists under `(instance_owner_iss, request_id, instance_subject)` | REJECT |
| M16 | Missing closure/proof, receipt not after closure or not over exactly the closed set, or relevant admission after closure and before `S_R` | Missing closure/proof → HALT; wrong order or omitted, duplicated, injected, or post-closure evidence through `S_R` → REJECT |
| M17 | P10 predicate lacks `limitations`, or verifier ignores it as unknown | REJECT |
| M18 | Selected inclusion/consistency proofs supplied without the complete VDS prefix through `S_R` | HALT, no epistemic verdict |
| M19 | Within committed L, another valid commitment or conflicting profile/claim exists for `(instance_owner_iss, request_id, instance_subject)` | REJECT |
| M20 | Statement has matching `sub`, but `iss` is outside the frozen authorized-admitter set | Not an admission; if cited by closure → REJECT |
| M21 | A replayed `RelevantAdmissionπ` is omitted from `ordered_admission_refs` | REJECT |
| M22 | `RelevantAdmissionπ` occurs after closure but before `size(S_R)` | REJECT |
| M23 | Admission reference is duplicated or references are not in strictly increasing leaf order | REJECT |
| M24 | A detached/encrypted payload required by frozen admission rules is unavailable | HALT, no epistemic verdict |
| M25 | A new relevant entry is registered only after `S_R` | Historical claim remains scoped to `S_R`; no claim of future absence |
| M26 | Same `(issuer_id, request_id)` exists in L1 and L2 | Each receipt claims completeness only within its committed L; no global uniqueness claim |
| M27 | Receipt/replay uses a different TS `iss`, checkpoint key, VDS algorithm, or leaf encoding from committed `LogIdentityV0` | REJECT |
| M28 | Matching-`sub` profile/commitment/closure signed by an `iss` other than `instance_owner_iss` | Not a valid lifecycle entry; if cited by a valid object → REJECT |
| M29 | Admission registered after the pre-closure transcript but before the closure leaf | Closure candidate invalid; replay/rebuild/retry, with no epistemic verdict until a valid closure |
| M30 | Issuer-signed P10 payload contains `S_R`, receipt ref, or final replay/coverage result | REJECT; post-registration values MUST remain outside the payload |
| M31 | Mandatory cross-instance limitation bytes are absent, altered, or do not match `limitations_digest` | REJECT |
| M32 | The verifier loads, checks, or executes a profile whose digest differs from `InstanceCommitment.profile_digest`, even if that profile was registered before evidence admission | REJECT |
| M33 | Checker source, `.olean` artifact, dependency lock, Lean toolchain, axiom policy, acceptance command, or build manifest differs from `VerifierManifestV0` | REJECT; unavailable required artifact → HALT, with no epistemic verdict |
| M34 | Certificate proves a different, weaker, or certificate-supplied proposition instead of checker-constructed `CertificateTargetV0(π, e, c, w₀, w₁)` | REJECT |
| M35 | `receipt.verifier_digest ≠ profile.verifier_manifest_digest` | REJECT |

### 7.2 Adversarial-profile test

| # | Test | Expected |
|---|---|---|
| **AP1** | `Compatibleπ` is strict only for frozen `eᵈ` and trivially `true` for all other evidence in `Eπ` | Formally passes `FormallyUnderdeterminationCapable`. **Not** a soundness hole in the Lean core or a claim counterexample: the issued receipt proves the true proposition `Underdeterminedπ(e, c)` relative to the profile. An independent profile-adequacy review catches it, and the receipt carries the AP1 limitation (§3). Not part of the mathematical core. |

**Profile-adequacy review** is mandatory for every concrete profile before first use, beginning with the Sandia EFC profile. It is a separate gate outside this document.

### 7.3 Prior-art boundary question

> Do Pramāṇa, ClaimReceipt, `draft-wadkins-agentproto-action-determinability-00`, or `draft-krausz-verification-state-02` already require a pre-evidence committed model class with executable compatibility and evaluation semantics and carry a concrete divergent-world witness pair checked against the same closed evidence set?

- **Review answer: No.**
- **Pramāṇa:** its commitment is the `source_digest` of retrieved bytes used by `verify(claim, source)`; it has no pre-evidence commitment of a world class/compatibility semantics. UNVERIFIABLE carries no witness pair.
- **ClaimReceipt:** it has pre-ingress manifest/specification and coverage commitments, but no explicitly frozen `Wπ` with executable `Compatibleπ`, nor an INCONCLUSIVE receipt carrying a concrete divergent witness pair.
- **Independent Determinability of Agent Actions:** its compatible candidates are governing-condition sets or policy revisions, not claim-worlds. It supplies the general compatible-candidate principle, decision-time binding, independent retrospective evaluation, and the requirement to detect omission or report that completeness is unavailable. It deliberately defines no evidence format or transparency service and carries no concrete divergent-world witness pair under frozen executable semantics.
- **The `verification.*` Constraint Family:** it supplies a signed and recomputable claim/ruleset/evidence-bound receipt, an `indeterminate` state, content-addressed evidence, and SCITT compatibility. Its receipt cannot establish disclosure completeness or detect an omitted source, and it carries no P10 divergent-world witness proof.
- The claim therefore survives only as the narrower **profile-and-binding combination** stated in §5: concrete divergent-world witnesses from a pre-evidence committed model class, executable `Compatibleπ` and `Evalπ` checks backed by Lean, a uniquely resolved instance-specific profile and transitively bound verifier manifest, checkpoint-complete evidence coverage, and transparency-log registration-order verification. P10 verifier-time use is not a claim that the verdict governed a downstream action in Wadkins's DET-2 sense.

### 7.4 Publication review requirement

An independent publication review MUST bind the exact SHA-256 of this artifact. The review MUST cover the complete document, including the formal core, closure and coverage semantics, declared trust boundaries, mutation tests, prior-art boundary, and publication metadata. A verdict over any other byte sequence does not apply to this artifact.

---

## 8. Source snapshot and verification boundaries

The following sources were inspected directly on 2026-09-23, with the two identified Internet-Drafts added on 2026-09-27. The verification statements below are limited to the cited source versions and inspected artifacts.

**Primary sources opened directly (Europe/Belgrade; inspection dates stated above):**
- Koomullil, arXiv `2605.16407v1`, complete HTML; linked GitHub repository at commit `8e5b718c4fc1a53678f1da9a94499df3b311d065`, including `README.txt`, `MCR.lean`, and `AxiomAudit.lean`.
- Pramāṇa, arXiv `2605.20312v1`, complete HTML.
- ClaimReceipt, arXiv `2609.01992v1`, complete HTML.
- `draft-wadkins-agentproto-action-determinability-00`, complete Datatracker HTML, dated 2026-09-10 and last updated 2026-09-11.
- IETF Datatracker IPR disclosure 7599, submitted 2026-09-11, naming unpublished pending U.S. provisional application `US64/147765`; the submitter made no licensing declaration at that time. This is a source-reported disclosure record, not a legal conclusion by P10.
- `draft-krausz-verification-state-02`, complete Datatracker HTML, published 2026-09-22.
- RFC 9943: §§3, 5.1.3, 6, 7, 9.1, and 9.3. Protected `sub` groups Transparent Statements and supports subject completeness checks; VDS replayability permits checking every registered structure only for an actor with content access. Registration Policy can change and is not a soundness premise. §9.1 confirms that VDS registration order need not equal issuance order; §9.3 confirms selective registration.
- RFC 9943 Figure 3 defines CWT `iss` and `sub` as `tstr`, places the standard SCITT Receipt in COSE unprotected-header label `394`, binds TS identity to a public key, and leaves concrete VDS structures/proofs dependent on the selected VDS profile. P10 therefore additionally freezes `LogIdentityV0` and `LeafEncodeV0`.
- in-toto Attestation v1 README and `statement.md`: Envelope/Statement/Predicate layers and the rule that a consumer ignores unknown fields unless the predicate specification says otherwise.
- IETF Datatracker important dates: IETF 127 Internet-Draft cutoff `2026-11-02 23:59 UTC`, confirmed on 2026-09-23.

**Not independently executed:** Koomullil `lake build`, all pilot experiments, and the ClaimReceipt reference verifier. Their build/test results remain primary-source self-reports. Source inspection confirms only the content of inspected files at the stated commit; specifically, it found that `MCR.lean` contains neither paper-level maximality nor an evidence anti-monotonicity theorem.

**Excluded:** existence of an automation task and any market/commercial-priority claim.

---

## 9. Publication path

1. Complete an independent English-language publication review over the exact artifact hash specified in the publication manifest.
2. Record a standalone technical verdict that binds that exact hash.
3. Obtain explicit human ratification before publication or visibility changes.
4. After ratification, proceed with profile-adequacy review for the first concrete profile, Lean kernel implementation, reference profile, and Internet-Draft preparation.

---

## 10. Change log

### v0.1.1 — 2026-09-27

- Added `draft-wadkins-agentproto-action-determinability-00` and `draft-krausz-verification-state-02` to the prior-art boundary.
- Restricted the novelty narrative to the concrete P10 divergent-world, executable-semantics, Lean-proof, checkpoint-coverage, and registration-order combination.
- Added explicit non-claims for the concepts anticipated by those drafts.
- Added the mandatory cross-instance selection limitation and the downstream-action non-claim.
- Added `VerifierManifestV0`, `ActiveProfileBindingV0`, and M31–M35 to bind the exact active profile, checker, build, axiom policy, dependencies, `.olean` files, and Lean toolchain transitively into verification, and to require the checker-constructed `CertificateTargetV0` proposition.
- Made no change to the mathematical definitions of `Determinateπ`, `Underdeterminedπ`, or `FormallyUnderdeterminationCapable`, to evidence-closure semantics, or to existing tests M1–M30 and AP1.
