# Related work (precise, minimal)

Provenance rule: statements below are limited to (a) what the profile's own §5 records after direct inspection by the
profile authors, and (b) what the requester described. **In the S1 build environment `datatracker.ietf.org`, IETF and
arXiv hosts were blocked by the egress proxy, so no external source was re-opened here.** Nothing below was independently
verified by this repository's tooling.

## Sergeev, *Claim Boundaries* -01 (as characterized by the requester; not opened)
* §3 — a same-evidence test (a claim is supported only if it holds across the worlds compatible with the same evidence).
* §9 — a verification route; the requester's reading: the Lean-proved proposition must be *the* proposition the statement
  asserts (no proving `Underdetermined(foo)` while issuing for `Underdetermined(bar)`).
S1 addresses that concern *within its own scope* by computing the checked proposition from the committed bytes and digest
(`P10.Bound`, checker-owned statement). It makes no claim about Sergeev's text beyond this. The profile v0.1.1 §5 does not
list this draft, so the exact wording of §3/§9 is unverified here.

## Wadkins, `draft-wadkins-agentproto-action-determinability-00` (as recorded in profile §5/§6)
The profile records (from its authors' inspection on 2026-09-27) that the draft requires decision-time governance
(DET-2), treats selecting one of several evidence-compatible candidates as not determination, and requires omission
detection or an explicit inability result; its candidates are governing-condition sets, not claim-worlds. P10's
verifier-time recomputation is **not** equated with decision-time binding; this repository proves nothing about
decision time.

## Others recorded in profile §5
Koomullil (arXiv 2605.16407), Pramāṇa (2605.20312), ClaimReceipt (2609.01992), `draft-krausz-verification-state-02`
— see the profile; not repeated.

## Positioning
P10 operationalizes the same-evidence support test as an explicit witness-carrying, machine-checkable artifact under
committed executable profile semantics, with exact profile/evidence/witness/proof/verifier bindings suitable for
transparent registration.

P10 does **not** claim: that the same-evidence countermodel criterion is novel; that a Lean certificate shows model
adequacy; that failing to find witnesses means determinate; that a SCITT receipt establishes epistemic truth; that
decision-time binding exists (it was not proved).
