# Yang--Mills Referee Checklist

Date: 2026-04-19

## Purpose

This checklist is for a skeptical referee who wants the shortest path through
the current Lean-supported extension package.

It is deliberately narrow: each item corresponds to one likely objection and
one concrete place to inspect.

## Checklist

1. Verify that the top manuscript-facing package boundary is real and axiom-free.
   Check:
   - `MaleyLean.YangMillsFullManuscriptNativePackageExportStatement`
   - `Checks.Axiom.YangMillsFullManuscriptNativePackageAxiomCheck`
   - `reports/submission/yang_mills_referee_verification_note_2026-04-15.md`

2. Verify that the project is not only a theorem register.
   Check the four seam files:
   - `MaleyLean/Papers/YangMills/Extension/VacuumGapConcreteCriticalSeam.lean`
   - `MaleyLean/Papers/YangMills/Extension/VacuumGapConcreteOSTimeUpgradeProjection.lean`
   - `MaleyLean/Papers/YangMills/Extension/VacuumGapConcreteContinuumTransportProjection.lean`
   - `MaleyLean/Papers/YangMills/Extension/EndpointConcretePreferredRouteCompatibility.lean`

3. Verify that Section 4 has a fixed canonical theorem-scope object and bridge.
   Check:
   - `YMSection4CanonicalTheoremScopePackage`
   - `YMSection4CanonicalTheoremScopeBridge`
   - `YMSection4CanonicalTheoremScopePackageBridge`
   in:
   - `MaleyLean/Papers/YangMills/Extension/EndpointTheoremScopeObjects.lean`
   - `MaleyLean/Papers/YangMills/Extension/EndpointTaggedTheoremScopeRealization.lean`

4. Verify that Section 7 is attached directly to that chosen Section 4 route.
   Check:
   - `YMCompanionIIIGlobalFormRecoveryPackage`
   - `YMCompanionIIIGlobalFormRecoveryPackageFromDistinction`
   - `YMSection7_PreferredGlobalFormRecovery`
   - `YMSection7_PreferredGlobalFormRecoveryOfPackage`
   in:
   - `MaleyLean/Papers/YangMills/Extension/EndpointGlobalFormRecoveryFormalization.lean`
   - `MaleyLean/Papers/YangMills/Extension/EndpointTaggedManuscriptCorollaries.lean`

5. Verify that Section 8 has one canonical theorem surface.
   Check:
   - `YMSection8_CanonicalPreferredEndpointTheorem`
   - `YMSection8_CanonicalPreferredClayEndpoint`
   - `YMSection7And8_CanonicalPreferredEndpointCorollary`
   in:
   - `MaleyLean/Papers/YangMills/Extension/EndpointConcretePreferredRouteCompatibility.lean`

6. Verify that nearby Section 8 routes collapse back to that canonical theorem.
   Check:
   - `YMSection8_PreferredClayEndpointFromStructuredBridgeTarget_eq_canonical`
   - `YMSection8_PreferredClayEndpointFromClosedManuscriptBoundaryBridgeViaRoute1EndpointSecondSeam_eq_canonical`
   - `YMSection8_PreferredClayEndpointFromClosedManuscriptBoundaryBridgeViaRoute1EndpointPaperSecondSeam_eq_canonical`
   - `YMSection8_PreferredClayEndpointFromPatchedAssumptionBundleTargetOfBoundaryBridge_eq_canonical`

7. Verify that the repo states its own non-claims honestly.
   Check:
   - `reports/status/yang_mills_solution_dossier.md`
   - `reports/submission/yang_mills_completion_memo_2026-04-19.md`
   - `reports/submission/yang_mills_referee_verification_note_2026-04-15.md`

8. Verify that the post-freeze edits are documented as presentation polish,
   not theorem-content drift.
   Check:
   - `reports/status/yang_mills_post_freeze_roadmap.md`
   - `reports/status/yang_mills_extension_status.md`

## Recommended reading order

If time is short, inspect in this order:

1. `reports/submission/yang_mills_referee_verification_note_2026-04-15.md`
2. `reports/status/yang_mills_hostile_referee_audit.md`
3. `reports/submission/yang_mills_completion_memo_2026-04-19.md`
4. `MaleyLean/Papers/YangMills/Extension/EndpointConcretePreferredRouteCompatibility.lean`
5. `MaleyLean/Papers/YangMills/Extension/EndpointTheoremScopeObjects.lean`
6. `MaleyLean/Papers/YangMills/Extension/EndpointTaggedTheoremScopeRealization.lean`
7. `MaleyLean/Papers/YangMills/Extension/EndpointGlobalFormRecoveryFormalization.lean`
8. `MaleyLean/Papers/YangMills/Extension/EndpointTaggedManuscriptCorollaries.lean`
