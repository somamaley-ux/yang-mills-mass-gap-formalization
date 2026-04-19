# Yang--Mills Extension Stack

This folder contains the Lean-facing extension stack for the nonlocal
Yang--Mills endpoint paper.

## Main point

The main human-facing result here is the analytical mechanization of four
critical seams:

- the QE3 density / graph-core handoff
- the dyadic-to-continuous-time OS upgrade
- the continuum transport / sharp-gap bridge
- the Section 8 endpoint / admissibility bridge

These are the main transitions that used to be easiest to describe only at a
high level. In the current stack they are isolated as named theorem surfaces,
reduced payloads, proof-home projections, source-route recoveries, and direct
reconstruction paths.

## Manuscript shape

The stack is organized in manuscript-facing terms:

- `EndpointTheoremScopeObjects.lean` fixes the theorem-scope support/label
  object layer.
- `EndpointConcreteTheoremScopeBridge.lean` realizes that layer in the existing
  reconstructed-sector carrier.
- `EndpointGlobalFormRecoveryFormalization.lean` packages the Section 7
  same-local-shadow / different-global-form recovery surface.
- `EndpointCompletionBridgeFormalization.lean`,
  `EndpointClayConclusionFormalization.lean`, and
  `EndpointConcretePreferredRouteCompatibility.lean` carry the Section 8
  completion/admissibility bridge.

On the QE3 side, the main seam files are:

- `VacuumGapConcreteCriticalSeam.lean`
- `VacuumGapConcreteOSTimeUpgradeProjection.lean`
- `VacuumGapConcreteContinuumTransportProjection.lean`

## Suggested reading order

If you want the shortest route through the extension story, read:

1. `EndpointFormalizationOverview.lean`
2. `VacuumGapConcreteCriticalSeam.lean`
3. `VacuumGapConcreteOSTimeUpgradeProjection.lean`
4. `VacuumGapConcreteContinuumTransportProjection.lean`
5. `EndpointConcreteTheoremScopeBridge.lean`
6. `EndpointGlobalFormRecoveryFormalization.lean`
7. `EndpointConcretePreferredRouteCompatibility.lean`

For the human-facing summary outside the code tree, see:

- `reports/status/yang_mills_extension_status.md`
- `reports/status/yang_mills_status.md`
- `MaleyLean/Papers/YangMills/FormalizationStatus.md`

## Residuals

The remaining abstraction is now relatively narrow:

- the most paper-faithful concrete instantiation of the theorem-scope
  extended-support class is still a strengthening target
- the final Section 8 bridge still has a manuscript-packaging residue, even
  though the current development now records that this is packaging rather than
  extra mathematical content
