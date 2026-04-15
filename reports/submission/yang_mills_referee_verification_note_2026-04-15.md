# Yang-Mills Referee Verification Note

Date: 2026-04-15

## Purpose

This note tells a referee what can presently be checked in the Lean repository
without overstating the formalization.

## Current strongest checkable theorem boundary

The strongest current submission-facing theorem is:

- `MaleyLean.YangMillsFullManuscriptNativePackageExportStatement`

Defined in:

- `MaleyLean/Papers/YangMills/Kernel/FullManuscriptNativePackage.lean`

Surface summary:

- `MaleyLean/Papers/YangMills/Surface/FullManuscriptNativePackageSummary.lean`

This theorem packages, in one axiom-free statement:

- public scope,
- the Part C constructive paper statement,
- the Part D Route 1 paper statement,
- the endpoint paper statement,
- key theorem labels including `5.74A`, `5.74`, `5.75`, `5.76`, `5.77`,
  `M.5`, `O.2`, `O.3`, and `O.5`,
- and the corresponding constructive, vacuum-gap, and endpoint witness layer
  exposed by the current native package stack.

## Supporting verification artifacts

The most relevant audit targets are:

- `Checks.Axiom.YangMillsConstructiveTheoremObjectsAxiomCheck`
- `Checks.Axiom.YangMillsVacuumGapTheoremObjectsAxiomCheck`
- `Checks.Axiom.YangMillsVacuumGapMassGapChainAxiomCheck`
- `Checks.Axiom.YangMillsVacuumGapMassGapCompatibilityAxiomCheck`
- `Checks.Axiom.YangMillsVacuumGapChosenSiteBridgeObjectsAxiomCheck`
- `Checks.Axiom.YangMillsEndpointTheoremObjectsAxiomCheck`
- `Checks.Axiom.YangMillsVacuumGapEndpointBridgeObjectsAxiomCheck`
- `Checks.Axiom.YangMillsRoute1EndpointNativePackageAxiomCheck`
- `Checks.Axiom.YangMillsFullManuscriptNativePackageAxiomCheck`

The current repository audit reports that
`YangMillsFullManuscriptNativePackageExportStatement` is axiom-free.

## Best way to use the Lean material

The Lean repository is best used as:

- a theorem-routing and dependency audit layer,
- a source-label and witness-label concordance,
- and a checkable packaging of the main constructive, mass-gap, and endpoint
  interfaces.

It should not presently be read as a complete replacement for referee review of
the analytic arguments in the manuscript and companions.

## Current accurate scope claim

The accurate present claim is:

- axiom-free manuscript-facing native package verification with explicit theorem
  and witness anchors.

The inaccurate stronger claim would be:

- that every underlying analytic Yang--Mills argument has already been fully
  internalized as a foundational Lean proof.
