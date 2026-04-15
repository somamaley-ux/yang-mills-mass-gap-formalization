# Yang-Mills Submission Layer Audit

Date: 2026-04-15

## Purpose

This note records the current referee-facing Yang-Mills submission boundary in
this checkout.

It is narrower and more concrete than a general status note. Its purpose is to
say exactly:

- what the strongest current submission-facing Lean object is,
- what manuscript claims and witness labels it exposes,
- which verification artifacts support it,
- and what still lies outside that native boundary.

## Current submission-facing boundary

The strongest current native manuscript package is:

- `MaleyLean/Papers/YangMills/Kernel/FullManuscriptNativePackage.lean`

Its top export theorem is:

- `MaleyLean.YangMillsFullManuscriptNativePackageExportStatement`

This theorem packages, in one axiom-free statement:

- public scope,
- the Lane A / Part C paper statement,
- the Route 1 / Part D paper statement,
- the endpoint paper statement,
- Lane A source labels `5.74A`, `5.74`, `5.75`, `5.76`, `5.77`,
- downstream source labels `M.5`, `O.2`, `O.3`, `O.5`,
- the constructive bounded-base witness label `5.76`,
- the vacuum-gap transport-origin witness label `M.5`,
- the endpoint exact-endpoint witness label `O.5`,
- the constructive bounded-base witness itself,
- the reconstructed Minkowski-gap witness itself,
- and the exact local-net endpoint witness itself.

So the current submission layer is no longer only:

- theorem-register inventory,
- packet architecture,
- source-label crosswalk,
- or manuscript-completion packaging.

It now includes one native theorem-facing object spanning the constructive,
vacuum-gap, and endpoint hearts together.

## Supporting native package stack

The current submission boundary rests on these deeper packages.

### Lane A / constructive side

- `MaleyLean/Papers/YangMills/Kernel/ConstructiveTheoremObjects.lean`

Key export:

- `MaleyLean.YangMillsConstructiveNativeTheoremObjectsExportStatement`

This exposes the theorem labels and chosen-site witness path for the Lane A
finite-cap and sharp-local chain.

### Vacuum-gap / mass-gap side

- `MaleyLean/Papers/YangMills/Kernel/VacuumGapTheoremObjects.lean`
- `MaleyLean/Papers/YangMills/Kernel/VacuumGapMassGapChain.lean`
- `MaleyLean/Papers/YangMills/Kernel/VacuumGapMassGapCompatibility.lean`
- `MaleyLean/Papers/YangMills/Kernel/VacuumGapChosenSiteBridgeObjects.lean`

Key exports:

- `MaleyLean.YangMillsVacuumGapNativeTheoremObjectsExportStatement`
- `MaleyLean.YangMillsVacuumGapMassGapChainExportStatement`
- `MaleyLean.YangMillsVacuumGapMassGapCompatibilityExportStatement`
- `MaleyLean.YangMillsVacuumGapChosenSiteBridgeExportStatement`

These expose the current native `F.216 -> F.5 -> M.5` pathway with typed
objects and chosen-site compatibility laws.

### Endpoint / universality side

- `MaleyLean/Papers/YangMills/Kernel/EndpointTheoremObjects.lean`

Key export:

- `MaleyLean.YangMillsEndpointNativeTheoremObjectsExportStatement`

This exposes the reconstruction and universality side with explicit theorem
labels and endpoint witness labels.

### Inter-heart bridge

- `MaleyLean/Papers/YangMills/Kernel/VacuumGapEndpointBridgeObjects.lean`
- `MaleyLean/Papers/YangMills/Kernel/Route1EndpointNativePackage.lean`

Key exports:

- `MaleyLean.YangMillsVacuumGapEndpointBridgeExportStatement`
- `MaleyLean.YangMillsRoute1EndpointNativePackageExportStatement`

These carry the current native `M.5 -> O.2 / O.3 / O.5` bridge and the
submission-facing Route 1 to endpoint package just below the full manuscript
package.

## Verification status

The current submission boundary is supported by live Lean verification in this
checkout.

Relevant verification targets:

- `Checks.Axiom.YangMillsConstructiveTheoremObjectsAxiomCheck`
- `Checks.Axiom.YangMillsVacuumGapTheoremObjectsAxiomCheck`
- `Checks.Axiom.YangMillsVacuumGapMassGapChainAxiomCheck`
- `Checks.Axiom.YangMillsVacuumGapMassGapCompatibilityAxiomCheck`
- `Checks.Axiom.YangMillsVacuumGapChosenSiteBridgeObjectsAxiomCheck`
- `Checks.Axiom.YangMillsEndpointTheoremObjectsAxiomCheck`
- `Checks.Axiom.YangMillsVacuumGapEndpointBridgeObjectsAxiomCheck`
- `Checks.Axiom.YangMillsRoute1EndpointNativePackageAxiomCheck`
- `Checks.Axiom.YangMillsFullManuscriptNativePackageAxiomCheck`

The decisive current result is:

- `MaleyLean.YangMillsFullManuscriptNativePackageExportStatement` does not
  depend on any axioms.

## Referee-facing reading

The most accurate current submission statement supported by this repo is:

- the encoded Yang-Mills manuscript inventory is represented in Lean,
- the theorem/source crosswalk matches the manuscript corpus used by the repo,
- the manuscript-instantiation layer is closed,
- the manuscript-facing theorem surface is axiom-free,
- and the current top native theorem object packages the constructive,
  mass-gap, and endpoint chains together with explicit theorem-label and
  witness-label anchors.

## What remains outside this boundary

This submission layer still does not amount to:

- a full native Lean proof of the analytic Yang-Mills/QFT arguments,
- elimination of the imported standard framework assumptions,
- or a theorem-by-theorem native derivation of every argument internal to the
  route objects.

So the current submission-grade claim should be framed as:

- an axiom-free manuscript-faithful native theorem-object formalization with a
  closed manuscript instance and explicit theorem/witness crosswalks,

not as:

- a fully internalized Lean proof of all analytic proof homes cited by the
  manuscript.

## Bottom line

The submission layer is now materially stronger than a structural ledger or
surface summary.

It is centered on one axiom-free full-manuscript native package that spans:

- Part A public scope,
- Part C constructive closure,
- Part D mass-gap transport and transfer,
- and endpoint universality / exactness.

That is the current best Lean boundary to cite in a referee-facing submission
note.
