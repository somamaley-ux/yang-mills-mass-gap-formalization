# Yang-Mills Repo Inspection Note

Date: 2026-04-15

## Fast inspection path

For a fast repository inspection, the most useful files are:

1. `reports/audits/yang_mills_submission_layer_audit_2026-04-15.md`
2. `reports/status/yang_mills_status.md`
3. `reports/support_maps/yang_mills_support_map.txt`
4. `MaleyLean/Papers/YangMills/Kernel/FullManuscriptNativePackage.lean`
5. `MaleyLean/Papers/YangMills/Surface/FullManuscriptNativePackageSummary.lean`

## What each file tells you

- The submission-layer audit states the strongest current referee-facing Lean
  claim.
- The status note explains what is complete and what is not.
- The support map shows how the manuscript-facing Yang--Mills stack is layered.
- The kernel file gives the current top native package.
- The surface summary gives the corresponding high-level exported proposition.

## Minimal verification path

If a referee wants only the most relevant check, the key target is:

- `Checks.Axiom.YangMillsFullManuscriptNativePackageAxiomCheck`

This is the shortest route to verifying that the current top package export is
axiom-free at the repository audit boundary.

## Recommended use

Use the repository as a structural and theorem-routing aid while reading the
core paper and companions, not as a substitute for mathematical judgment about
the underlying analytic arguments.
