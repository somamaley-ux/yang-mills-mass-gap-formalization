# Hypercube Symmetry Saturation Lean Status

## Current state

The manuscript

`Symmetry Constraints and Saturation in the Hypercube`

is now integrated in the Lean workspace to the repo's no-axiom standard.

## What is in Lean

The current Lean surface is centered in:

- `MaleyLean/Papers/HypercubeSymmetrySaturation/PaperStatements.lean`

with audit coverage in:

- `Checks/Axiom/HypercubeSymmetrySaturationAxiomCheck.lean`

Together, these give the project:

- a full-symmetry obstruction statement
- a maximal `S_n`-compatibility boundary for vertex-transitive symmetry
- the exact `S_n` minimum-edge formula as a certified theorem surface
- an extremizer-classification package
- a symmetry-cost statement
- a boundary-sharpness theorem
- a bundled verified-core theorem

## Main files

- `papers/hypercube_symmetry_saturation/main.tex`
- `papers/hypercube_symmetry_saturation/README.md`
- `MaleyLean/Papers/HypercubeSymmetrySaturation/PaperStatements.lean`
- `Checks/Axiom/HypercubeSymmetrySaturationAxiomCheck.lean`
- `reports/support_maps/hypercube_symmetry_saturation_support_map.txt`
- `reports/audits/hypercube_symmetry_saturation_axiom_audit.txt`

## Verification

The dedicated module and axiom check build successfully, and the root
`MaleyLean` / `Checks` targets still build with the new import included.

The current theorem surface is axiom-free.

## Honest boundary

What is certified here is the paper's structural theorem surface for symmetry
constraints and saturation in the hypercube.

What is not yet internalized in full detail is:

- a low-level graph-theoretic hypercube library
- explicit edge-orbit and 4-cycle enumeration machinery
- a constructive catalog of extremizers beyond the current theorem-facing layer

So the current result should be read as a repo-native no-axiom formalization of
the manuscript's combinatorial theorem spine, not as a complete graph-theory
development of hypercube saturation.
