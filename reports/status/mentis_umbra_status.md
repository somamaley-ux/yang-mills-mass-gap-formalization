# Mentis Umbra Lean Status

## Current state

The manuscript

`Mentis Umbra: Consciousness, Agency, and Qualia as Admissible Projections`

is now integrated in the Lean workspace to the repo's no-axiom standard.

## What is in Lean

The current Mentis Umbra surface is centered in:

- `MaleyLean/Papers/MentisUmbra/ProjectionCore.lean`
- `MaleyLean/Papers/MentisUmbra/PaperStatements.lean`

with audit coverage in:

- `Checks/Axiom/MentisUmbraAxiomCheck.lean`

Together, these give the project:

- a single-system projection package built from mediator factorization and invariant reference structure
- a necessity-under-removal theorem at the projection-component level
- a role-based classification layer for agency, intentionality, and interior representation as derived role predicates
- a bridge to existing repo results on admissible-interior uniqueness and standing-classifier collapse
- a multi-system layer for pairwise mediators, global factorization through product-style mediator data, and obstruction from compatibility failure
- a bundled verified-core theorem for the current paper-facing formal surface

## What changed in the integration

The manuscript text explicitly presents itself as assuming framework axioms in prose.
The Lean integration does not import those prose axioms directly. Instead, it
recasts the paper's structural claims as explicit hypothesis-driven declarations
and derives part of the surface from already existing repo infrastructure such as
admissible-interior uniqueness and standing-classifier collapse.

This means the result is a repo-native no-hidden-axiom reformulation of the
paper's theorem surface rather than a literal transcription of every axiom block
in the TeX source.

## Main files

- `papers/mentis_umbra/main.tex`
- `papers/mentis_umbra/README.md`
- `MaleyLean/Papers/MentisUmbra/ProjectionCore.lean`
- `MaleyLean/Papers/MentisUmbra/PaperStatements.lean`
- `Checks/Axiom/MentisUmbraAxiomCheck.lean`
- `reports/support_maps/mentis_umbra_support_map.txt`
- `reports/audits/mentis_umbra_axiom_audit.txt`

## Verification

The dedicated Mentis Umbra modules and axiom check build successfully, and the
root `MaleyLean` / `Checks` targets still build with the new import surface.

The current Mentis Umbra theorem surface is axiom-free.

## Honest boundary

What is certified here is the manuscript-facing structural theorem layer for
projection, reference, role-classification, pairwise mediation, and global
compatibility.

What is not yet internalized in full detail is:

- a low-level syntactic alpha-renaming library for typed name supply
- an explicit computational semantics for the envelope/operator layer
- a richer concrete realization of the multi-agent compatibility machinery

So the current result should be read as fully integrated to the repo's no-axiom
standard for its present theorem surface, not as a complete foundational
formalization of every informal semantic notion used in the manuscript prose.
