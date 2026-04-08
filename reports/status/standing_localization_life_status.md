# Standing Localization Lean Status

## Current state

The manuscript

`Standing Localization and the Structural Inevitability of Life`

is now integrated in the Lean workspace to the repo's no-axiom standard.

## What is in Lean

The current Lean surface is centered in:

- `MaleyLean/Papers/StandingLocalizationLife/PaperStatements.lean`

with audit coverage in:

- `Checks/Axiom/StandingLocalizationLifeAxiomCheck.lean`

Together, these give the project:

- a standing-to-localization interface
- a non-standing exclusion for globally coordinated regimes
- a persistence-to-internal-regulation bridge
- a minimal-life collapse theorem from internal regulation
- the paper's conditional inevitability theorem
- a bundled verified-core theorem

## Main files

- `papers/standing_localization_life/main.tex`
- `papers/standing_localization_life/README.md`
- `MaleyLean/Papers/StandingLocalizationLife/PaperStatements.lean`
- `Checks/Axiom/StandingLocalizationLifeAxiomCheck.lean`
- `reports/support_maps/standing_localization_life_support_map.txt`
- `reports/audits/standing_localization_life_axiom_audit.txt`

## Verification

The dedicated module and axiom check build successfully, and the root
`MaleyLean` / `Checks` targets still build with the new import included.

The current theorem surface is axiom-free.

## Honest boundary

What is certified here is the paper's structural theorem chain relating
standing, localization, perturbation persistence, internal regulation, and
minimal life-like organization.

What is not yet internalized in full detail is:

- a low-level physical semantics for spatial or energetic localization
- a dynamical perturbation model beyond the current structural interface
- a biochemical or computational realization theory of life

So the current result should be read as a repo-native no-axiom formalization of
the manuscript's structural core, not as a complete foundational life theory.
