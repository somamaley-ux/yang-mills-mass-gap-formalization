# Godel Lean Status

## Current state

The updated Godel manuscript is now reflected in the Lean workspace at the
manuscript-facing level.

Updated manuscript title:

`Non-Instantiability of Same-Domain Godel Threat Architectures in the Unique Admissible Interior`

## What is in Lean

The current Godel surface has two layers worth distinguishing.

- The main paper-facing theorem surface remains in
  `MaleyLean/GodelPaperStatements.lean`.
- The updated manuscript wording and section/theorem naming layer now appears
  in `MaleyLean/GodelVerbatimRegister.lean`.

Together, these give the project:

- the existing theorem spine for same-domain Godel threat exhaustion
- the terminal non-instantiability theorem surface
- a refreshed manuscript-title register
- a refreshed section/theorem-title register keyed to the updated draft

## What changed in the update

The new draft is more explicitly kernel-first and now presents itself under the
"same-domain Godel threat architectures" title. The updated Lean refresh does
not rebuild the entire theorem surface from scratch, because the current
`GodelPaperStatements.lean` already covers the main logical spine.

Instead, the refresh adds a verbatim manuscript register so the Lean side now
tracks the revised title and major section/theorem labels.

## Main files

- `MaleyLean/GodelPaperStatements.lean`
- `MaleyLean/GodelVerbatimRegister.lean`
- `GodelAxiomCheck.lean`
- `GodelVerbatimRegisterAxiomCheck.lean`
- `godel_axiom_audit.txt`
- `godel_verbatim_register_axiom_audit.txt`

## Verification

The updated Godel verbatim layer is axiom-free, and the root
`MaleyLean.lean` import surface still checks with the new register included.

## Best next move

If we keep pushing this paper, the natural next step is the same one we used
for Navier--Stokes:

1. add a cleaner human-facing summary block to the repo README
2. refresh the old support map so it points to the updated manuscript title and
   the new verbatim register
3. optionally add a tighter claim-by-claim theorem ledger if the manuscript
   continues to evolve
