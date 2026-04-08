# MaleyLean

## Navier--Stokes formalization status

This repository now contains a manuscript-facing Lean scaffold for the
Navier--Stokes project behind:

`Carrier Universality and Global Smoothness for the Periodic 3D Navier--Stokes Equations`

The current formalization is intentionally primitives-first. It does not claim
to be a full Lean proof of the classical periodic 3D Navier--Stokes global
regularity theorem from standard analysis alone. Instead, it formalizes the
structural route, the manuscript-facing claim map, and the exact point where
the remaining analytic burden sits.

### What is formalized

- A primitive core for carrier, standing, admissibility, continuation, horizon
  witness, restart transport, maximal-lineage closure, and no-second-gate
  reasoning.
- A primitive no-blowup boundary stated honestly as a structural result, with
  restart transport kept explicit rather than hidden.
- A primitive-to-PDE obligation register and concrete obligation inventory.
- A verbatim subsection register keyed to actual extracted manuscript titles.
- A verbatim theorem register keyed to actual extracted theorem, lemma,
  proposition, and corollary titles.
- A verbatim dependency spine showing which theorem titles are structurally
  closed, which title marks the named failure boundary, and which endpoint
  titles remain downstream of that boundary.

### What is closed

The Lean surface certifies the structural part of the manuscript route as
axiom-free. In particular, the current finalized manuscript-facing layers are:

- `MaleyLean.NavierStokesVerbatimSubsectionRegister`
- `MaleyLean.NavierStokesVerbatimTheoremRegister`
- `MaleyLean.NavierStokesVerbatimDependencySpineSimple`
- `MaleyLean.NavierStokesPaperSurfaceSummary`

The top-level summary theorem in
`MaleyLean.NavierStokesPaperSurfaceSummary` packages the current state into one
axiom-free manuscript-facing statement.

### What is not claimed

This repository does not currently claim:

- a full end-to-end Lean proof of periodic 3D Navier--Stokes global smoothness
  in the usual PDE sense
- closure of the missing analytic bridge at the vortex-stretching step
- replacement of the named analytic burden with a hidden structural shortcut

### Named analytic boundary

The remaining analytic burden is isolated explicitly rather than blurred across
the development.

- Named failure boundary:
  `Pointwise vortex-stretching gate collapse`
- Downstream endpoint titles:
  `Official periodic theorem on T^3 (Fefferman (B); official classical restatement of Corollary 21A)`
  and
  `No finite-time blow-up on the official periodic carrier`

In the current Lean surface, those endpoint titles are marked as downstream of
the named vortex-stretching failure line.

### How to read the current surface

If you want the shortest path through the finalized Navier--Stokes layer, read
these in order:

1. `MaleyLean/NavierStokesPrimitiveNoBlowup.lean`
2. `MaleyLean/NavierStokesPDEObligationInventory.lean`
3. `MaleyLean/NavierStokesVerbatimSubsectionRegister.lean`
4. `MaleyLean/NavierStokesVerbatimTheoremRegister.lean`
5. `MaleyLean/NavierStokesVerbatimDependencySpineSimple.lean`
6. `MaleyLean/NavierStokesPaperSurfaceSummary.lean`

### Verification

The final manuscript-facing Navier--Stokes surface has dedicated axiom checks,
including:

- `NavierStokesVerbatimSubsectionRegisterAxiomCheck.lean`
- `NavierStokesVerbatimTheoremRegisterAxiomCheck.lean`
- `NavierStokesVerbatimDependencySpineSimpleAxiomCheck.lean`
- `NavierStokesPaperSurfaceSummaryAxiomCheck.lean`

Their audit files report the finalized surface as axiom-free.
