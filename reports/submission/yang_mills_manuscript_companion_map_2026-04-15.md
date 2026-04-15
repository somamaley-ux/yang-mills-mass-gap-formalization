# Yang-Mills Manuscript and Companion Map

Date: 2026-04-15

## Core paper

Primary role:

- states the main Yang--Mills result in submission form,
- carries the main proof spine at journal-manageable length,
- and points outward only where longer technical development is needed.

Lean-facing role:

- aligns to the top manuscript package boundary
  `YangMillsFullManuscriptNativePackageExportStatement`.

## Companion I

Primary role:

- ultraviolet gate and Route 1 mass-gap chain,
- including the transport-to-gap pathway that feeds the downstream `M.5`
  boundary.

Lean-facing role:

- aligns mainly to the vacuum-gap side, especially the Route 1, transport,
  reconstruction, and `M.5` package stack.

Key Lean package family:

- `VacuumGapTheoremObjects`
- `VacuumGapMassGapChain`
- `VacuumGapMassGapCompatibility`
- `VacuumGapChosenSiteBridgeObjects`

## Companion II

Primary role:

- Lane A sharp local constructive development.

Lean-facing role:

- aligns mainly to the constructive side and its finite-cap, sharp-local,
  bounded-state, and inductive-union layers.

Key Lean package family:

- `ConstructiveTheoremObjects`
- `ConstructiveNativeProofHomes`
- `ConstructivePrimitiveConstructions`

## Companion III

Primary role:

- reconstruction, non-triviality, and faithful Wilson universality material.

Lean-facing role:

- aligns mainly to the endpoint side and the vacuum-gap to endpoint bridge.

Key Lean package family:

- `EndpointTheoremObjects`
- `EndpointNativeProofHomes`
- `EndpointPrimitiveConstructions`
- `VacuumGapEndpointBridgeObjects`

## How the parts fit together

The editorially relevant division is:

- core paper for the main result and readable proof spine,
- Companion II for the constructive heart,
- Companion I for the Route 1 mass-gap heart,
- Companion III for the endpoint reconstruction and universality heart.

The Lean repository mirrors that division and ties the three hearts together in
one top theorem-facing package rather than leaving the companions as disconnected
appendices.
