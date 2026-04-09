# Remaining Yang-Mills Manuscript Witness Elimination Map

Last updated: 2026-04-10

## Purpose

The concrete manuscript-instantiation core is now down to three witness bundle axioms:

- `ym_endpoint_decl_bundle`
- `ym_constructive_decl_bundle`
- `ym_vacuum_decl_bundle`

This note records the exact manuscript-facing content those bundles still stand
for, using the current manuscript/PDF labels rather than repo-local shorthand,
so the next elimination pass can replace them with real Lean theorem proofs
rather than further packaging refactors.

## Current Lean Boundary

Files:

- `MaleyLean/Papers/YangMills/Kernel/EndpointManuscriptWitnessDeclarations.lean`
- `MaleyLean/Papers/YangMills/Kernel/ConstructiveManuscriptWitnessDeclarations.lean`
- `MaleyLean/Papers/YangMills/Kernel/VacuumGapManuscriptWitnessDeclarations.lean`

Current localized axiom count:

- endpoint witness bundle: `1`
- constructive witness bundle: `1`
- vacuum-gap witness bundle: `1`
- spine witness/declaration file: `0`

## 1. Endpoint Bundle

Lean axiom:

- `ym_endpoint_decl_bundle : YMEndpointDeclBundle`

Fields still represented:

- `euclidean_dossier_ready`
- `endpoint_packet_ready`
- `hE : euclidean_dossier_ready`
- `hP : endpoint_packet_ready`

Everything else in the file is already derived from those two clauses.

Manuscript source targets:

- `euclidean_dossier_ready`
  - theorem target: `M.1`
  - manuscript meaning:
    from the full sharp-local state `ω^(uren)` together with the Lane A inputs
    `5.74(b)`, `5.76`, `F.247`, and `5.77`, the full sharp-local Schwinger
    family satisfies the Euclidean OS dossier on the full sharp-local algebra:
    Euclidean invariance, bosonic symmetry, reflection positivity,
    temperedness/regularity, and OS reconstruction with dense bounded-base
    algebra
- `dossier_yields_reconstruction`
  - theorem target: `M.3`
  - manuscript meaning:
    the `M.1` Euclidean dossier feeds the standard OS
    reconstruction/analytic-continuation theorem family, yielding the
    reconstructed Wightman fields, Poincare representation with forward cone
    spectrum, locality, and Haag-Kastler net
- `endpoint_packet_ready`
  - theorem target: `O.5`
  - manuscript meaning:
    from `O.3`, `M.4`, `5.76`, and Lemmas `2.5`, `2.6`, the paper fixes the
    exact theorem-level local-net endpoint and separates extended-support sector
    data from the theorem claim
- `endpoint -> exact local net`
  - theorem target: `O.5`, with `O.7` a group-only restatement
- bundled Lean implication:
  - `M.1 -> M.3 -> M.4 -> O.3 -> O.5`

Elimination task:

- replace `ym_endpoint_decl_bundle` by actual Lean theorems/wrappers for:
  - `M.1`
  - `M.3`
  - `O.5`
- then define the bundle by theorem terms, not by axiom.

## 2. Constructive Bundle

Lean axiom:

- `ym_constructive_decl_bundle : YMConstructiveDeclBundle`

Fields still represented:

- `flowed_state_ready`
- `finite_truncation_ready`
- `finite_cap_extension_ready`
- `htrunc : finite_truncation_ready`
- `hext : finite_cap_extension_ready`
- `inductive_union_extends_bounded_base`

Everything else in the file is already collapsed to consequences of finite-cap extension.

Manuscript source targets:

- `flowed_state_ready`
  - theorem target: `4.92`
  - bounded-base export at `4.94`
  - manuscript meaning:
    the no-subsequence convergence / injective tuning / stable-manifold /
    observable Lipschitz package yields the unique flowed continuum state on
    `A_flow`
- `finite_truncation_ready`
  - theorem target: `5.69`
  - closure/remainder package at `5.70`
  - manuscript meaning:
    exact-dimension block machinery plus one-shell transport and
    insertion-control imply basis-independent finite-truncation inverse control
- `finite_cap_extension_ready`
  - theorem target: `5.74`
  - promoted bridge at `5.74A`
  - manuscript meaning:
    `F.330A`, `F.331`, and `5.70` are upgraded by `5.74A` to a unique positive
    unital capwise functional, and `5.74` turns that into the finite-cap
    sharp-local state with capwise OS structure and field realization
- `inductive_union_extends_bounded_base`
  - theorem target: `5.76`
  - manuscript meaning:
    the compatible finite-cap states produced by `5.74` glue to the unique
    inductive-union sharp-local state extending the bounded base state
- compatibility node:
  - theorem target: `5.75`
- bundled Lean implication:
  - `4.92/4.94 -> L.8/L.11 -> 5.39 -> 5.69 -> 5.70 -> F.330A -> F.331 ->
    5.74A -> 5.74 -> 5.75 -> 5.76 -> 5.77`

Elimination task:

- replace `ym_constructive_decl_bundle` by actual Lean theorem/wrapper terms for:
  - `4.92`
  - `5.69`
  - `5.74`
  - `5.76` state-extension consequence
- then define the bundle by those theorem terms.

## 3. Vacuum-Gap Bundle

Lean axiom:

- `ym_vacuum_decl_bundle : YMVacuumDeclBundle`

Fields still represented:

- `ultraviolet_scope_ready`
- `entrance_ready`
- `fixed_lattice_gap_ready`
- `weak_window_certificate_ready`
- `continuum_gap_transport_ready`
- `huv : ultraviolet_scope_ready`
- `hent : entrance_ready`
- `hww : weak_window_certificate_ready`
- `htransport : continuum_gap_transport_ready`
- `hlattice : fixed_lattice_gap_ready`

Everything else in the file is already derived from transport.

Manuscript source targets:

- `ultraviolet_scope_ready`
  - theorem targets: `III.1`, `III.2`
  - manuscript meaning:
    the compact-simple `A1` ultraviolet gate is proved at `III.1` and exported
    to the public Route 1 spine at `III.2`
- `entrance_ready`
  - theorem target: `III.3`
  - manuscript meaning:
    the exact one-shot blocked specification enters the KP/Dobrushin basin at
    bounded physical scale and remains there along the tuned dyadic trajectory
- `fixed_lattice_gap_ready`
  - theorem target: `IV.1`
  - manuscript meaning:
    the full fixed-lattice OS Hamiltonian gap has positive liminf on the tuned
    dyadic trajectory at physical scale
- `weak_window_certificate_ready`
  - theorem targets: `IV.4`, proof-home `F.298`
  - manuscript meaning:
    all live downstream weak-window uses factor only through the repaired
    weak-window package `WWcurv`
- `continuum_gap_transport_ready`
  - theorem target: `F.216`
  - sharp-local continuum gap packaged at `F.5`
- bundled Lean implication:
  - `N.21 -> F.3 -> F.4 -> III.18 -> F.211 -> F.212 -> F.213 -> F.214 ->
    F.216 -> F.5`
  - with `F.298` certifying that only the repaired weak-window package is used
- reconstruction/gap transfer:
  - `F.5 -> M.1 -> M.3 -> M.5`

Elimination task:

- replace `ym_vacuum_decl_bundle` by actual Lean theorem/wrapper terms for:
  - UV/public-scope gate
  - entrance
  - fixed-lattice gap
  - weak-window certificate
  - QE3 transport
- then define the bundle by those theorem terms.

## Immediate Best Order

1. endpoint bundle
2. constructive bundle
3. vacuum-gap bundle

Reason:

- endpoint has the smallest theorem core and the cleanest manuscript anchors;
- constructive is next because the bundle is already very compressed;
- vacuum-gap has the broadest chain and the most section-crossing provenance.

## Honest State

At this point the remaining three witness axioms are not blocked by missing
manuscript mathematics. They are blocked by missing Lean proof terms/wrappers
for the manuscript theorem cores recorded above.
