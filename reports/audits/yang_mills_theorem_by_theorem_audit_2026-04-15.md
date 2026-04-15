# Yang-Mills Theorem-by-Theorem Audit

Date: 2026-04-15

## Scope

This audit is submission-facing.

Its purpose is to compare:

- the current four-file Yang-Mills manuscript corpus,
- the theorem-label and companion crosswalk registered in Lean,
- the closed manuscript-instantiation layer now present in the repo,
- and the remaining distance to a deeper native formalization of the actual
  mathematical content.

The manuscript corpus checked for this audit is:

- `Vacuum_sector_mass_gap_for_the_local_gauge_invariant_sharp_local_Yang_Mills_net.pdf`
- `Companion_I__Ultraviolet_Gate_and_Route_1_Mass_Gap_Chain.pdf`
- `Companion_II__Lane_A_Sharp_Local_Construction.pdf`
- `Companion_III__Reconstruction__Non_Triviality__and_Faithful_Wilson_Universality.pdf`

## Executive Verdict

The manuscript theorem inventory is now fully represented at the theorem-label
and closed-manuscript-instantiation level.

In particular:

- all 41 registered primary theorem/source labels used by the current Lean
  crosswalk were found across the four PDFs,
- the companion-local crosswalk rows match the source-label register,
- the repo contains a closed manuscript instantiation constant
  `I : YMClosedInstantiatedManuscript`,
- and the manuscript-completion proposition
  `ym_closed_manuscript_completion` is realized.

So the remaining work is no longer:

- theorem inventory discovery,
- manuscript/Lean correspondence discovery,
- or manuscript-instantiation closure.

The remaining work is deeper native formalization of the theorem content
internal to the route/core objects, especially along the mass-gap chain.

## Corpus Check

PDF extraction was used to scan the four manuscript files for the theorem labels
used by the Lean source crosswalk.

Result:

- 41 of 41 registered primary labels were found across the manuscript corpus.
- No registered primary labels were missing.

The matched label set is:

- `N.20`, `N.21`
- `F.3`, `F.317`, `F.318`, `F.4`, `F.298`, `F.308`
- `4.92`, `4.93`, `4.94`
- `L.8`, `L.11`
- `5.39`, `5.69`, `5.74A`, `5.74`, `5.75`, `5.76`, `5.77`
- `F.211`, `F.212`, `F.213`, `F.214`, `F.216`, `F.245`, `F.330A`, `F.331`,
  `F.5`
- `III.18`
- `M.1`, `M.2`, `M.3`, `M.4`, `M.5`, `M.6`
- `O.2`, `O.3`, `O.4`, `O.5`, `O.7`

This agrees with:

- `MaleyLean/Papers/YangMills/SourceCrosswalk/Register.lean`
- `MaleyLean/Papers/YangMills/SourceCrosswalk/CompanionTables.lean`

## Direct Manuscript Evidence

The main PDF explicitly presents the theorem packets in the same public order
used by the Lean crosswalk:

- Packet 1: `N.20`, `N.21`
- Packet 2: `F.3`, `F.317`, `F.318`
- Packet 3: `F.4`, `F.308`
- Packet 4-7 / Lane A: `4.92`, `4.93`, `4.94`, `5.39`, `5.69`, `F.245`,
  `F.330A`, `F.331`, `5.74A`, `5.74`, `5.75`, `5.76`, `5.77`
- Packet 8 / QE3 transport: `III.18`, `F.211`, `F.212`, `F.213`, `F.214`,
  `F.216`, `F.5`
- Packet 9: `M.1`, `M.2`, `M.3`, `M.4`, `M.5`, `M.6`
- Packet 10: `O.2`, `O.3`, `O.4`, `O.5`, `O.7`

Representative extraction snippets from the PDFs align with the current Lean
reading:

- `F.216` is described in the main paper as the unique transport node carrying
  the tuned fixed-lattice lower bound to the continuum sharp-local Hilbert
  space.
- `M.3` appears in the main paper packet docket as the OS/Wightman
  reconstruction step.
- `O.5` appears in the main paper packet docket as the exact theorem-level
  local-net endpoint.
- Companion I describes `III.18` as the Wilson-to-patched return used on the
  public Route 1 spine, then `F.216` as the continuum gap transfer, and `F.5`
  as the resulting continuum vacuum-gap corollary.
- Companion II separates `5.74A`, `5.74`, `5.75`, `5.76`, `5.77` as distinct
  finite-cap bridge, finite-cap OS, compatibility, inductive-union, and
  bounded-base cyclicity steps.
- Companion III presents `M.3`, `M.5`, `M.6`, `O.3`, and `O.5` as the
  reconstruction, Minkowski-gap transfer, non-triviality, universality, and
  exact-endpoint chain.

## Lean Coverage Already Achieved

### 1. Inventory and Crosswalk

The theorem inventory, ownership, packet map, and source labels are already
registered and axiom-free at the manuscript-facing level.

Primary files:

- `MaleyLean/Papers/YangMills/Verbatim/TheoremRegister.lean`
- `MaleyLean/Papers/YangMills/SourceCrosswalk/Register.lean`
- `MaleyLean/Papers/YangMills/SourceCrosswalk/CompanionTables.lean`
- `MaleyLean/Papers/YangMills/Kernel/NamedCompanionTheoremReflection.lean`

### 2. Closed Manuscript Instantiation

The formerly reported manuscript-instantiation gap is closed in the current
checkout.

Primary files:

- `MaleyLean/Papers/YangMills/Kernel/ManuscriptObjectPackageDeclarations.lean`
- `MaleyLean/Papers/YangMills/Kernel/ClosedInstantiatedManuscript.lean`
- `MaleyLean/Papers/YangMills/Kernel/ClosedManuscriptCompletionCriterion.lean`

Key realized objects:

- `noncomputable def I : YMClosedInstantiatedManuscript`
- `theorem ym_closed_manuscript_completion_realized :
  ym_closed_manuscript_completion`

### 3. Closed Theorem Reflection

Given the closed manuscript object, the current Lean layer exports the full
current reflection theorem surface for the registered manuscript content.

Primary file:

- `MaleyLean/Papers/YangMills/Kernel/ClosedInstantiatedManuscript.lean`

## Where The Current Formalization Is Still Shallow

The remaining depth issue is visible in the core route definitions.

### Constructive route

`MaleyLean/Papers/YangMills/Kernel/ConstructiveCore.lean`

The constructive route already carries named package fields and derivation maps,
but its proof burden is still organized around readiness propositions such as:

- `flowed_state_ready`
- `finite_truncation_ready`
- `finite_cap_extension_ready`
- `cyclicity_ready`
- `finite_cap_bridge_ready`
- `bounded_state_compatibility_ready`
- `inductive_union_ready`

These are enough for theorem-interface reflection, but they do not yet natively
reconstruct the underlying analytic arguments.

### Vacuum-gap route

`MaleyLean/Papers/YangMills/Kernel/VacuumGapCore.lean`

This is the highest-priority deepening target for a Millennium-level claim.

The route already exposes the mass-gap path as:

- UV/public-scope gate
- entrance
- fixed-lattice gap
- weak-window certificate
- continuum gap transport
- reconstruction
- endpoint

and exports the explicit theorem-facing statement:

- transport readiness
- OS transport
- positive gap
- lattice-gap input
- reconstruction readiness
- OS sector readiness
- Minkowski-gap readiness
- transport origin

But the core still packages those steps through route-level readiness props and
bundle fields rather than a native internal development of the transported gap
argument.

### Endpoint route

`MaleyLean/Papers/YangMills/Kernel/EndpointCore.lean`

The endpoint side is structurally strong, but reconstruction, field
correspondence, vacuum-correlation, non-triviality, and faithful universality
still appear at the route/core interface level rather than as a deeper native
chain of theorem objects and intermediate lemmas.

## Highest-Value Native Deepening Order

### Priority 1. Vacuum-gap / mass-gap chain

Target labels:

- `F.298`
- `III.18`
- `F.211`
- `F.212`
- `F.213`
- `F.214`
- `F.216`
- `F.5`
- `M.5`

Target goal:

- replace more of the route-level readiness interface with native internal
  theorem data and intermediate lemmas showing how QE3 transport yields the
  positive gap and how that gap is transferred into the reconstructed
  Minkowski-side object.

### Priority 2. Endpoint reconstruction and universality

Target labels:

- `M.1`
- `M.3`
- `M.4`
- `M.6`
- `O.2`
- `O.3`
- `O.4`
- `O.5`

Target goal:

- strengthen the endpoint dossier and reconstruction package from an interface
  layer into a richer theorem layer where Wightman reconstruction,
  field-correspondence, non-triviality, universality, and exact-endpoint
  outputs have more internal native proof structure.

### Priority 3. Constructive Lane A internals

Target labels:

- `4.92`
- `4.94`
- `L.8`
- `L.11`
- `5.39`
- `5.69`
- `F.245`
- `F.330A`
- `F.331`
- `5.74A`
- `5.74`
- `5.75`
- `5.76`
- `5.77`

Target goal:

- convert more of the finite-cap and sharp-local pipeline from readiness props
  into explicit intermediate theorem objects and compatibility lemmas, so the
  Lane A chain is less “interface-certified” and more “internally derived.”

## Immediate Engineering Recommendation

If the aim is the highest possible standard, the next formalization sprint
should begin with the vacuum-gap chain.

Reason:

- it is closest to the mass-gap claim,
- it is currently the most important remaining interface-heavy layer,
- and it is the bridge between the Route 1 transport story and the endpoint
  reconstruction story.

Concretely, the next work package should introduce one deeper native layer
between:

- `YMVacuumGapRoute`

and

- the current theorem-facing consequences exported in
  `MaleyLean/Papers/YangMills/Kernel/VacuumGapCore.lean`,
  `VacuumGapSemanticBundle.lean`,
  and `VacuumGapTransportRealizeLawPackage.lean`.

That package should aim to expose:

- a more explicit transported-gap theorem object for `F.216`,
- a more explicit sharp-local gap theorem object for `F.5`,
- a more explicit reconstruction-gap transfer theorem object for `M.5`,
- and native compatibility lemmas tying them together.

## Bottom Line

The manuscript correspondence layer is now in excellent shape:

- theorem labels match the PDFs,
- the crosswalk matches the companion structure,
- the manuscript constant is closed,
- and the current reflection boundary is mechanically realized.

The remaining distance to the highest standard is no longer administrative or
architectural.

It is native mathematical deepening inside the route objects, with the
vacuum-gap / mass-gap path as the most important next target.
