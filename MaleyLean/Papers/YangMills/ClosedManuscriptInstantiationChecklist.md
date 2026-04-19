# Yang-Mills Closed Manuscript Instantiation Checklist

Last updated: 2026-04-15

## Purpose

This note records the closed manuscript-instantiation boundary for the current
Yang-Mills theorem development.

The repository now contains:

- a direct flat manuscript theorem surface,
- a single-object `YMFormalizedManuscript` layer,
- chosen constructive / vacuum-gap / endpoint / spine object records,
- and a `YMClosedManuscriptBlueprint` layer proving that any one closed
  blueprint yields the full current reflection theorem.

What used to be missing has now been supplied at the instantiated-manuscript
level:

- `noncomputable def I : YMClosedInstantiatedManuscript`
  in `MaleyLean/Papers/YangMills/Kernel/ManuscriptObjectPackageDeclarations.lean`

This file now records what that closed object packages structurally.

That closure step should not be confused with residual axiom support: the
current manuscript-facing Yang-Mills surface reported by the repo audits is
already axiom-free, and the repo now also contains a closed distinguished
manuscript instance of the already-formalized route objects.

For a fillable author-facing version keyed to the paper/source labels, see:

- [ClosedManuscriptAuthorWorksheet.md](/d:/lean/MaleyLean/MaleyLean/Papers/YangMills/ClosedManuscriptAuthorWorksheet.md)

## What Already Exists

The current Lean development already formalizes the following object layers:

- `MaleyLean/Papers/YangMills/Kernel/FormalizedManuscriptReflection.lean`
- `MaleyLean/Papers/YangMills/Kernel/ChosenManuscriptObjects.lean`
- `MaleyLean/Papers/YangMills/Kernel/ClosedManuscriptBlueprint.lean`

These establish:

- the theorem-facing reflection theorem over one formal manuscript object,
- the chosen constructive / vacuum-gap / endpoint / spine objects associated to
  that manuscript object,
- and the exact blueprint shape for a future closed constant.

## Closed Constant Structure

The instantiated manuscript object is assembled from two parts.

### 1. Concrete manuscript objects

The constant must provide one:

- `S : YMLoadBearingSpine`
- `RC : YMConstructiveRoute`
- `RD : YMVacuumGapRoute`
- `RE : YMEndpointCore`

This is the `YMManuscriptConcreteObjects` layer in:

- `MaleyLean/Papers/YangMills/Kernel/ClosedManuscriptBlueprint.lean`

### 2. Readiness witnesses

Given those objects, the constant must also provide:

- `hp1 : S.packet1_uv_gate`
- `hp2 : S.packet2_entrance`
- `hAroute : ym_public_scope_route S`
- `htrunc : RC.finite_truncation_ready`
- `hext : RC.finite_cap_extension_ready`
- `hcompat : RC.bounded_state_compatibility_ready`
- `hunion : RC.inductive_union_ready`
- `hww : RD.weak_window_certificate_ready`
- `hE : RE.euclidean_dossier_ready`
- `hP : RE.endpoint_packet_ready`

This is the `YMManuscriptReadinessWitnesses` layer in:

- `MaleyLean/Papers/YangMills/Kernel/ClosedManuscriptBlueprint.lean`

## Why The Existing Constant Maps Are Not Enough

The current kernel does contain constant witness-producing maps, for example:

- `bounded_base_from_assembly` in
  `MaleyLean/Papers/YangMills/Kernel/ConstructiveExtendAssembleLawPackage.lean`
- `exact_endpoint_from_correlations` in
  `MaleyLean/Papers/YangMills/Kernel/EndpointCorrelationLawPackage.lean`

Those maps help explain current witness propagation, but they do **not**
provide the final closed manuscript constant by themselves.

Why:

- they live inside already-parameterized route/package objects,
- they do not define one global `YMLoadBearingSpine`,
- they do not define one global `YMConstructiveRoute`,
- they do not define one global `YMVacuumGapRoute`,
- they do not define one global `YMEndpointCore`,
- and they do not package the required readiness witnesses into one closed
  blueprint.

So they reduce some internal variability, but they do not close the final
object-level instantiation step.

## Best Current Honest Status

The repo is now extremely close to a full mechanically proven reflection of the
paper.

What remains is no longer theorem packaging or theorem meaning.

It is also no longer witness-bundle axiom elimination.

That object-level instantiation step is now realized through the manuscript
object package declarations. As a result, the current Lean development already
recovers:

- the formalized manuscript object,
- the chosen manuscript objects,
- and the flat manuscript-granular reflection theorem.
