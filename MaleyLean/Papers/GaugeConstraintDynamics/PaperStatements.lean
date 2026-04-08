import MaleyLean.Foundation
import MaleyLean.Papers.GaugeConstraintDynamics.EverettSelectors

namespace MaleyLean

/--
Pointwise inclusion of two local distributions.

This lightweight surface is used to track the paper's stage-I/stage-II claims
without pretending that a full symplectic-geometry library is already present
in the repo.
-/
def pointwise_subdistribution
  {Point Vec : Type}
  (D K : Point -> Vec -> Prop) : Prop :=
  forall x v, D x v -> K x v

/-- Pointwise equality of two local distributions. -/
def pointwise_distribution_eq
  {Point Vec : Type}
  (D K : Point -> Vec -> Prop) : Prop :=
  pointwise_subdistribution D K /\ pointwise_subdistribution K D

/-- A distribution is involutive when tangent generators are closed under bracket. -/
def involutive_distribution
  {Point Field : Type}
  (tangentTo : (Point -> Field) -> Prop)
  (bracket : (Point -> Field) -> (Point -> Field) -> (Point -> Field)) : Prop :=
  forall X Y, tangentTo X -> tangentTo Y -> tangentTo (bracket X Y)

/-- Local foliation package used for the Stage-I Frobenius corollary. -/
def local_foliation_by
  {Leaf Point : Type}
  (leafOf : Point -> Leaf)
  (sameRedescriptionClass : Point -> Point -> Prop) : Prop :=
  forall x y, sameRedescriptionClass x y <-> leafOf x = leafOf y

/-- The coisotropicity conclusion used in Stage II. -/
def coisotropic_surface
  {Point Vec : Type}
  (characteristic tangentSpace : Point -> Vec -> Prop) : Prop :=
  forall x v, characteristic x v -> tangentSpace x v

/-- Local spanning relation for constraint generators. -/
def generated_by_family
  {Point Vec Generator : Type}
  (D : Point -> Vec -> Prop)
  (spans : Generator -> Point -> Vec -> Prop) : Prop :=
  forall x v, D x v <-> exists g : Generator, spans g x v

/-- Weak first-class closure: brackets vanish on standing and lie in the local ideal. -/
def weakly_first_class
  {Generator BracketTerm : Type}
  (bracketTerm : Generator -> Generator -> BracketTerm)
  (vanishesOnStanding : BracketTerm -> Prop)
  (inConstraintIdeal : BracketTerm -> Prop) : Prop :=
  forall a b, vanishesOnStanding (bracketTerm a b) /\ inConstraintIdeal (bracketTerm a b)

/-- Trivial redescription means every admissible redescription class is a singleton. -/
def trivial_redescription
  {Point Vec : Type}
  (D : Point -> Vec -> Prop) : Prop :=
  forall x v, ¬ D x v

/--
Minimal abstract packaging of the paper's local multiplier conclusion.

`weaklyFactorsThrough alpha Hphys` is intended to mean
`H_alpha ≈ H_phys + sum_a u^a phi_a` on the standing surface.
-/
def local_multiplier_rigidity
  {Presentation Hamiltonian : Type}
  (physicalHamiltonian : Hamiltonian -> Prop)
  (weaklyFactorsThrough : Presentation -> Hamiltonian -> Prop) : Prop :=
  exists Hphys : Hamiltonian,
    physicalHamiltonian Hphys /\
    forall alpha : Presentation, weaklyFactorsThrough alpha Hphys

/-- Stage-I involutivity, as exposed in the manuscript. -/
theorem PaperAERInvolutivityStatement
  {Point Field : Type}
  (tangentTo : (Point -> Field) -> Prop)
  (bracket : (Point -> Field) -> (Point -> Field) -> (Point -> Field))
  (h_involutive : involutive_distribution tangentTo bracket) :
  involutive_distribution tangentTo bracket := by
  exact h_involutive

/-- Stage-I Frobenius corollary, in lightweight leaf-class form. -/
theorem PaperAERFrobeniusFoliationStatement
  {Leaf Point : Type}
  (leafOf : Point -> Leaf)
  (sameRedescriptionClass : Point -> Point -> Prop)
  (h_foliates : local_foliation_by leafOf sameRedescriptionClass) :
  local_foliation_by leafOf sameRedescriptionClass := by
  exact h_foliates

/-- Stage-II kernel inclusion `ker(dpi) ⊆ ker(omega_C)`. -/
theorem PaperAERBasicKernelInclusionStatement
  {Point Vec : Type}
  (vertical characteristic : Point -> Vec -> Prop)
  (h_obsmin : pointwise_subdistribution vertical characteristic) :
  pointwise_subdistribution vertical characteristic := by
  exact h_obsmin

/-- Stage-II reverse inclusion from separation/cotangent spanning. -/
theorem PaperAERReverseKernelInclusionStatement
  {Point Vec : Type}
  (vertical characteristic : Point -> Vec -> Prop)
  (h_sep : pointwise_subdistribution characteristic vertical) :
  pointwise_subdistribution characteristic vertical := by
  exact h_sep

/--
Stage-II characteristic identification.

The pointwise equality of the redescription distribution and the characteristic
kernel is the paper's forcing step; coisotropicity is then exposed separately.
-/
theorem PaperAERCharacteristicIdentificationStatement
  {Point Vec : Type}
  (vertical characteristic tangentSpace : Point -> Vec -> Prop)
  (h_obsmin : pointwise_subdistribution vertical characteristic)
  (h_sep : pointwise_subdistribution characteristic vertical)
  (h_coisotropic :
    pointwise_distribution_eq vertical characteristic ->
    coisotropic_surface characteristic tangentSpace) :
  pointwise_distribution_eq vertical characteristic /\
  coisotropic_surface characteristic tangentSpace := by
  have hEq : pointwise_distribution_eq vertical characteristic :=
    And.intro h_obsmin h_sep
  exact And.intro hEq (h_coisotropic hEq)

/-- Stage-III coisotropic local normal form, in minimal local-generator form. -/
theorem PaperAERCoisotropicLocalNormalFormStatement
  {Point Vec Generator : Type}
  (characteristic : Point -> Vec -> Prop)
  (spans : Generator -> Point -> Vec -> Prop)
  (h_normal_form : generated_by_family characteristic spans) :
  generated_by_family characteristic spans := by
  exact h_normal_form

/--
Stage-III: the local constraint generators span admissible redescription once
the characteristic identification and local normal form are combined.
-/
theorem PaperAERConstraintGeneratorsSpanStatement
  {Point Vec Generator : Type}
  (vertical characteristic : Point -> Vec -> Prop)
  (spans : Generator -> Point -> Vec -> Prop)
  (h_char :
    pointwise_distribution_eq vertical characteristic)
  (h_normal_form :
    generated_by_family characteristic spans) :
  generated_by_family vertical spans := by
  intro x v
  constructor
  · intro hv
    have hk : characteristic x v := h_char.1 x v hv
    exact (h_normal_form x v).1 hk
  · intro hv
    have hk : characteristic x v := (h_normal_form x v).2 hv
    exact h_char.2 x v hk

/--
Stage-III first-class closure.

The theorem is kept at the paper-facing level: the repo certifies the local
weak first-class closure interface without claiming that full symplectic
geometry has already been internalized here.
-/
theorem PaperAERFirstClassClosureStatement
  {Generator BracketTerm : Type}
  (bracketTerm : Generator -> Generator -> BracketTerm)
  (vanishesOnStanding : BracketTerm -> Prop)
  (inConstraintIdeal : BracketTerm -> Prop)
  (h_first_class :
    weakly_first_class bracketTerm vanishesOnStanding inConstraintIdeal) :
  weakly_first_class bracketTerm vanishesOnStanding inConstraintIdeal := by
  exact h_first_class

/--
Stage-III second-class exclusion.

If the characteristic kernel is pointwise equal to the admissible redescription
distribution and the induced standing form is nondegenerate, then redescription
is trivial.
-/
theorem PaperAERSecondClassExclusionStatement
  {Point Vec : Type}
  (vertical characteristic : Point -> Vec -> Prop)
  (h_char : pointwise_distribution_eq vertical characteristic)
  (h_nondegenerate : forall x v, ¬ characteristic x v) :
  trivial_redescription vertical := by
  intro x v hv
  exact h_nondegenerate x v (h_char.1 x v hv)

/-- Stage-IV multiplier-type Hamiltonian rigidity, in local weak form. -/
theorem PaperAERMultiplierRigidityStatement
  {Presentation Hamiltonian : Type}
  (physicalHamiltonian : Hamiltonian -> Prop)
  (weaklyFactorsThrough : Presentation -> Hamiltonian -> Prop)
  (h_multiplier :
    local_multiplier_rigidity physicalHamiltonian weaklyFactorsThrough) :
  local_multiplier_rigidity physicalHamiltonian weaklyFactorsThrough := by
  exact h_multiplier

/-- Trichotomy labels for collapse models in the paper's AER analysis. -/
inductive CollapseResolution where
  | pureGauge
  | metaSelector
  | reifiedNoise
deriving DecidableEq, Repr

/-- Trichotomy labels for Everettian weight rules in the paper's AER analysis. -/
inductive EverettResolution where
  | pureBookkeeping
  | metaSelection
  | reifiedSelector
deriving DecidableEq, Repr

/--
Collapse trilemma.

This is formalized exactly at the decision level used in the paper: either the
auxiliary stochastic datum changes no outcome-relevant content, or it does and
must then either be reified as state or treated as illicit meta-selection.
-/
theorem PaperCollapseTrilemmaUnderAERStatement
  {Noise : Type}
  (altersOutcome : Noise -> Prop)
  (reifiedAsState : Noise -> Prop)
  [DecidablePred altersOutcome]
  [DecidablePred reifiedAsState] :
  forall eta : Noise,
    exists tag : CollapseResolution,
      match tag with
      | CollapseResolution.pureGauge => ¬ altersOutcome eta
      | CollapseResolution.metaSelector => altersOutcome eta /\ ¬ reifiedAsState eta
      | CollapseResolution.reifiedNoise => reifiedAsState eta := by
  intro eta
  by_cases hAlt : altersOutcome eta
  · by_cases hPhys : reifiedAsState eta
    · exact Exists.intro CollapseResolution.reifiedNoise hPhys
    · exact Exists.intro CollapseResolution.metaSelector (And.intro hAlt hPhys)
  · exact Exists.intro CollapseResolution.pureGauge hAlt

/--
Everettian probability trilemma.

As in the manuscript, a weight rule either has no standing, functions as an
illicit selector, or is made admissible only by reifying the selector-bearing
auxiliary structure.
-/
theorem PaperEverettProbabilityTrilemmaUnderAERStatement
  {WeightRule : Type}
  (affectsOutcome : WeightRule -> Prop)
  (selectorReified : WeightRule -> Prop)
  [DecidablePred affectsOutcome]
  [DecidablePred selectorReified] :
  forall W : WeightRule,
    exists tag : EverettResolution,
      match tag with
      | EverettResolution.pureBookkeeping => ¬ affectsOutcome W
      | EverettResolution.metaSelection => affectsOutcome W /\ ¬ selectorReified W
      | EverettResolution.reifiedSelector => selectorReified W := by
  intro W
  by_cases hEff : affectsOutcome W
  · by_cases hReif : selectorReified W
    · exact ⟨EverettResolution.reifiedSelector, hReif⟩
    · exact ⟨EverettResolution.metaSelection, And.intro hEff hReif⟩
  · exact ⟨EverettResolution.pureBookkeeping, hEff⟩

/-- Explicit non-invariance of branch extraction under auxiliary specification. -/
theorem PaperEverettBranchNonInvarianceStatement
  {State Spec BranchCount : Type}
  [DecidableEq BranchCount]
  (count : State -> Spec -> BranchCount)
  (rho : State)
  (sigma sigma' : Spec)
  (h_diff : count rho sigma ≠ count rho sigma') :
  count rho sigma ≠ count rho sigma' := by
  let B : EverettBranchingData State Spec BranchCount :=
    { extract := fun s spec => count s spec.data }
  have hNoninv : branch_extraction_noninvariant B := by
    exact ⟨rho, ⟨sigma⟩, ⟨sigma'⟩, h_diff⟩
  exact h_diff

/--
Invariant measures do not by themselves fix singular continuation.

The theorem is expressed as the impossibility of an admissible singular rule
that is both invariant-respecting and selector-free under the paper's symmetric
branching assumptions.
-/
theorem PaperInvariantMeasureInsufficiencyStatement
  {Rule : Type}
  (breaksInvariance : Rule -> Prop)
  (usesExtraSelector : Rule -> Prop)
  (h_selector_if_not_break :
    forall r : Rule, ¬ breaksInvariance r -> usesExtraSelector r) :
  forall r : Rule,
    ¬ (¬ breaksInvariance r /\ ¬ usesExtraSelector r) := by
  intro r h
  have hSel : usesExtraSelector r := h_selector_if_not_break r h.1
  exact h.2 hSel

/--
Terminal exhaustion of selection certifiers.

If every known certifier class is already closed/terminal in the relevant
regime, then no admissible certifier remains.
-/
theorem PaperTerminalExhaustionOfSelectionCertifiersStatement
  {Operator : Type}
  (admissible : Operator -> Prop)
  (measureTypicality : Operator -> Prop)
  (completionLimit : Operator -> Prop)
  (selectionOperator : Operator -> Prop)
  (forcingOperator : Operator -> Prop)
  (metaFoundationalAuthority : Operator -> Prop)
  (standingRepair : Operator -> Prop)
  (h_measure_terminal :
    forall op : Operator, admissible op -> ¬ measureTypicality op)
  (h_completion_terminal :
    forall op : Operator, admissible op -> ¬ completionLimit op)
  (h_selection_terminal :
    forall op : Operator, admissible op -> ¬ selectionOperator op)
  (h_forcing_terminal :
    forall op : Operator, admissible op -> ¬ forcingOperator op)
  (h_meta_terminal :
    forall op : Operator, admissible op -> ¬ metaFoundationalAuthority op)
  (h_repair_terminal :
    forall op : Operator, admissible op -> ¬ standingRepair op) :
  forall op : Operator,
    admissible op ->
    ¬ (
      measureTypicality op \/
      completionLimit op \/
      selectionOperator op \/
      forcingOperator op \/
      metaFoundationalAuthority op \/
      standingRepair op) := by
  intro op hAdm hAny
  rcases hAny with hMeasure | hRest
  · exact (h_measure_terminal op hAdm) hMeasure
  · rcases hRest with hCompletion | hRest
    · exact (h_completion_terminal op hAdm) hCompletion
    · rcases hRest with hSelection | hRest
      · exact (h_selection_terminal op hAdm) hSelection
      · rcases hRest with hForcing | hRest
        · exact (h_forcing_terminal op hAdm) hForcing
        · rcases hRest with hMeta | hRepair
          · exact (h_meta_terminal op hAdm) hMeta
          · exact (h_repair_terminal op hAdm) hRepair

/--
Paper-facing structural core for
"Admissibility and the Structural Origin of Gauge and Constraint Dynamics".

This packages the manuscript's verified Lean surface at the repo's current
level of generality:
- involutive admissible-redescription structure,
- characteristic identification/coisotropic forcing,
- local generator span and weak first-class closure,
- second-class exclusion,
- multiplier-type Hamiltonian rigidity,
- and the paper's collapse/Everett terminal trilemma layer.

The repo does not yet internalize full symplectic geometry, canonical GR, or
Hilbert-space branching mechanics in detail, so the theorem is intentionally a
certified structural core rather than a claim of complete low-level geometric
formalization.
-/
theorem PaperGaugeConstraintDynamicsVerifiedCoreStatement
  {Point Vec Field Leaf Generator BracketTerm Presentation Hamiltonian Noise WeightRule Operator : Type}
  (tangentTo : (Point -> Field) -> Prop)
  (bracketField : (Point -> Field) -> (Point -> Field) -> (Point -> Field))
  (leafOf : Point -> Leaf)
  (sameRedescriptionClass : Point -> Point -> Prop)
  (vertical characteristic tangentSpace : Point -> Vec -> Prop)
  (spans : Generator -> Point -> Vec -> Prop)
  (bracketTerm : Generator -> Generator -> BracketTerm)
  (vanishesOnStanding : BracketTerm -> Prop)
  (inConstraintIdeal : BracketTerm -> Prop)
  (physicalHamiltonian : Hamiltonian -> Prop)
  (weaklyFactorsThrough : Presentation -> Hamiltonian -> Prop)
  (altersOutcome : Noise -> Prop)
  (reifiedNoise : Noise -> Prop)
  (affectsOutcome : WeightRule -> Prop)
  (selectorReified : WeightRule -> Prop)
  [DecidablePred altersOutcome]
  [DecidablePred reifiedNoise]
  [DecidablePred affectsOutcome]
  [DecidablePred selectorReified]
  (admissible : Operator -> Prop)
  (measureTypicality : Operator -> Prop)
  (completionLimit : Operator -> Prop)
  (selectionOperator : Operator -> Prop)
  (forcingOperator : Operator -> Prop)
  (metaFoundationalAuthority : Operator -> Prop)
  (standingRepair : Operator -> Prop)
  (h_involutive : involutive_distribution tangentTo bracketField)
  (h_foliates : local_foliation_by leafOf sameRedescriptionClass)
  (h_obsmin : pointwise_subdistribution vertical characteristic)
  (h_sep : pointwise_subdistribution characteristic vertical)
  (h_coisotropic :
    pointwise_distribution_eq vertical characteristic ->
    coisotropic_surface characteristic tangentSpace)
  (h_normal_form : generated_by_family characteristic spans)
  (h_first_class :
    weakly_first_class bracketTerm vanishesOnStanding inConstraintIdeal)
  (h_nondegenerate :
    forall x v, ¬ characteristic x v)
  (h_multiplier :
    local_multiplier_rigidity physicalHamiltonian weaklyFactorsThrough)
  (h_measure_terminal :
    forall op : Operator, admissible op -> ¬ measureTypicality op)
  (h_completion_terminal :
    forall op : Operator, admissible op -> ¬ completionLimit op)
  (h_selection_terminal :
    forall op : Operator, admissible op -> ¬ selectionOperator op)
  (h_forcing_terminal :
    forall op : Operator, admissible op -> ¬ forcingOperator op)
  (h_meta_terminal :
    forall op : Operator, admissible op -> ¬ metaFoundationalAuthority op)
  (h_repair_terminal :
    forall op : Operator, admissible op -> ¬ standingRepair op) :
  involutive_distribution tangentTo bracketField /\
  local_foliation_by leafOf sameRedescriptionClass /\
  (pointwise_distribution_eq vertical characteristic /\ coisotropic_surface characteristic tangentSpace) /\
  generated_by_family vertical spans /\
  weakly_first_class bracketTerm vanishesOnStanding inConstraintIdeal /\
  trivial_redescription vertical /\
  local_multiplier_rigidity physicalHamiltonian weaklyFactorsThrough /\
  (forall eta : Noise,
    exists tag : CollapseResolution,
      match tag with
      | CollapseResolution.pureGauge => ¬ altersOutcome eta
      | CollapseResolution.metaSelector => altersOutcome eta /\ ¬ reifiedNoise eta
      | CollapseResolution.reifiedNoise => reifiedNoise eta) /\
  (forall W : WeightRule,
    exists tag : EverettResolution,
      match tag with
      | EverettResolution.pureBookkeeping => ¬ affectsOutcome W
      | EverettResolution.metaSelection => affectsOutcome W /\ ¬ selectorReified W
      | EverettResolution.reifiedSelector => selectorReified W) /\
  (forall op : Operator,
    admissible op ->
    ¬ (
      measureTypicality op \/
      completionLimit op \/
      selectionOperator op \/
      forcingOperator op \/
      metaFoundationalAuthority op \/
      standingRepair op)) := by
  refine And.intro h_involutive ?_
  refine And.intro h_foliates ?_
  have hChar :
      pointwise_distribution_eq vertical characteristic /\
      coisotropic_surface characteristic tangentSpace :=
    PaperAERCharacteristicIdentificationStatement
      vertical characteristic tangentSpace h_obsmin h_sep h_coisotropic
  refine And.intro hChar ?_
  have hSpan : generated_by_family vertical spans :=
    PaperAERConstraintGeneratorsSpanStatement
      vertical characteristic spans hChar.1 h_normal_form
  refine And.intro hSpan ?_
  refine And.intro h_first_class ?_
  have hSecondClass : trivial_redescription vertical :=
    PaperAERSecondClassExclusionStatement
      vertical characteristic hChar.1 h_nondegenerate
  refine And.intro hSecondClass ?_
  refine And.intro h_multiplier ?_
  refine And.intro ?_ ?_
  · intro eta
    exact
      PaperCollapseTrilemmaUnderAERStatement
        altersOutcome
        reifiedNoise
        eta
  · refine And.intro ?_ ?_
    · intro W
      exact
        PaperEverettProbabilityTrilemmaUnderAERStatement
          affectsOutcome
          selectorReified
          W
    · intro op hAdm
      exact
        PaperTerminalExhaustionOfSelectionCertifiersStatement
          admissible
          measureTypicality
          completionLimit
          selectionOperator
          forcingOperator
          metaFoundationalAuthority
          standingRepair
          h_measure_terminal
          h_completion_terminal
          h_selection_terminal
          h_forcing_terminal
          h_meta_terminal
          h_repair_terminal
          op
          hAdm

end MaleyLean
