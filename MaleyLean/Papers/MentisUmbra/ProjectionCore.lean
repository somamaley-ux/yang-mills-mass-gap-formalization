import MaleyLean.Foundation
import MaleyLean.InteriorUniqueness
import MaleyLean.StandingClassifierBridge

namespace MaleyLean

/-- Well-typed single-system transition envelope. -/
abbrev TransitionEnvelope (State : Type) := (State -> State) -> Prop

/-- A mediator compresses a system presentation into a transition-relevant summary. -/
structure TransitionMediator (State Summary : Type) where
  project : State -> Summary

/-- Induced transition family acting on mediator summaries. -/
structure InducedTransitionFamily (State Summary : Type) where
  lift : (State -> State) -> Summary -> State

/-- Transition semantics factor through a mediator when every admitted transition lifts to summary data. -/
def factors_through_mediator
  {State Summary : Type}
  (E : TransitionEnvelope State)
  (M : TransitionMediator State Summary)
  (L : InducedTransitionFamily State Summary) : Prop :=
  forall T : State -> State, E T -> forall s : State, T s = L.lift T (M.project s)

/-- Reference stability under admissible redescription. -/
def invariant_reference_structure
  {State Ref : Type}
  (referenceEq : Ref -> Ref -> Prop)
  (refOf : State -> Ref)
  (admissibleRedescription : (State -> State) -> Prop) : Prop :=
  forall R : State -> State, admissibleRedescription R -> forall s : State,
    referenceEq (refOf (R s)) (refOf s)

/-- Single-system projection package used by the Mentis Umbra formal surface. -/
structure ProjectionStructure
  (State Summary Ref : Type)
  (E : TransitionEnvelope State)
  (admissibleRedescription : (State -> State) -> Prop) where
  mediator : TransitionMediator State Summary
  induced : InducedTransitionFamily State Summary
  referenceEq : Ref -> Ref -> Prop
  refOf : State -> Ref
  factorization : factors_through_mediator E mediator induced
  referenceInvariant :
    invariant_reference_structure referenceEq refOf admissibleRedescription

/-- Agency-structure is just invariant-reference-governed evaluation in this role-based reading. -/
def agency_structure
  {State Summary Ref : Type}
  {E : TransitionEnvelope State}
  {admissibleRedescription : (State -> State) -> Prop}
  (P : ProjectionStructure State Summary Ref E admissibleRedescription) : Prop :=
  invariant_reference_structure P.referenceEq P.refOf admissibleRedescription

/-- Intentional-structure is mediator-governed transition evaluation. -/
def intentional_structure
  {State Summary Ref : Type}
  {E : TransitionEnvelope State}
  {admissibleRedescription : (State -> State) -> Prop}
  (P : ProjectionStructure State Summary Ref E admissibleRedescription) : Prop :=
  factors_through_mediator E P.mediator P.induced

/-- Interior-representation-structure is compressed coordination through the mediator. -/
def interior_representation_structure
  {State Summary Ref : Type}
  {E : TransitionEnvelope State}
  {admissibleRedescription : (State -> State) -> Prop}
  (P : ProjectionStructure State Summary Ref E admissibleRedescription) : Prop :=
  factors_through_mediator E P.mediator P.induced

/-- Package a projection structure from its mediator and invariant-reference components. -/
def single_system_projection_of_components
  {State Summary Ref : Type}
  (E : TransitionEnvelope State)
  (admissibleRedescription : (State -> State) -> Prop)
  (M : TransitionMediator State Summary)
  (L : InducedTransitionFamily State Summary)
  (referenceEq : Ref -> Ref -> Prop)
  (refOf : State -> Ref)
  (h_factorization : factors_through_mediator E M L)
  (h_reference :
    invariant_reference_structure referenceEq refOf admissibleRedescription) :
  ProjectionStructure State Summary Ref E admissibleRedescription := by
  exact
    { mediator := M
      induced := L
      referenceEq := referenceEq
      refOf := refOf
      factorization := h_factorization
      referenceInvariant := h_reference }

/-- The role predicates are immediate once a projection structure is fixed. -/
theorem projection_structure_supports_role_predicates
  {State Summary Ref : Type}
  {E : TransitionEnvelope State}
  {admissibleRedescription : (State -> State) -> Prop}
  (P : ProjectionStructure State Summary Ref E admissibleRedescription) :
  agency_structure P /\
  intentional_structure P /\
  interior_representation_structure P := by
  exact And.intro P.referenceInvariant (And.intro P.factorization P.factorization)

/-- Pure necessity-under-removal logic: if stability implies two components, removing either blocks stability. -/
theorem removal_of_projection_component_breaks_stability
  (stable hasMediator hasInvariantReference : Prop)
  (h_stable_implies_mediator : stable -> hasMediator)
  (h_stable_implies_reference : stable -> hasInvariantReference) :
  (Not hasMediator \/ Not hasInvariantReference) -> Not stable := by
  intro hMissing hStable
  rcases hMissing with hNoMed | hNoRef
  · exact hNoMed (h_stable_implies_mediator hStable)
  · exact hNoRef (h_stable_implies_reference hStable)

/-- Pairwise mediator family for the paper's multi-system global-mediation section. -/
structure PairwiseMediatorFamily (World PairIndex PairSummary : Type) where
  project : PairIndex -> World -> PairSummary

/-- Two global states agree pairwise when every pair-mediator output agrees. -/
def same_pairwise_projection
  {World PairIndex PairSummary : Type}
  (F : PairwiseMediatorFamily World PairIndex PairSummary)
  (x y : World) : Prop :=
  forall i : PairIndex, F.project i x = F.project i y

/-- Joint transitions are pairwise-determinate when pairwise mediator data fixes their outputs. -/
def pairwise_determinate
  {World PairIndex PairSummary : Type}
  (F : PairwiseMediatorFamily World PairIndex PairSummary)
  (E : TransitionEnvelope World) : Prop :=
  forall T : World -> World, E T -> forall x y : World,
    same_pairwise_projection F x y -> T x = T y

/-- Explicit section choosing a representative for projected mediator data. -/
structure PairwiseProjectionSection
  {World PairIndex PairSummary : Type}
  (F : PairwiseMediatorFamily World PairIndex PairSummary) where
  pick : (PairIndex -> PairSummary) -> World
  exact :
    forall w : World,
      same_pairwise_projection F (pick (fun i => F.project i w)) w

/-- Induced transition on product-mediator data via an explicit representative section. -/
def induced_transition_on_product_image
  {World PairIndex PairSummary : Type}
  (F : PairwiseMediatorFamily World PairIndex PairSummary)
  (σ : PairwiseProjectionSection F)
  (T : World -> World) :
  (PairIndex -> PairSummary) -> World :=
  fun v => T (σ.pick v)

/-- Product-mediator factorization from pairwise determinacy. -/
theorem induced_transition_on_product_image_factorizes
  {World PairIndex PairSummary : Type}
  (F : PairwiseMediatorFamily World PairIndex PairSummary)
  (E : TransitionEnvelope World)
  (h_det : pairwise_determinate F E)
  (σ : PairwiseProjectionSection F)
  (T : World -> World)
  (hT : E T) :
  forall w : World,
    T w =
      induced_transition_on_product_image F σ T
        (fun i => F.project i w) := by
  intro w
  dsimp [induced_transition_on_product_image]
  have hsame : same_pairwise_projection F (σ.pick (fun i => F.project i w)) w :=
    σ.exact w
  have hEq : T (σ.pick (fun i => F.project i w)) = T w :=
    h_det T hT (σ.pick (fun i => F.project i w)) w hsame
  exact Eq.symm hEq

/-- Pairwise mediator family equipped with overlap data for compatibility checks. -/
structure OverlapMediatedFamily (World PairIndex PairSummary Overlap : Type) where
  project : PairIndex -> World -> PairSummary
  overlap : PairIndex -> PairSummary -> Overlap

/-- Triple compatibility: all pairwise overlap readings agree on each global state. -/
def triple_compatible
  {World PairIndex PairSummary Overlap : Type}
  (F : OverlapMediatedFamily World PairIndex PairSummary Overlap) : Prop :=
  forall i j k : PairIndex, forall w : World,
    F.overlap i (F.project i w) = F.overlap j (F.project j w) /\
    F.overlap j (F.project j w) = F.overlap k (F.project k w)

/-- Global mediator whose restrictions recover the pairwise family and a shared overlap witness. -/
structure GlobalMediator
  {World PairIndex PairSummary Overlap GlobalSummary : Type}
  (F : OverlapMediatedFamily World PairIndex PairSummary Overlap) where
  project : World -> GlobalSummary
  restrict : PairIndex -> GlobalSummary -> PairSummary
  globalOverlap : GlobalSummary -> Overlap
  agrees : forall i : PairIndex, forall w : World,
    restrict i (project w) = F.project i w
  consistent : forall i : PairIndex, forall g : GlobalSummary,
    F.overlap i (restrict i g) = globalOverlap g

/-- Any global mediator with restriction consistency forces triple compatibility. -/
theorem global_mediator_forces_triple_compatibility
  {World PairIndex PairSummary Overlap GlobalSummary : Type}
  (F : OverlapMediatedFamily World PairIndex PairSummary Overlap)
  (G : GlobalMediator (GlobalSummary := GlobalSummary) F) :
  triple_compatible F := by
  intro i j k w
  constructor
  · calc
      F.overlap i (F.project i w)
          = F.overlap i (G.restrict i (G.project w)) := by rw [G.agrees]
      _ = G.globalOverlap (G.project w) := G.consistent i (G.project w)
      _ = F.overlap j (G.restrict j (G.project w)) := by
            rw [← G.consistent j (G.project w)]
      _ = F.overlap j (F.project j w) := by rw [G.agrees]
  · calc
      F.overlap j (F.project j w)
          = F.overlap j (G.restrict j (G.project w)) := by rw [G.agrees]
      _ = G.globalOverlap (G.project w) := G.consistent j (G.project w)
      _ = F.overlap k (G.restrict k (G.project w)) := by
            rw [← G.consistent k (G.project w)]
      _ = F.overlap k (F.project k w) := by rw [G.agrees]

/-- If triple compatibility fails, no globally consistent mediator can realize the pairwise family. -/
theorem no_global_mediator_without_triple_compatibility
  {World PairIndex PairSummary Overlap GlobalSummary : Type}
  (F : OverlapMediatedFamily World PairIndex PairSummary Overlap)
  (h_not_compatible : Not (triple_compatible F)) :
  Not (exists _ : GlobalMediator (GlobalSummary := GlobalSummary) F, True) := by
  intro hG
  rcases hG with ⟨G, _⟩
  exact h_not_compatible (global_mediator_forces_triple_compatibility F G)

/-- Invariant-reference uniqueness imported from the repo's admissible-interior uniqueness core. -/
theorem invariant_reference_uniqueness
  {α : Type}
  (S : System α)
  (I₁ I₂ : α -> Prop)
  (h₁ : ∀ a, I₁ a -> standing S a)
  (h₂ : ∀ a, I₂ a -> standing S a)
  (h_complete₁ : ∀ a, standing S a -> I₁ a)
  (h_complete₂ : ∀ a, standing S a -> I₂ a) :
  lawfully_equivalent_interiors I₁ I₂ := by
  exact uniqueness_of_admissible_interior S I₁ I₂ h₁ h₂ h_complete₁ h_complete₂

/-- Standing-role collapse imported from the repo's standing-classifier bridge. -/
theorem standing_role_classifier_collapse
  {α : Type}
  (S : System α)
  (QD : α -> Prop)
  (h_toStanding : ∀ a : α, QD a -> standing S a)
  (h_fromStanding : ∀ a : α, standing S a -> QD a) :
  lawfully_equivalent_interiors QD (fun x => standing S x) := by
  exact standing_classifier_lawful_equivalence S QD h_toStanding h_fromStanding

end MaleyLean
