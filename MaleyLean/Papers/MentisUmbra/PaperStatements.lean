import MaleyLean.Papers.MentisUmbra.ProjectionCore

namespace MaleyLean

/-- Single-system projection necessity, in the paper-facing mediator/reference form. -/
def PaperMentisUmbraSingleSystemProjectionNecessityStatement
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
    single_system_projection_of_components
      E
      admissibleRedescription
      M
      L
      referenceEq
      refOf
      h_factorization
      h_reference

/-- Necessity-under-removal for the single-system projection package. -/
theorem PaperMentisUmbraNecessityUnderRemovalStatement
  (stable hasMediator hasInvariantReference : Prop)
  (h_stable_implies_mediator : stable -> hasMediator)
  (h_stable_implies_reference : stable -> hasInvariantReference) :
  (Not hasMediator \/ Not hasInvariantReference) -> Not stable := by
  exact
    removal_of_projection_component_breaks_stability
      stable
      hasMediator
      hasInvariantReference
      h_stable_implies_mediator
      h_stable_implies_reference

/-- Role-based classification: agency, intentionality, and interiority are role names on the same projection package. -/
theorem PaperMentisUmbraRoleClassificationStatement
  {State Summary Ref : Type}
  {E : TransitionEnvelope State}
  {admissibleRedescription : (State -> State) -> Prop}
  (P : ProjectionStructure State Summary Ref E admissibleRedescription) :
  agency_structure P /\
  intentional_structure P /\
  interior_representation_structure P := by
  exact projection_structure_supports_role_predicates P

/-- Invariant reference uniqueness, using the repo's admissible-interior uniqueness core. -/
theorem PaperMentisUmbraInvariantReferenceUniquenessStatement
  {α : Type}
  (S : System α)
  (I₁ I₂ : α -> Prop)
  (h₁ : ∀ a, I₁ a -> standing S a)
  (h₂ : ∀ a, I₂ a -> standing S a)
  (h_complete₁ : ∀ a, standing S a -> I₁ a)
  (h_complete₂ : ∀ a, standing S a -> I₂ a) :
  lawfully_equivalent_interiors I₁ I₂ := by
  exact invariant_reference_uniqueness S I₁ I₂ h₁ h₂ h_complete₁ h_complete₂

/-- Standing-role collapse for derived role classifiers. -/
theorem PaperMentisUmbraRoleClassifierCollapseStatement
  {α : Type}
  (S : System α)
  (QD : α -> Prop)
  (h_toStanding : ∀ a : α, QD a -> standing S a)
  (h_fromStanding : ∀ a : α, standing S a -> QD a) :
  lawfully_equivalent_interiors QD (fun x => standing S x) := by
  exact standing_role_classifier_collapse S QD h_toStanding h_fromStanding

/-- Two-system interaction projection necessity, as a packaged existence statement. -/
theorem PaperMentisUmbraInteractionProjectionNecessityStatement
  {State1 Summary1 Ref1 State2 Summary2 Ref2 JointSummary JointRef : Type}
  (E1 : TransitionEnvelope State1)
  (R1 : (State1 -> State1) -> Prop)
  (E2 : TransitionEnvelope State2)
  (R2 : (State2 -> State2) -> Prop)
  (E12 : TransitionEnvelope (State1 × State2))
  (R12 : ((State1 × State2) -> (State1 × State2)) -> Prop)
  (P1 : ProjectionStructure State1 Summary1 Ref1 E1 R1)
  (P2 : ProjectionStructure State2 Summary2 Ref2 E2 R2)
  (P12 : ProjectionStructure (State1 × State2) JointSummary JointRef E12 R12) :
  (exists _ : ProjectionStructure State1 Summary1 Ref1 E1 R1, True) /\
  (exists _ : ProjectionStructure State2 Summary2 Ref2 E2 R2, True) /\
  (exists _ : ProjectionStructure (State1 × State2) JointSummary JointRef E12 R12, True) := by
  exact And.intro ⟨P1, trivial⟩ (And.intro ⟨P2, trivial⟩ ⟨P12, trivial⟩)

/-- Universal global factorization through the product mediator induced by pairwise mediator data. -/
theorem PaperMentisUmbraUniversalGlobalFactorizationStatement
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
  exact induced_transition_on_product_image_factorizes F E h_det σ T hT

/-- Obstruction theorem: without triple compatibility there is no globally consistent mediator. -/
theorem PaperMentisUmbraObstructionStatement
  {World PairIndex PairSummary Overlap GlobalSummary : Type}
  (F : OverlapMediatedFamily World PairIndex PairSummary Overlap)
  (h_not_compatible : Not (triple_compatible F)) :
  Not (exists _ : GlobalMediator (GlobalSummary := GlobalSummary) F, True) := by
  exact no_global_mediator_without_triple_compatibility F h_not_compatible

/-- Capstone closure theorem for the current Mentis Umbra Lean surface. -/
theorem PaperMentisUmbraClosureStatement
  {State Summary Ref World PairIndex PairSummary Overlap GlobalSummary : Type}
  {E : TransitionEnvelope State}
  {R : (State -> State) -> Prop}
  (P : ProjectionStructure State Summary Ref E R)
  (F : OverlapMediatedFamily World PairIndex PairSummary Overlap)
  (G : GlobalMediator (GlobalSummary := GlobalSummary) F) :
  agency_structure P /\
  intentional_structure P /\
  interior_representation_structure P /\
  triple_compatible F := by
  have hRoles := projection_structure_supports_role_predicates P
  refine And.intro hRoles.1 ?_
  refine And.intro hRoles.2.1 ?_
  exact And.intro hRoles.2.2 (global_mediator_forces_triple_compatibility F G)

/-- Verified-core bundle for the current Mentis Umbra formal surface. -/
theorem PaperMentisUmbraVerifiedCoreStatement
  {State Summary Ref α World PairIndex PairSummary Overlap GlobalSummary : Type}
  (E : TransitionEnvelope State)
  (R : (State -> State) -> Prop)
  (M : TransitionMediator State Summary)
  (L : InducedTransitionFamily State Summary)
  (referenceEq : Ref -> Ref -> Prop)
  (refOf : State -> Ref)
  (h_factorization : factors_through_mediator E M L)
  (h_reference : invariant_reference_structure referenceEq refOf R)
  (S : System α)
  (I₁ I₂ : α -> Prop)
  (h₁ : ∀ a, I₁ a -> standing S a)
  (h₂ : ∀ a, I₂ a -> standing S a)
  (h_complete₁ : ∀ a, standing S a -> I₁ a)
  (h_complete₂ : ∀ a, standing S a -> I₂ a)
  (QD : α -> Prop)
  (h_toStanding : ∀ a : α, QD a -> standing S a)
  (h_fromStanding : ∀ a : α, standing S a -> QD a)
  (F : OverlapMediatedFamily World PairIndex PairSummary Overlap)
  (G : GlobalMediator (GlobalSummary := GlobalSummary) F) :
  (exists _ : ProjectionStructure State Summary Ref E R, True) /\
  lawfully_equivalent_interiors I₁ I₂ /\
  lawfully_equivalent_interiors QD (fun x => standing S x) /\
  triple_compatible F := by
  refine And.intro ?_ ?_
  · exact
      ⟨PaperMentisUmbraSingleSystemProjectionNecessityStatement
        E R M L referenceEq refOf h_factorization h_reference, trivial⟩
  · refine And.intro ?_ ?_
    · exact
        PaperMentisUmbraInvariantReferenceUniquenessStatement
          S I₁ I₂ h₁ h₂ h_complete₁ h_complete₂
    · refine And.intro ?_ ?_
      · exact
          PaperMentisUmbraRoleClassifierCollapseStatement
            S QD h_toStanding h_fromStanding
      · exact global_mediator_forces_triple_compatibility F G

end MaleyLean
