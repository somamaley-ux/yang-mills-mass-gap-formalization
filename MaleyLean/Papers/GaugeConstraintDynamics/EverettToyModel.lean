import MaleyLean.Papers.GaugeConstraintDynamics.EverettSelectors

namespace MaleyLean

/--
A tiny finite carrier for the paper's Bell-state toy discussion.

The point is not to formalize Hilbert space in full, but to give the repo a
concrete state/specification pair witnessing that branch extraction can vary
with factorization choice even when the underlying state is fixed.
-/
inductive EverettToyState where
  | bellLike
deriving DecidableEq, Repr

/-- Two competing auxiliary factorizations for the same toy state. -/
inductive EverettToyFactorization where
  | standardAB
  | rotatedAprimeBprime
deriving DecidableEq, Repr

/-- Branch multiplicity extracted from the toy state under a chosen factorization. -/
def everett_toy_branch_count :
  EverettToyState -> EverettToyFactorization -> Nat
  | .bellLike, .standardAB => 2
  | .bellLike, .rotatedAprimeBprime => 1

/-- Corresponding branch-description labels for the same toy state. -/
inductive EverettToyBranchDescription where
  | twoBranch
  | oneBranch
deriving DecidableEq, Repr

/-- Concrete branch extraction mirroring the manuscript's toy factorization contrast. -/
def everett_toy_branch_description :
  EverettToyState -> EverettToyFactorization -> EverettToyBranchDescription
  | .bellLike, .standardAB => .twoBranch
  | .bellLike, .rotatedAprimeBprime => .oneBranch

/-- The toy branch extraction as an instance of the abstract Everett substrate. -/
def everettToyBranchingData :
  EverettBranchingData EverettToyState EverettToyFactorization EverettToyBranchDescription where
  extract rho sigma := everett_toy_branch_description rho sigma.data

/-- A simple weight rule derived from the extracted branch count. -/
def everettToyWeightRule :
  EverettWeightRule EverettToyState EverettToyFactorization Nat where
  assign rho sigma := everett_toy_branch_count rho sigma.data

/-- The Bell-like toy state has different branch counts under the two factorizations. -/
theorem everett_toy_branch_count_noninvariant :
  everett_toy_branch_count
      EverettToyState.bellLike
      EverettToyFactorization.standardAB
    ≠
    everett_toy_branch_count
      EverettToyState.bellLike
      EverettToyFactorization.rotatedAprimeBprime := by
  decide

/-- The branch-description layer is likewise factorization-dependent. -/
theorem everett_toy_branch_description_noninvariant :
  everett_toy_branch_description
      EverettToyState.bellLike
      EverettToyFactorization.standardAB
    ≠
    everett_toy_branch_description
      EverettToyState.bellLike
      EverettToyFactorization.rotatedAprimeBprime := by
  decide

/-- Concrete witness that the toy branch extraction is non-invariant. -/
theorem everett_toy_branching_noninvariant :
  branch_extraction_noninvariant everettToyBranchingData := by
  refine ⟨EverettToyState.bellLike, ⟨EverettToyFactorization.standardAB⟩, ?_, ?_⟩
  · exact ⟨EverettToyFactorization.rotatedAprimeBprime⟩
  · exact everett_toy_branch_description_noninvariant

/-- The toy branch extraction is therefore not state-determined. -/
theorem everett_toy_branching_not_state_determined :
  ¬ (forall rho : EverettToyState,
      forall sigma tau : EverettAuxiliarySpec EverettToyFactorization,
        everettToyBranchingData.extract rho sigma =
          everettToyBranchingData.extract rho tau) := by
  exact
    noninvariant_branch_extraction_not_state_determined
      everettToyBranchingData
      everett_toy_branching_noninvariant

/-- Concrete witness that the toy weight rule is outcome-relevant. -/
theorem everett_toy_weight_rule_outcome_relevant :
  everett_weight_outcome_relevant everettToyWeightRule := by
  refine ⟨EverettToyState.bellLike, ⟨EverettToyFactorization.standardAB⟩, ?_, ?_⟩
  · exact ⟨EverettToyFactorization.rotatedAprimeBprime⟩
  · exact everett_toy_branch_count_noninvariant

/-- Hence the toy weight rule cannot be determined by state alone. -/
theorem everett_toy_weight_rule_not_state_determined :
  ¬ everett_weight_state_determined everettToyWeightRule := by
  exact
    outcome_relevant_weights_require_auxiliary_dependence
      everettToyWeightRule
      everett_toy_weight_rule_outcome_relevant

/--
If one treats the factorization label as not carried by the physical state, the
toy model lands in the meta-selection branch of the selector diagnosis.
-/
theorem everett_toy_selector_meta_if_not_reified
  (stateCarries : EverettToyState -> EverettAuxiliarySpec EverettToyFactorization -> Prop)
  (h_not_reified : ¬ selector_reified_as_state stateCarries) :
  exists tag : EverettSelectorDiagnosis,
    match tag with
    | EverettSelectorDiagnosis.pureBookkeeping =>
        ¬ everett_weight_outcome_relevant everettToyWeightRule
    | EverettSelectorDiagnosis.metaSelection =>
        everett_weight_outcome_relevant everettToyWeightRule /\
        ¬ selector_reified_as_state stateCarries
    | EverettSelectorDiagnosis.reifiedSelector =>
        selector_reified_as_state stateCarries := by
  exact ⟨EverettSelectorDiagnosis.metaSelection,
    And.intro everett_toy_weight_rule_outcome_relevant h_not_reified⟩

/--
Toy symmetric branch pair: two labels that are treated as invariantly
indistinguishable by the admitted observables.
-/
def everettToySymmetricPair : SymmetricBranchPair Bool where
  left := true
  right := false
  invariantlyIndistinguishable := True

/-- Equal weights on the toy symmetric pair. -/
theorem everett_toy_invariant_measure_on_symmetric_pair :
  invariant_measure_on_pair
    (fun _ : Bool => (1 : Nat))
    Eq
    everettToySymmetricPair := by
  rfl

/-- Constant selectors are selector-free on the toy symmetric pair. -/
theorem everett_toy_constant_selector_free
  (c : Nat) :
  selector_free_on_pair
    ({ pick := fun _ => c } : BranchSelector Bool Nat)
    everettToySymmetricPair
    Eq := by
  rfl

end MaleyLean
