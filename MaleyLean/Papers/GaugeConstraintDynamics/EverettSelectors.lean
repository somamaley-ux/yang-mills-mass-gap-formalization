import MaleyLean.Foundation

namespace MaleyLean

/--
Auxiliary specification used to extract branches from the same underlying
physical state: factorization, coarse-graining, pointer algebra, record rule,
or any equivalent selector-bearing presentation data.
-/
structure EverettAuxiliarySpec (Spec : Type) where
  data : Spec

/--
Minimal branch-extraction package for the Everett section of the paper.

`extract state sigma` is the branch description produced from the same physical
state together with some auxiliary branch-extraction specification.
-/
structure EverettBranchingData (State Spec Branch : Type) where
  extract : State -> EverettAuxiliarySpec Spec -> Branch

/-- A weight rule built on top of a branch extraction package. -/
structure EverettWeightRule (State Spec Weight : Type) where
  assign : State -> EverettAuxiliarySpec Spec -> Weight

/--
Outcome relevance for a weight rule: two presentations with the same underlying
physical state can disagree in the rule's output.
-/
def everett_weight_outcome_relevant
  {State Spec Weight : Type}
  (W : EverettWeightRule State Spec Weight) : Prop :=
  exists rho : State, exists sigma tau : EverettAuxiliarySpec Spec,
    W.assign rho sigma ≠ W.assign rho tau

/--
The rule is determined by the reduced/physical state alone if every two
auxiliary presentations of the same state yield the same output.
-/
def everett_weight_state_determined
  {State Spec Weight : Type}
  (W : EverettWeightRule State Spec Weight) : Prop :=
  forall rho : State,
    forall sigma tau : EverettAuxiliarySpec Spec,
      W.assign rho sigma = W.assign rho tau

/--
Selector reification means the relevant auxiliary specification is promoted into
the physical state interface rather than treated as extra external data.
-/
def selector_reified_as_state
  {State Spec : Type}
  (stateCarries : State -> EverettAuxiliarySpec Spec -> Prop) : Prop :=
  forall rho : State, exists sigma : EverettAuxiliarySpec Spec, stateCarries rho sigma

/-- A branch extraction is non-invariant when two auxiliary presentations disagree. -/
def branch_extraction_noninvariant
  {State Spec Branch : Type}
  (B : EverettBranchingData State Spec Branch) : Prop :=
  exists rho : State, exists sigma tau : EverettAuxiliarySpec Spec,
    B.extract rho sigma ≠ B.extract rho tau

/--
A branch selector singles out one branch from a branch description. This is the
abstract selector layer the paper argues is not fixed by unitary branching
alone.
-/
structure BranchSelector (Branch Choice : Type) where
  pick : Branch -> Choice

/--
Symmetric branching means the two candidate branches are indistinguishable by
the invariant observables currently admitted on the reduced space.
-/
structure SymmetricBranchPair (Branch : Type) where
  left : Branch
  right : Branch
  invariantlyIndistinguishable : Prop

/-- An invariant measure cannot distinguish a symmetric pair if it agrees on both sides. -/
def invariant_measure_on_pair
  {Branch Weight : Type}
  (mu : Branch -> Weight)
  (sameWeight : Weight -> Weight -> Prop)
  (pair : SymmetricBranchPair Branch) : Prop :=
  sameWeight (mu pair.left) (mu pair.right)

/--
Selector-freeness on a symmetric pair means no admitted rule singles out one
side over the other.
-/
def selector_free_on_pair
  {Branch Choice : Type}
  (S : BranchSelector Branch Choice)
  (pair : SymmetricBranchPair Branch)
  (sameChoice : Choice -> Choice -> Prop) : Prop :=
  sameChoice (S.pick pair.left) (S.pick pair.right)

/-- Decision labels for the Everett selector trilemma. -/
inductive EverettSelectorDiagnosis where
  | pureBookkeeping
  | metaSelection
  | reifiedSelector
deriving DecidableEq, Repr

/--
If a branch extraction already varies with auxiliary specification, then it is
not a function of the physical state alone.
-/
theorem noninvariant_branch_extraction_not_state_determined
  {State Spec Branch : Type}
  (B : EverettBranchingData State Spec Branch)
  (h_noninv : branch_extraction_noninvariant B) :
  ¬ (forall rho : State,
      forall sigma tau : EverettAuxiliarySpec Spec,
        B.extract rho sigma = B.extract rho tau) := by
  intro hdet
  rcases h_noninv with ⟨rho, sigma, tau, hneq⟩
  exact hneq (hdet rho sigma tau)

/--
A concrete non-invariant branch extraction immediately yields the paper's
selector-dependence claim.
-/
theorem noninvariant_branch_extraction_forces_auxiliary_dependence
  {State Spec Branch : Type}
  (B : EverettBranchingData State Spec Branch)
  (h_noninv : branch_extraction_noninvariant B) :
  exists rho : State, exists sigma tau : EverettAuxiliarySpec Spec,
    B.extract rho sigma ≠ B.extract rho tau := by
  exact h_noninv

/--
If a weight rule is state-determined, then it cannot be outcome-relevant in the
paper's auxiliary-variance sense.
-/
theorem state_determined_weights_not_outcome_relevant
  {State Spec Weight : Type}
  (W : EverettWeightRule State Spec Weight)
  (hdet : everett_weight_state_determined W) :
  ¬ everett_weight_outcome_relevant W := by
  intro hrel
  rcases hrel with ⟨rho, sigma, tau, hneq⟩
  exact hneq (hdet rho sigma tau)

/--
Conversely, an outcome-relevant weight rule cannot be state-determined.
-/
theorem outcome_relevant_weights_require_auxiliary_dependence
  {State Spec Weight : Type}
  (W : EverettWeightRule State Spec Weight)
  (hrel : everett_weight_outcome_relevant W) :
  ¬ everett_weight_state_determined W := by
  intro hdet
  exact state_determined_weights_not_outcome_relevant W hdet hrel

/--
Selector diagnosis for a weight rule: either it is pure bookkeeping, illicit
meta-selection, or its selector data must be reified as part of state.
-/
theorem everett_selector_diagnosis
  {State Spec Weight : Type}
  (W : EverettWeightRule State Spec Weight)
  (stateCarries : State -> EverettAuxiliarySpec Spec -> Prop)
  [Decidable (everett_weight_outcome_relevant W)]
  [Decidable (selector_reified_as_state stateCarries)] :
  exists tag : EverettSelectorDiagnosis,
    match tag with
    | EverettSelectorDiagnosis.pureBookkeeping =>
        ¬ everett_weight_outcome_relevant W
    | EverettSelectorDiagnosis.metaSelection =>
        everett_weight_outcome_relevant W /\
        ¬ selector_reified_as_state stateCarries
    | EverettSelectorDiagnosis.reifiedSelector =>
        selector_reified_as_state stateCarries := by
  by_cases hOut : everett_weight_outcome_relevant W
  · by_cases hReif : selector_reified_as_state stateCarries
    · exact ⟨EverettSelectorDiagnosis.reifiedSelector, hReif⟩
    · exact ⟨EverettSelectorDiagnosis.metaSelection, And.intro hOut hReif⟩
  · exact ⟨EverettSelectorDiagnosis.pureBookkeeping, hOut⟩

/--
If an invariant measure gives equal weight to a symmetric branch pair, then any
selector that picks one side over the other must add structure beyond the
measure itself.
-/
theorem invariant_measure_on_symmetric_pair_blocks_selector_free_singling
  {Branch Weight Choice : Type}
  (mu : Branch -> Weight)
  (sameWeight : Weight -> Weight -> Prop)
  (sameChoice : Choice -> Choice -> Prop)
  (pair : SymmetricBranchPair Branch)
  (S : BranchSelector Branch Choice)
  (h_measure : invariant_measure_on_pair mu sameWeight pair)
  (h_sameWeight_respects_sameChoice :
    sameWeight (mu pair.left) (mu pair.right) ->
    sameChoice (S.pick pair.left) (S.pick pair.right)) :
  selector_free_on_pair S pair sameChoice := by
  exact h_sameWeight_respects_sameChoice h_measure

/--
An admitted singular selector on a symmetric pair must either break invariance
or rely on extra selector structure.
-/
theorem symmetric_pair_selector_requires_break_or_extra_structure
  {Rule : Type}
  (breaksInvariance : Rule -> Prop)
  (usesExtraSelector : Rule -> Prop)
  (h_selector_if_not_break :
    forall r : Rule, ¬ breaksInvariance r -> usesExtraSelector r) :
  forall r : Rule, ¬ (¬ breaksInvariance r /\ ¬ usesExtraSelector r) := by
  intro r h
  have hExtra : usesExtraSelector r := h_selector_if_not_break r h.1
  exact h.2 hExtra

/--
Terminal exhaustion of selector-certifier classes in the Everett regime.
-/
theorem everett_no_admissible_certifier_from_terminal_classes
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

end MaleyLean
