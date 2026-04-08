import MaleyLean.Papers.GaugeConstraintDynamics.EverettSelectors

namespace MaleyLean

/--
Minimal decoherence-facing package for the Everett section of the paper.

The intent is to expose the dependence of branch records on auxiliary pointer
or coarse-graining choices without pretending that a full Hilbert-space library
is already present in the repo.
-/
structure EverettDecoherenceData (State Pointer Record : Type) where
  recordOf : State -> EverettAuxiliarySpec Pointer -> Record

/-- A decoherence record is presentation-invariant when pointer choices never change it. -/
def decoherence_record_state_determined
  {State Pointer Record : Type}
  (D : EverettDecoherenceData State Pointer Record) : Prop :=
  forall rho : State,
    forall sigma tau : EverettAuxiliarySpec Pointer,
      D.recordOf rho sigma = D.recordOf rho tau

/-- A decoherence record is non-invariant when two pointer presentations disagree. -/
def decoherence_record_noninvariant
  {State Pointer Record : Type}
  (D : EverettDecoherenceData State Pointer Record) : Prop :=
  exists rho : State, exists sigma tau : EverettAuxiliarySpec Pointer,
    Not (D.recordOf rho sigma = D.recordOf rho tau)

/-- Every decoherence package induces an Everett branch-extraction package. -/
def EverettDecoherenceData.toBranchingData
  {State Pointer Record : Type}
  (D : EverettDecoherenceData State Pointer Record) :
  EverettBranchingData State Pointer Record where
  extract := D.recordOf

/--
If a decoherence record varies with pointer presentation, then it is not a
function of the physical state alone.
-/
theorem decoherence_record_noninvariant_not_state_determined
  {State Pointer Record : Type}
  (D : EverettDecoherenceData State Pointer Record)
  (h_noninv : decoherence_record_noninvariant D) :
  Not (decoherence_record_state_determined D) := by
  intro hdet
  rcases h_noninv with ⟨rho, sigma, tau, hneq⟩
  exact hneq (hdet rho sigma tau)

/--
Non-invariant decoherence records produce the same auxiliary-dependence
diagnosis as a non-invariant Everett branch extraction.
-/
theorem decoherence_record_noninvariant_forces_branch_noninvariance
  {State Pointer Record : Type}
  (D : EverettDecoherenceData State Pointer Record)
  (h_noninv : decoherence_record_noninvariant D) :
  branch_extraction_noninvariant D.toBranchingData := by
  rcases h_noninv with ⟨rho, sigma, tau, hneq⟩
  exact ⟨rho, sigma, tau, hneq⟩

/-- A simple pointer-weight rule derived from branch-record multiplicity data. -/
structure EverettPointerWeightRule (State Pointer Weight : Type) where
  assign : State -> EverettAuxiliarySpec Pointer -> Weight

/-- Pointer-weight rules are state-determined when pointer choices never matter. -/
def pointer_weight_state_determined
  {State Pointer Weight : Type}
  (W : EverettPointerWeightRule State Pointer Weight) : Prop :=
  forall rho : State,
    forall sigma tau : EverettAuxiliarySpec Pointer,
      W.assign rho sigma = W.assign rho tau

/-- Pointer-weight rules are outcome-relevant when pointer choices change the weights. -/
def pointer_weight_outcome_relevant
  {State Pointer Weight : Type}
  (W : EverettPointerWeightRule State Pointer Weight) : Prop :=
  exists rho : State, exists sigma tau : EverettAuxiliarySpec Pointer,
    Not (W.assign rho sigma = W.assign rho tau)

/-- Outcome relevance again blocks state-determined status. -/
theorem pointer_weight_outcome_relevant_not_state_determined
  {State Pointer Weight : Type}
  (W : EverettPointerWeightRule State Pointer Weight)
  (h_rel : pointer_weight_outcome_relevant W) :
  Not (pointer_weight_state_determined W) := by
  intro hdet
  rcases h_rel with ⟨rho, sigma, tau, hneq⟩
  exact hneq (hdet rho sigma tau)

/--
Finite toy state for a decoherence/coarse-graining witness.

The same underlying entangled state can be read with a fine pointer basis
yielding two records or with a coarse pointer basis yielding one merged record.
-/
inductive EverettToyDecoherenceState where
  | entangledPair
deriving DecidableEq, Repr

/-- Competing auxiliary pointer presentations for the same toy state. -/
inductive EverettToyPointerPresentation where
  | finePointer
  | coarsePointer
deriving DecidableEq, Repr

/-- Observable branch records extracted from the toy state. -/
inductive EverettToyPointerRecord where
  | leftRecord
  | rightRecord
  | mergedRecord
deriving DecidableEq, Repr

/-- Fine presentation keeps two records distinct, coarse presentation merges them. -/
def everett_toy_pointer_record :
  EverettToyDecoherenceState ->
  EverettToyPointerPresentation ->
  EverettToyPointerRecord
  | .entangledPair, .finePointer => .leftRecord
  | .entangledPair, .coarsePointer => .mergedRecord

/-- The toy decoherence package. -/
def everettToyDecoherenceData :
  EverettDecoherenceData
    EverettToyDecoherenceState
    EverettToyPointerPresentation
    EverettToyPointerRecord where
  recordOf rho sigma := everett_toy_pointer_record rho sigma.data

/-- Simple multiplicity-like weight rule attached to the toy pointer presentation. -/
def everettToyPointerWeightRule :
  EverettPointerWeightRule
    EverettToyDecoherenceState
    EverettToyPointerPresentation
    Nat where
  assign rho sigma :=
    match rho, sigma.data with
    | .entangledPair, .finePointer => 2
    | .entangledPair, .coarsePointer => 1

/-- The toy pointer record is presentation-dependent. -/
theorem everett_toy_pointer_record_noninvariant :
  decoherence_record_noninvariant everettToyDecoherenceData := by
  refine Exists.intro EverettToyDecoherenceState.entangledPair ?_
  refine Exists.intro ⟨EverettToyPointerPresentation.finePointer⟩ ?_
  refine Exists.intro ⟨EverettToyPointerPresentation.coarsePointer⟩ ?_
  decide

/-- Hence the toy decoherence record is not determined by state alone. -/
theorem everett_toy_pointer_record_not_state_determined :
  Not (decoherence_record_state_determined everettToyDecoherenceData) := by
  exact
    decoherence_record_noninvariant_not_state_determined
      everettToyDecoherenceData
      everett_toy_pointer_record_noninvariant

/-- The induced Everett branch extraction is likewise non-invariant. -/
theorem everett_toy_decoherence_branching_noninvariant :
  branch_extraction_noninvariant everettToyDecoherenceData.toBranchingData := by
  exact
    decoherence_record_noninvariant_forces_branch_noninvariance
      everettToyDecoherenceData
      everett_toy_pointer_record_noninvariant

/-- The toy pointer-weight rule is outcome-relevant. -/
theorem everett_toy_pointer_weight_outcome_relevant :
  pointer_weight_outcome_relevant everettToyPointerWeightRule := by
  refine Exists.intro EverettToyDecoherenceState.entangledPair ?_
  refine Exists.intro ⟨EverettToyPointerPresentation.finePointer⟩ ?_
  refine Exists.intro ⟨EverettToyPointerPresentation.coarsePointer⟩ ?_
  decide

/-- Therefore the toy pointer-weight rule is not state-determined. -/
theorem everett_toy_pointer_weight_not_state_determined :
  Not (pointer_weight_state_determined everettToyPointerWeightRule) := by
  exact
    pointer_weight_outcome_relevant_not_state_determined
      everettToyPointerWeightRule
      everett_toy_pointer_weight_outcome_relevant

/--
If the pointer presentation is not reified as physical state, the toy
decoherence witness lands in the meta-selection branch of the Everett trilemma.
-/
theorem everett_toy_decoherence_meta_if_not_reified
  (stateCarries :
    EverettToyDecoherenceState ->
    EverettAuxiliarySpec EverettToyPointerPresentation ->
    Prop)
  (h_not_reified : Not (selector_reified_as_state stateCarries)) :
  exists tag : EverettSelectorDiagnosis,
    match tag with
    | EverettSelectorDiagnosis.pureBookkeeping =>
        Not (pointer_weight_outcome_relevant everettToyPointerWeightRule)
    | EverettSelectorDiagnosis.metaSelection =>
        pointer_weight_outcome_relevant everettToyPointerWeightRule /\
        Not (selector_reified_as_state stateCarries)
    | EverettSelectorDiagnosis.reifiedSelector =>
        selector_reified_as_state stateCarries := by
  refine Exists.intro EverettSelectorDiagnosis.metaSelection ?_
  exact And.intro everett_toy_pointer_weight_outcome_relevant h_not_reified

/-- Symmetric pair of fine-grained toy records. -/
def everettToyFineRecordPair : SymmetricBranchPair EverettToyPointerRecord where
  left := EverettToyPointerRecord.leftRecord
  right := EverettToyPointerRecord.rightRecord
  invariantlyIndistinguishable := True

/-- Equal weighting on the toy fine-grained record pair. -/
theorem everett_toy_fine_record_pair_invariant_measure :
  invariant_measure_on_pair
    (fun record =>
      match record with
      | EverettToyPointerRecord.leftRecord => 1
      | EverettToyPointerRecord.rightRecord => 1
      | EverettToyPointerRecord.mergedRecord => 2)
    Eq
    everettToyFineRecordPair := by
  rfl

/-- A constant selector remains selector-free on the symmetric fine-grained pair. -/
theorem everett_toy_fine_record_constant_selector_free
  (c : Nat) :
  selector_free_on_pair
    ({ pick := fun _ => c } : BranchSelector EverettToyPointerRecord Nat)
    everettToyFineRecordPair
    Eq := by
  rfl

end MaleyLean
