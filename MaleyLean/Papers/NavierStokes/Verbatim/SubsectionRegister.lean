import MaleyLean.Papers.NavierStokes.Verbatim.DraftClaimRegister

namespace MaleyLean

/--
Verbatim textual register extracted from the current Navier--Stokes manuscript
bundle.

Each entry is keyed to an actual title found in the extracted `.tex` sources
and mapped onto the cleaned draft-claim ledger.
-/
inductive NSVerbatimTextualEntry
  | carrierToLineageBindingCommitment
  | standingIntelligibilityPacketInternalizedAtFixedPeriodicScope
  | constructiveDiagnosticBranchForcingFromBreakdownWitnesses
  | constructiveSingularCandidateExtraction
  | noSecondSameScopeSingularityGate
  | noCompetingSameScopeContinuationGates
  | quotientVisibleVsIllicitSingularity
  | transferFaithfulnessLocalClassicalContinuation
  | pdeNativeAdmissibilityPacketOnTheMaximalClassicalInterval
  | noAdmissibleSameScopeSingularityGateRemains
  | pointwiseVortexStretchingGateCollapse
  | officialPeriodicTheoremOnT3
  deriving DecidableEq, Repr

def verbatim_entry_title (s : NSVerbatimTextualEntry) : String :=
  match s with
  | .carrierToLineageBindingCommitment =>
      "Carrier-to-lineage binding, no admissibility dynamics, and representational commitment on realized lineages"
  | .standingIntelligibilityPacketInternalizedAtFixedPeriodicScope =>
      "Standing/intelligibility packet internalized at fixed periodic scope"
  | .constructiveDiagnosticBranchForcingFromBreakdownWitnesses =>
      "Constructive diagnostic branch forcing from breakdown witnesses"
  | .constructiveSingularCandidateExtraction =>
      "Constructive singular-candidate extraction"
  | .noSecondSameScopeSingularityGate =>
      "No second same-scope singularity gate"
  | .noCompetingSameScopeContinuationGates =>
      "No competing same-scope continuation gates on the standard periodic carrier"
  | .quotientVisibleVsIllicitSingularity =>
      "Quotient-visible vs illicit singularity"
  | .transferFaithfulnessLocalClassicalContinuation =>
      "Transfer faithfulness: local classical continuation on the realized class"
  | .pdeNativeAdmissibilityPacketOnTheMaximalClassicalInterval =>
      "PDE-native admissibility packet on the maximal classical interval"
  | .noAdmissibleSameScopeSingularityGateRemains =>
      "No admissible same-scope singularity gate remains"
  | .pointwiseVortexStretchingGateCollapse =>
      "Pointwise vortex-stretching gate collapse"
  | .officialPeriodicTheoremOnT3 =>
      "Official periodic theorem on T^3 (Fefferman (B); official classical restatement of Corollary 21A)"

def verbatim_entry_to_draft_claim
  (s : NSVerbatimTextualEntry) : NSDraftClaimLabel :=
  match s with
  | .carrierToLineageBindingCommitment => .introCarrierLineage
  | .standingIntelligibilityPacketInternalizedAtFixedPeriodicScope => .introStandingLineage
  | .constructiveDiagnosticBranchForcingFromBreakdownWitnesses => .localPreHorizonWitness
  | .constructiveSingularCandidateExtraction => .localSingularImageTyping
  | .noSecondSameScopeSingularityGate => .quotientNoSecondGate
  | .noCompetingSameScopeContinuationGates => .continuationBoundaryGate
  | .quotientVisibleVsIllicitSingularity => .horizonCollapseSplit
  | .transferFaithfulnessLocalClassicalContinuation => .restartTransportPersistence
  | .pdeNativeAdmissibilityPacketOnTheMaximalClassicalInterval => .maximalLineageClosure
  | .noAdmissibleSameScopeSingularityGateRemains => .primitiveNoBlowupBoundary
  | .pointwiseVortexStretchingGateCollapse => .vortexStretchingAnomalyBoundary
  | .officialPeriodicTheoremOnT3 => .endpointTransferGap

def verbatim_entry_support_kind
  (s : NSVerbatimTextualEntry) : NSClaimSupportKind :=
  draft_claim_support_kind (verbatim_entry_to_draft_claim s)

theorem PaperVerbatimEntryClassificationStatement :
  forall s : NSVerbatimTextualEntry,
    verbatim_entry_support_kind s = .structurallyCertified \/
    verbatim_entry_support_kind s = .namedFailureBoundary \/
    verbatim_entry_support_kind s = .analyticDependent := by
  intro s
  cases s
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem PaperVerbatimRegisterAgreesWithDraftRegisterStatement :
  forall s : NSVerbatimTextualEntry,
    verbatim_entry_support_kind s = draft_claim_support_kind (verbatim_entry_to_draft_claim s) := by
  intro s
  cases s <;> rfl

theorem PaperVerbatimStructuralEntriesCertifiedStatement :
  verbatim_entry_support_kind .carrierToLineageBindingCommitment = .structurallyCertified /\
  verbatim_entry_support_kind .standingIntelligibilityPacketInternalizedAtFixedPeriodicScope = .structurallyCertified /\
  verbatim_entry_support_kind .constructiveDiagnosticBranchForcingFromBreakdownWitnesses = .structurallyCertified /\
  verbatim_entry_support_kind .constructiveSingularCandidateExtraction = .structurallyCertified /\
  verbatim_entry_support_kind .noSecondSameScopeSingularityGate = .structurallyCertified /\
  verbatim_entry_support_kind .noCompetingSameScopeContinuationGates = .structurallyCertified /\
  verbatim_entry_support_kind .quotientVisibleVsIllicitSingularity = .structurallyCertified /\
  verbatim_entry_support_kind .transferFaithfulnessLocalClassicalContinuation = .structurallyCertified /\
  verbatim_entry_support_kind .pdeNativeAdmissibilityPacketOnTheMaximalClassicalInterval = .structurallyCertified /\
  verbatim_entry_support_kind .noAdmissibleSameScopeSingularityGateRemains = .structurallyCertified := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PaperVerbatimNamedFailureBoundaryStatement :
  verbatim_entry_support_kind .pointwiseVortexStretchingGateCollapse = .namedFailureBoundary := by
  rfl

theorem PaperVerbatimEndpointGapStatement :
  verbatim_entry_support_kind .officialPeriodicTheoremOnT3 = .analyticDependent := by
  rfl

theorem PaperVerbatimRegisterInheritsStructuralAlignmentStatement :
  forall s : NSVerbatimTextualEntry,
    verbatim_entry_support_kind s = .structurallyCertified ->
    inventory_obligation_is_structural
      (section_obligation (claim_section (draft_claim_to_paper_claim (verbatim_entry_to_draft_claim s)))) := by
  intro s h
  have h' : draft_claim_support_kind (verbatim_entry_to_draft_claim s) = .structurallyCertified := by
    rw [<- PaperVerbatimRegisterAgreesWithDraftRegisterStatement s]
    exact h
  exact PaperDraftRegisterInheritsStructuralAlignmentStatement (verbatim_entry_to_draft_claim s) h'

end MaleyLean
