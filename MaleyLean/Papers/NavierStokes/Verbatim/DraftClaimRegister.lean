import MaleyLean.Papers.NavierStokes.Obligations.SectionTheoremLedger

namespace MaleyLean

/--
Draft-facing claim register for the primitive Navier--Stokes manuscript.

This file introduces explicit manuscript-style labels so the current Lean
surface can be read against the draft at near-textual granularity. Each draft
claim is mapped to a cleaned ledger claim and inherits its support status.
-/
inductive NSDraftClaimLabel
  | introCarrierLineage
  | introStandingLineage
  | localPreHorizonWitness
  | localSingularImageTyping
  | quotientNoSecondGate
  | continuationBoundaryGate
  | horizonCollapseSplit
  | restartTransportPersistence
  | maximalLineageClosure
  | primitiveNoBlowupBoundary
  | vortexStretchingAnomalyBoundary
  | endpointTransferGap
  deriving DecidableEq, Repr

def draft_claim_to_paper_claim
  (d : NSDraftClaimLabel) : NSPaperClaim :=
  match d with
  | .introCarrierLineage => .carrierLineageBindingClaim
  | .introStandingLineage => .standingPositiveLineageClaim
  | .localPreHorizonWitness => .preHorizonWitnessClaim
  | .localSingularImageTyping => .singularImageSameScopeClaim
  | .quotientNoSecondGate => .quotientNoSecondGateClaim
  | .continuationBoundaryGate => .continuationBoundaryClaim
  | .horizonCollapseSplit => .horizonCollapseClaim
  | .restartTransportPersistence => .restartTransportClaim
  | .maximalLineageClosure => .maximalLineageClosureClaim
  | .primitiveNoBlowupBoundary => .primitiveNoBlowupClaim
  | .vortexStretchingAnomalyBoundary => .vortexStretchingAnomalyClaim
  | .endpointTransferGap => .endpointTransferClaim

def draft_claim_support_kind
  (d : NSDraftClaimLabel) : NSClaimSupportKind :=
  match d with
  | .introCarrierLineage => .structurallyCertified
  | .introStandingLineage => .structurallyCertified
  | .localPreHorizonWitness => .structurallyCertified
  | .localSingularImageTyping => .structurallyCertified
  | .quotientNoSecondGate => .structurallyCertified
  | .continuationBoundaryGate => .structurallyCertified
  | .horizonCollapseSplit => .structurallyCertified
  | .restartTransportPersistence => .structurallyCertified
  | .maximalLineageClosure => .structurallyCertified
  | .primitiveNoBlowupBoundary => .structurallyCertified
  | .vortexStretchingAnomalyBoundary => .namedFailureBoundary
  | .endpointTransferGap => .analyticDependent

theorem PaperDraftRegisterClassificationStatement :
  ∀ d : NSDraftClaimLabel,
    draft_claim_support_kind d = .structurallyCertified ∨
    draft_claim_support_kind d = .namedFailureBoundary ∨
    draft_claim_support_kind d = .analyticDependent := by
  intro d
  cases d
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

theorem PaperDraftRegisterAgreesWithPaperClaimLedgerStatement :
  ∀ d : NSDraftClaimLabel,
    draft_claim_support_kind d = claim_support_kind (draft_claim_to_paper_claim d) := by
  intro d
  cases d <;> rfl

theorem PaperDraftStructuralClaimsCertifiedStatement :
  draft_claim_support_kind .introCarrierLineage = .structurallyCertified ∧
  draft_claim_support_kind .introStandingLineage = .structurallyCertified ∧
  draft_claim_support_kind .localPreHorizonWitness = .structurallyCertified ∧
  draft_claim_support_kind .localSingularImageTyping = .structurallyCertified ∧
  draft_claim_support_kind .quotientNoSecondGate = .structurallyCertified ∧
  draft_claim_support_kind .continuationBoundaryGate = .structurallyCertified ∧
  draft_claim_support_kind .horizonCollapseSplit = .structurallyCertified ∧
  draft_claim_support_kind .restartTransportPersistence = .structurallyCertified ∧
  draft_claim_support_kind .maximalLineageClosure = .structurallyCertified ∧
  draft_claim_support_kind .primitiveNoBlowupBoundary = .structurallyCertified := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PaperDraftNamedFailureBoundaryStatement :
  draft_claim_support_kind .vortexStretchingAnomalyBoundary = .namedFailureBoundary := by
  rfl

theorem PaperDraftEndpointGapStatement :
  draft_claim_support_kind .endpointTransferGap = .analyticDependent := by
  rfl

theorem PaperDraftRegisterInheritsStructuralAlignmentStatement :
  ∀ d : NSDraftClaimLabel,
    draft_claim_support_kind d = .structurallyCertified →
    inventory_obligation_is_structural
      (section_obligation (claim_section (draft_claim_to_paper_claim d))) := by
  intro d h
  have h' : claim_support_kind (draft_claim_to_paper_claim d) = .structurallyCertified := by
    rw [← PaperDraftRegisterAgreesWithPaperClaimLedgerStatement d]
    exact h
  exact PaperStructuralClaimLedgerAlignmentStatement (draft_claim_to_paper_claim d) h'

end MaleyLean
