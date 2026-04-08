import MaleyLean.Papers.NavierStokes.Obligations.PaperLedger

namespace MaleyLean

/--
Claim-level ledger for the primitive Navier--Stokes manuscript.

This file refines the section ledger to near-paper granularity. Each named
claim is assigned to a section family and classified by the kind of support it
currently has in the Lean scaffold: structurally certified, named failure
boundary, or downstream analytic dependency.
-/
inductive NSPaperClaim
  | carrierLineageBindingClaim
  | standingPositiveLineageClaim
  | preHorizonWitnessClaim
  | singularImageSameScopeClaim
  | quotientNoSecondGateClaim
  | continuationBoundaryClaim
  | horizonCollapseClaim
  | restartTransportClaim
  | maximalLineageClosureClaim
  | primitiveNoBlowupClaim
  | vortexStretchingAnomalyClaim
  | endpointTransferClaim
  deriving DecidableEq, Repr

inductive NSClaimSupportKind
  | structurallyCertified
  | namedFailureBoundary
  | analyticDependent
  deriving DecidableEq, Repr

def claim_section
  (c : NSPaperClaim) : NSPaperSection :=
  match c with
  | .carrierLineageBindingClaim => .primitiveCarrierSection
  | .standingPositiveLineageClaim => .primitiveCarrierSection
  | .preHorizonWitnessClaim => .horizonWitnessSection
  | .singularImageSameScopeClaim => .singularExtractorSection
  | .quotientNoSecondGateClaim => .noSecondGateSection
  | .continuationBoundaryClaim => .singularExtractorSection
  | .horizonCollapseClaim => .horizonWitnessSection
  | .restartTransportClaim => .restartTransportSection
  | .maximalLineageClosureClaim => .maximalLineageClosureSection
  | .primitiveNoBlowupClaim => .maximalLineageClosureSection
  | .vortexStretchingAnomalyClaim => .vortexStretchingAnomalySection
  | .endpointTransferClaim => .endpointTransferSection

def claim_support_kind
  (c : NSPaperClaim) : NSClaimSupportKind :=
  match c with
  | .carrierLineageBindingClaim => .structurallyCertified
  | .standingPositiveLineageClaim => .structurallyCertified
  | .preHorizonWitnessClaim => .structurallyCertified
  | .singularImageSameScopeClaim => .structurallyCertified
  | .quotientNoSecondGateClaim => .structurallyCertified
  | .continuationBoundaryClaim => .structurallyCertified
  | .horizonCollapseClaim => .structurallyCertified
  | .restartTransportClaim => .structurallyCertified
  | .maximalLineageClosureClaim => .structurallyCertified
  | .primitiveNoBlowupClaim => .structurallyCertified
  | .vortexStretchingAnomalyClaim => .namedFailureBoundary
  | .endpointTransferClaim => .analyticDependent

theorem PaperClaimSupportClassificationStatement :
  ∀ c : NSPaperClaim,
    claim_support_kind c = .structurallyCertified ∨
    claim_support_kind c = .namedFailureBoundary ∨
    claim_support_kind c = .analyticDependent := by
  intro c
  cases c
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

theorem PaperStructuralClaimLedgerAlignmentStatement :
  ∀ c : NSPaperClaim,
    claim_support_kind c = .structurallyCertified →
    inventory_obligation_is_structural (section_obligation (claim_section c)) := by
  intro c hstruct
  cases c <;> cases hstruct
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem PaperAnalyticClaimReductionStatement :
  ∀ c : NSPaperClaim,
    claim_support_kind c = .namedFailureBoundary ∨ claim_support_kind c = .analyticDependent →
    inventory_named_failure (section_obligation (claim_section c)) ∨
    inventory_endpoint_depends_on_named_failure (section_obligation (claim_section c)) := by
  intro c h
  cases c
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem PaperPrimitiveClaimsAreCertifiedStatement :
  claim_support_kind .carrierLineageBindingClaim = .structurallyCertified ∧
  claim_support_kind .standingPositiveLineageClaim = .structurallyCertified ∧
  claim_support_kind .preHorizonWitnessClaim = .structurallyCertified ∧
  claim_support_kind .singularImageSameScopeClaim = .structurallyCertified ∧
  claim_support_kind .quotientNoSecondGateClaim = .structurallyCertified ∧
  claim_support_kind .continuationBoundaryClaim = .structurallyCertified ∧
  claim_support_kind .horizonCollapseClaim = .structurallyCertified ∧
  claim_support_kind .restartTransportClaim = .structurallyCertified ∧
  claim_support_kind .maximalLineageClosureClaim = .structurallyCertified ∧
  claim_support_kind .primitiveNoBlowupClaim = .structurallyCertified := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PaperVortexStretchingClaimIsNamedFailureStatement :
  claim_support_kind .vortexStretchingAnomalyClaim = .namedFailureBoundary := by
  rfl

theorem PaperEndpointTransferClaimIsAnalyticDependentStatement :
  claim_support_kind .endpointTransferClaim = .analyticDependent := by
  rfl

end MaleyLean
