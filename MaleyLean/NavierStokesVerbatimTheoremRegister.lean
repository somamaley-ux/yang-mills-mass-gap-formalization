import MaleyLean.NavierStokesSectionTheoremLedger

namespace MaleyLean

/--
Verbatim theorem-level register extracted from the current Navier--Stokes
manuscript bundle.

Each entry is keyed to an actual theorem, lemma, proposition, or corollary
title found in the extracted `.tex` sources and mapped onto the cleaned paper
claim ledger.
-/
inductive NSVerbatimTheoremEntry
  | standingQuotientFutureBehaviorQuotient
  | noCompetingSameScopeContinuationGates
  | pointwiseVortexStretchingGateCollapse
  | noSecondSameScopeSingularityGate
  | quotientVisibleVsIllicitSingularity
  | structuralRegularityOnTheCertifiedPeriodicCarrier
  | transferFaithfulnessLocalClassicalContinuation
  | constructiveDiagnosticBranchForcingFromBreakdownWitnesses
  | constructiveSingularCandidateExtraction
  | noIllicitSingularImage
  | noQuotientVisibleSingularImage
  | transferImpossibilityNoSingularImageOfTheUniqueAdmissibleInterior
  | officialPeriodicTheoremOnT3
  | noFiniteTimeBlowUpOnTheOfficialPeriodicCarrier
  deriving DecidableEq, Repr

def verbatim_theorem_title (t : NSVerbatimTheoremEntry) : String :=
  match t with
  | .standingQuotientFutureBehaviorQuotient =>
      "Standing quotient = future-behavior quotient"
  | .noCompetingSameScopeContinuationGates =>
      "No competing same-scope continuation gates on the standard periodic carrier"
  | .pointwiseVortexStretchingGateCollapse =>
      "Pointwise vortex-stretching gate collapse"
  | .noSecondSameScopeSingularityGate =>
      "No second same-scope singularity gate"
  | .quotientVisibleVsIllicitSingularity =>
      "Quotient-visible vs illicit singularity"
  | .structuralRegularityOnTheCertifiedPeriodicCarrier =>
      "Structural regularity on the certified periodic carrier"
  | .transferFaithfulnessLocalClassicalContinuation =>
      "Transfer faithfulness: local classical continuation on the realized class"
  | .constructiveDiagnosticBranchForcingFromBreakdownWitnesses =>
      "Constructive diagnostic branch forcing from breakdown witnesses"
  | .constructiveSingularCandidateExtraction =>
      "Constructive singular-candidate extraction"
  | .noIllicitSingularImage =>
      "No illicit singular image"
  | .noQuotientVisibleSingularImage =>
      "No quotient-visible singular image"
  | .transferImpossibilityNoSingularImageOfTheUniqueAdmissibleInterior =>
      "Transfer impossibility: no singular image of the unique admissible interior"
  | .officialPeriodicTheoremOnT3 =>
      "Official periodic theorem on T^3 (Fefferman (B); official classical restatement of Corollary 21A)"
  | .noFiniteTimeBlowUpOnTheOfficialPeriodicCarrier =>
      "No finite-time blow-up on the official periodic carrier"

def verbatim_theorem_to_claim
  (t : NSVerbatimTheoremEntry) : NSPaperClaim :=
  match t with
  | .standingQuotientFutureBehaviorQuotient => .standingPositiveLineageClaim
  | .noCompetingSameScopeContinuationGates => .continuationBoundaryClaim
  | .pointwiseVortexStretchingGateCollapse => .vortexStretchingAnomalyClaim
  | .noSecondSameScopeSingularityGate => .quotientNoSecondGateClaim
  | .quotientVisibleVsIllicitSingularity => .horizonCollapseClaim
  | .structuralRegularityOnTheCertifiedPeriodicCarrier => .primitiveNoBlowupClaim
  | .transferFaithfulnessLocalClassicalContinuation => .restartTransportClaim
  | .constructiveDiagnosticBranchForcingFromBreakdownWitnesses => .preHorizonWitnessClaim
  | .constructiveSingularCandidateExtraction => .singularImageSameScopeClaim
  | .noIllicitSingularImage => .singularImageSameScopeClaim
  | .noQuotientVisibleSingularImage => .horizonCollapseClaim
  | .transferImpossibilityNoSingularImageOfTheUniqueAdmissibleInterior => .primitiveNoBlowupClaim
  | .officialPeriodicTheoremOnT3 => .endpointTransferClaim
  | .noFiniteTimeBlowUpOnTheOfficialPeriodicCarrier => .endpointTransferClaim

def verbatim_theorem_support_kind
  (t : NSVerbatimTheoremEntry) : NSClaimSupportKind :=
  claim_support_kind (verbatim_theorem_to_claim t)

theorem PaperVerbatimTheoremClassificationStatement :
  forall t : NSVerbatimTheoremEntry,
    verbatim_theorem_support_kind t = .structurallyCertified \/
    verbatim_theorem_support_kind t = .namedFailureBoundary \/
    verbatim_theorem_support_kind t = .analyticDependent := by
  intro t
  cases t
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inr rfl)

theorem PaperVerbatimTheoremRegisterAgreesWithClaimLedgerStatement :
  forall t : NSVerbatimTheoremEntry,
    verbatim_theorem_support_kind t = claim_support_kind (verbatim_theorem_to_claim t) := by
  intro t
  cases t <;> rfl

theorem PaperVerbatimStructuralTheoremsCertifiedStatement :
  verbatim_theorem_support_kind .standingQuotientFutureBehaviorQuotient = .structurallyCertified /\
  verbatim_theorem_support_kind .noCompetingSameScopeContinuationGates = .structurallyCertified /\
  verbatim_theorem_support_kind .noSecondSameScopeSingularityGate = .structurallyCertified /\
  verbatim_theorem_support_kind .quotientVisibleVsIllicitSingularity = .structurallyCertified /\
  verbatim_theorem_support_kind .structuralRegularityOnTheCertifiedPeriodicCarrier = .structurallyCertified /\
  verbatim_theorem_support_kind .transferFaithfulnessLocalClassicalContinuation = .structurallyCertified /\
  verbatim_theorem_support_kind .constructiveDiagnosticBranchForcingFromBreakdownWitnesses = .structurallyCertified /\
  verbatim_theorem_support_kind .constructiveSingularCandidateExtraction = .structurallyCertified /\
  verbatim_theorem_support_kind .noIllicitSingularImage = .structurallyCertified /\
  verbatim_theorem_support_kind .noQuotientVisibleSingularImage = .structurallyCertified /\
  verbatim_theorem_support_kind .transferImpossibilityNoSingularImageOfTheUniqueAdmissibleInterior = .structurallyCertified := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PaperVerbatimTheoremNamedFailureBoundaryStatement :
  verbatim_theorem_support_kind .pointwiseVortexStretchingGateCollapse = .namedFailureBoundary := by
  rfl

theorem PaperVerbatimTheoremEndpointGapStatement :
  verbatim_theorem_support_kind .officialPeriodicTheoremOnT3 = .analyticDependent /\
  verbatim_theorem_support_kind .noFiniteTimeBlowUpOnTheOfficialPeriodicCarrier = .analyticDependent := by
  exact ⟨rfl, rfl⟩

theorem PaperVerbatimTheoremRegisterInheritsAlignmentStatement :
  forall t : NSVerbatimTheoremEntry,
    verbatim_theorem_support_kind t = .structurallyCertified ->
    inventory_obligation_is_structural
      (section_obligation (claim_section (verbatim_theorem_to_claim t))) := by
  intro t h
  have h' : claim_support_kind (verbatim_theorem_to_claim t) = .structurallyCertified := by
    rw [<- PaperVerbatimTheoremRegisterAgreesWithClaimLedgerStatement t]
    exact h
  exact PaperStructuralClaimLedgerAlignmentStatement (verbatim_theorem_to_claim t) h'

end MaleyLean
