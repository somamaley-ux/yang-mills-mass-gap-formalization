import MaleyLean.NavierStokesVerbatimTheoremRegister
import MaleyLean.NavierStokesPDEObligationInventory

namespace MaleyLean

/--
Simple verbatim dependency spine for the current Navier--Stokes manuscript
bundle.

This file records the manuscript-facing dependency split over actual theorem
titles: structurally closed titles, the named vortex-stretching failure title,
and the endpoint titles that remain downstream of that named failure.
-/
def verbatim_theorem_obligation_simple
  (t : NSVerbatimTheoremEntry) : NSPDEObligation :=
  match t with
  | .standingQuotientFutureBehaviorQuotient => .transportConsistency
  | .noCompetingSameScopeContinuationGates => .noTerminalSecondGate
  | .pointwiseVortexStretchingGateCollapse => .vortexStretchingBridgeEstimate
  | .noSecondSameScopeSingularityGate => .noTerminalSecondGate
  | .quotientVisibleVsIllicitSingularity => .singularExtractorSoundness
  | .structuralRegularityOnTheCertifiedPeriodicCarrier => .restartStableTerminalClosure
  | .transferFaithfulnessLocalClassicalContinuation => .transportConsistency
  | .constructiveDiagnosticBranchForcingFromBreakdownWitnesses => .preHorizonWitnessVisibility
  | .constructiveSingularCandidateExtraction => .singularExtractorSoundness
  | .noIllicitSingularImage => .singularExtractorSoundness
  | .noQuotientVisibleSingularImage => .singularExtractorSoundness
  | .transferImpossibilityNoSingularImageOfTheUniqueAdmissibleInterior => .restartStableTerminalClosure
  | .officialPeriodicTheoremOnT3 => .endpointRegularityTransfer
  | .noFiniteTimeBlowUpOnTheOfficialPeriodicCarrier => .endpointRegularityTransfer

def verbatim_theorem_is_structurally_closed_simple
  (t : NSVerbatimTheoremEntry) : Prop :=
  inventory_obligation_is_structural (verbatim_theorem_obligation_simple t)

def verbatim_theorem_is_named_failure_boundary_simple
  (t : NSVerbatimTheoremEntry) : Prop :=
  inventory_named_failure (verbatim_theorem_obligation_simple t)

def verbatim_theorem_is_endpoint_downstream_simple
  (t : NSVerbatimTheoremEntry) : Prop :=
  inventory_endpoint_depends_on_named_failure (verbatim_theorem_obligation_simple t)

theorem PaperVerbatimStructuralTitlesClosedSimpleStatement :
  verbatim_theorem_is_structurally_closed_simple .standingQuotientFutureBehaviorQuotient /\
  verbatim_theorem_is_structurally_closed_simple .noCompetingSameScopeContinuationGates /\
  verbatim_theorem_is_structurally_closed_simple .noSecondSameScopeSingularityGate /\
  verbatim_theorem_is_structurally_closed_simple .quotientVisibleVsIllicitSingularity /\
  verbatim_theorem_is_structurally_closed_simple .structuralRegularityOnTheCertifiedPeriodicCarrier /\
  verbatim_theorem_is_structurally_closed_simple .transferFaithfulnessLocalClassicalContinuation /\
  verbatim_theorem_is_structurally_closed_simple .constructiveDiagnosticBranchForcingFromBreakdownWitnesses /\
  verbatim_theorem_is_structurally_closed_simple .constructiveSingularCandidateExtraction /\
  verbatim_theorem_is_structurally_closed_simple .noIllicitSingularImage /\
  verbatim_theorem_is_structurally_closed_simple .noQuotientVisibleSingularImage /\
  verbatim_theorem_is_structurally_closed_simple .transferImpossibilityNoSingularImageOfTheUniqueAdmissibleInterior := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem PaperVerbatimNamedFailureTitleSimpleStatement :
  verbatim_theorem_is_named_failure_boundary_simple .pointwiseVortexStretchingGateCollapse := by
  rfl

theorem PaperVerbatimEndpointTitlesSimpleStatement :
  verbatim_theorem_is_endpoint_downstream_simple .officialPeriodicTheoremOnT3 /\
  verbatim_theorem_is_endpoint_downstream_simple .noFiniteTimeBlowUpOnTheOfficialPeriodicCarrier := by
  exact ⟨rfl, rfl⟩

theorem PaperVerbatimSupportDependencyAlignmentSimpleStatement :
  (verbatim_theorem_support_kind .pointwiseVortexStretchingGateCollapse = .namedFailureBoundary ->
    verbatim_theorem_is_named_failure_boundary_simple .pointwiseVortexStretchingGateCollapse) /\
  (verbatim_theorem_support_kind .officialPeriodicTheoremOnT3 = .analyticDependent ->
    verbatim_theorem_is_endpoint_downstream_simple .officialPeriodicTheoremOnT3) /\
  (verbatim_theorem_support_kind .noFiniteTimeBlowUpOnTheOfficialPeriodicCarrier = .analyticDependent ->
    verbatim_theorem_is_endpoint_downstream_simple .noFiniteTimeBlowUpOnTheOfficialPeriodicCarrier) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact rfl
  · intro _
    exact rfl
  · intro _
    exact rfl

end MaleyLean
