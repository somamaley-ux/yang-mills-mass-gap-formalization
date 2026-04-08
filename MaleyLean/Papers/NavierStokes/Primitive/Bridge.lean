import MaleyLean.Papers.NavierStokes.Primitive.Core

namespace MaleyLean

theorem PaperCarrierToLineageBindingStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (hrealized : S.lineage.realized)
  (hmax : S.lineage.maximal)
  (hscope : S.carrier.fixedScope) :
  carrier_to_lineage_binding S := by
  exact ⟨hrealized, hmax, hscope⟩

theorem PaperStandingPositiveLineageStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (h :
    ∀ t : Time,
      S.sameScopeContinuation t →
      S.standing (S.lineage.stateAt t)) :
  standing_positive_lineage S := by
  exact h

theorem PaperNoAdmissibilityDynamicsStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (h :
    ∀ t₁ t₂ : Time,
      S.sameScopeContinuation t₁ →
      S.sameScopeContinuation t₂ →
      (S.standing (S.lineage.stateAt t₁) ↔ S.standing (S.lineage.stateAt t₂))) :
  no_admissibility_dynamics S := by
  exact h

theorem PaperPreHorizonWitnessStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (h :
    ∃ t : Time, S.sameScopeContinuation t ∧
      ∃ w : Witness,
        S.horizonWitness.carrierVisible w ∧
        S.horizonWitness.quotientVisible w ∧
        S.horizonWitness.horizonBearing w) :
  pre_horizon_witness_exists S := by
  exact h

theorem PaperSingularCandidateTypingStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (h :
    ∃ t : Time, S.sameScopeContinuation t ∧
      ∃ c : Candidate,
        S.singularCandidate.carrierVisible c ∧
        S.singularCandidate.sameScope c) :
  singular_image_same_scope S := by
  exact h

theorem PaperMetricDivergenceSkinNonAuthorityStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (h :
    ∀ q : Quantity,
      S.metricQuantity q →
      S.quotientVisibleWitnessBookkeeping q ∨ ¬ S.illicitMetricGate q) :
  metric_divergence_skin_only S := by
  exact h

theorem PaperQuotientVisibleWitnessVsIllicitMetricGateStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (q : Quantity)
  (hq : S.metricQuantity q)
  (hskin : metric_divergence_skin_only S) :
  S.quotientVisibleWitnessBookkeeping q ∨ ¬ S.illicitMetricGate q := by
  exact hskin q hq

theorem PaperVortexStretchingAnomalyBoundaryStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (hanom : vortex_stretching_anomaly_boundary S) :
  ∃ q : Quantity,
    S.metricQuantity q ∧
    ¬ S.quotientVisibleWitnessBookkeeping q ∧
    S.illicitMetricGate q := by
  exact hanom

theorem PaperPrimitiveToPDEBridgeBoundaryStatement
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (hskin : metric_divergence_skin_only S)
  (hanom : vortex_stretching_anomaly_boundary S) :
  False := by
  rcases hanom with ⟨q, hmetric, hnotbook, hillicit⟩
  rcases hskin q hmetric with hbook | hnotgate
  · exact hnotbook hbook
  · exact hnotgate hillicit

end MaleyLean
