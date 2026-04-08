import MaleyLean.MetaNecessityAdmissibilityCore

namespace MaleyLean

theorem PaperFailureOfIrreversibilityUnderUnconstrainedCompositionStatement
  {Claim State : Type}
  (Sys : IrreversibleDecisionSystem Claim State)
  (standing : State → Claim → Prop)
  (hfail :
    ¬ standing_preserving_invariant Sys standing →
    ¬ irreversibility_defined Sys) :
  ¬ standing_preserving_invariant Sys standing →
  ¬ irreversibility_defined Sys := by
  intro h
  exact hfail h

theorem PaperTemporalAsymmetryAsAdmissibleInteriorArtifactStatement
  {Claim State : Type}
  (Sys : IrreversibleDecisionSystem Claim State)
  (h :
    admissible_interior_supports_reference Sys →
    temporal_asymmetry_artifact Sys) :
  admissible_interior_supports_reference Sys →
  temporal_asymmetry_artifact Sys := by
  intro hs
  exact h hs

theorem PaperNoAggregationLemmaTemporalStatement
  {Q : Type}
  (quantities : List Q)
  (h_nonprimitive :
    ∀ q : Q, q ∈ quantities → ¬ admissible_quantity q)
  (h_recover :
    recovers_temporal_primitivity quantities) :
  False := by
  rcases h_recover with ⟨q, hmem, hq⟩
  exact h_nonprimitive q hmem hq

theorem PaperInformationNonPrimitivityStatement
  {Info : Type}
  (i : Info)
  (h :
    preserves_reference_stability i →
    preserves_redescription_invariant_encoding i →
    ¬ informational_primitive Info i) :
  preserves_reference_stability i →
  preserves_redescription_invariant_encoding i →
  ¬ informational_primitive Info i := by
  intro hRef hEnc
  exact h hRef hEnc

theorem PaperEncodingPresuppositionStatement
  {Info : Type}
  (i : Info)
  (h_info :
    preserves_reference_stability i →
    preserves_redescription_invariant_encoding i →
    ¬ informational_primitive Info i) :
  preserves_reference_stability i →
  preserves_redescription_invariant_encoding i →
  ¬ informational_primitive Info i := by
  intro hRef hEnc
  exact
    PaperInformationNonPrimitivityStatement
      i
      h_info
      hRef
      hEnc

theorem PaperNoRelabelingLemmaInformationalStatement
  {Info Label : Type}
  (i : Info)
  (l : Label)
  (h :
    relabeling_recovers_primitivity i l →
    promoted_to_ontic_status l) :
  relabeling_recovers_primitivity i l →
  promoted_to_ontic_status l := by
  intro hrel
  exact h hrel

theorem PaperStandingConservationConstraintTemporalStatement
  {Boundary : Type}
  (b : Boundary)
  (h :
    global_temporal_boundary_condition b →
    violates_standing_conservation b) :
  global_temporal_boundary_condition b →
  violates_standing_conservation b := by
  intro hb
  exact h hb

theorem PaperMetaNecessityOfAdmissibilityStatement
  {Claim State : Type}
  (Sys : IrreversibleDecisionSystem Claim State)
  (standing : State → Claim → Prop)
  [Decidable (standing_preserving_invariant Sys standing)]
  (hfail :
    ¬ standing_preserving_invariant Sys standing →
    ¬ irreversibility_defined Sys)
  (hdefined : irreversibility_defined Sys) :
  standing_preserving_invariant Sys standing := by
  by_cases hsp : standing_preserving_invariant Sys standing
  · exact hsp
  · exact False.elim ((hfail hsp) hdefined)

theorem PaperRoleInductionStatement
  {Claim State : Type}
  (Sys : IrreversibleDecisionSystem Claim State)
  (h :
    Sys.irreversible_decision →
    Sys.nondegenerate →
    Sys.unrestricted_composition →
    induces_canonical_gate_roles Sys) :
  Sys.irreversible_decision →
  Sys.nondegenerate →
  Sys.unrestricted_composition →
  induces_canonical_gate_roles Sys := by
  intro hirr hnon hcomp
  exact h hirr hnon hcomp

end MaleyLean
