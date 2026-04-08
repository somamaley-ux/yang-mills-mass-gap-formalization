import MaleyLean.ClaimModalityPaperCore

namespace MaleyLean

theorem PaperScopeAlignmentStatement
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality)
  (c : Claim)
  (σ : Scope)
  (h : S.admissibleModality c σ (S.assertedModality c)) :
  scope_alignment S c σ := by
  exact h

theorem PaperRedescriptionMonotonicityStatement
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality)
  (h :
    ∀ c : Claim, ∀ σ σ' : Scope,
      S.weakensTo σ σ' →
      S.admissibleModality c σ (S.assertedModality c) →
      S.weakerOrEqual (S.assertedModality c) (S.assertedModality c)) :
  redescription_monotonicity S := by
  exact h

theorem PaperNonAmplificationStatement
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality)
  (h :
    ∀ c : Claim, ∀ σ σ' : Scope,
      S.weakensTo σ σ' →
      ¬ S.weakerOrEqual (S.assertedModality c) (S.assertedModality c) →
      False) :
  non_amplification S := by
  exact h

theorem PaperFailClosedBehaviorStatement
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality)
  (h :
    ∀ c : Claim, ∀ σ : Scope,
      ¬ S.admissibleScope σ →
      S.admissibleModality c σ (S.assertedModality c) → False) :
  fail_closed_behavior S := by
  exact h

theorem PaperModalOverreachInducesStandingFailureStatement
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality)
  (c : Claim)
  (σ σ' : Scope)
  (h :
    modal_overreach S c σ σ' →
    ¬ S.standing c) :
  modal_overreach S c σ σ' →
  ¬ S.standing c := by
  intro hover
  exact h hover

theorem PaperModalOverreachIsNotErrorStatement
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality)
  (c : Claim)
  (σ σ' : Scope)
  (h :
    modal_overreach S c σ σ' →
    ¬ S.error c) :
  modal_overreach S c σ σ' →
  ¬ S.error c := by
  intro hover
  exact h hover

theorem PaperModalityConstraintNecessityStatement
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality)
  (h_overreach :
    unrestricted_assertion_force S →
    ∃ c : Claim, ∃ σ σ' : Scope, modal_overreach S c σ σ' ∧ S.standing c)
  (h_failure :
    ∀ c : Claim, ∀ σ σ' : Scope,
      modal_overreach S c σ σ' →
      ¬ S.standing c) :
  ¬ unrestricted_assertion_force S := by
  intro hunrestricted
  rcases h_overreach hunrestricted with ⟨c, σ, σ', hover, hstand⟩
  exact (h_failure c σ σ' hover) hstand

theorem PaperClaimModalityGateJustificationStatement
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality)
  (h :
    permits_assertion S →
    redescription_monotonicity S →
    fail_closed_behavior S →
    induces_claim_modality_gate S) :
  permits_assertion S →
  redescription_monotonicity S →
  fail_closed_behavior S →
  induces_claim_modality_gate S := by
  intro hp hm hf
  exact h hp hm hf

end MaleyLean
