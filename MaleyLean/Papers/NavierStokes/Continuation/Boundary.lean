import MaleyLean.Papers.NavierStokes.Primitive.QuotientFactorization

namespace MaleyLean

/--
Continuation-boundary packet for the primitive Navier--Stokes route.

This file sharpens the quotient layer by isolating two boundary objects:
continuation discriminators and singular-candidate extractors. The point is
to state, at the primitive level, that neither may introduce a hidden second
gate once same-scope quotient identity has been fixed.
-/
structure ContinuationBoundarySystem
    (State Time History Witness Candidate Quantity Label : Type) where
  history : SameScopeHistorySystem State Time History Witness Quantity
  continuationLabel : History → Label
  singularExtractor : History → Option Candidate
  continuationRelevant : Label → Prop
  extractorSameScope : Candidate → Prop

def continuation_relevance_respects_quotient
  {State Time History Witness Candidate Quantity Label : Type}
  (B : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label) :
  Prop :=
  same_scope_discriminator B.history B.continuationLabel

def singular_extractor_respects_quotient
  {State Time History Witness Candidate Quantity Label : Type}
  (B : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label) :
  Prop :=
  ∀ h₁ h₂ : History,
    future_behavior_equiv B.history h₁ h₂ →
    B.singularExtractor h₁ = B.singularExtractor h₂

def extractor_outputs_same_scope
  {State Time History Witness Candidate Quantity Label : Type}
  (B : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label) :
  Prop :=
  ∀ h : History, ∀ c : Candidate,
    B.singularExtractor h = some c →
    B.extractorSameScope c

def continuation_boundary_closed
  {State Time History Witness Candidate Quantity Label : Type}
  (B : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label) :
  Prop :=
  continuation_relevance_respects_quotient B ∧
  singular_extractor_respects_quotient B ∧
  extractor_outputs_same_scope B

def singular_extractor_cannot_reintroduce_second_gate
  {State Time History Witness Candidate Quantity Label : Type}
  (B : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label) :
  Prop :=
  singular_extractor_respects_quotient B

theorem PaperContinuationRelevanceFactorsThroughQuotientStatement
  {State Time History Witness Candidate Quantity Label : Type}
  (B : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label)
  (h :
    ∀ h₁ h₂ : History,
      future_behavior_equiv B.history h₁ h₂ →
      B.continuationLabel h₁ = B.continuationLabel h₂) :
  continuation_relevance_respects_quotient B := by
  exact h

theorem PaperSingularExtractorFactorsThroughQuotientStatement
  {State Time History Witness Candidate Quantity Label : Type}
  (B : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label)
  (h :
    ∀ h₁ h₂ : History,
      future_behavior_equiv B.history h₁ h₂ →
      B.singularExtractor h₁ = B.singularExtractor h₂) :
  singular_extractor_respects_quotient B := by
  exact h

theorem PaperExtractorOutputsSameScopeStatement
  {State Time History Witness Candidate Quantity Label : Type}
  (B : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label)
  (h :
    ∀ h : History, ∀ c : Candidate,
      B.singularExtractor h = some c →
      B.extractorSameScope c) :
  extractor_outputs_same_scope B := by
  exact h

theorem PaperSingularExtractorNoSecondGateStatement
  {State Time History Witness Candidate Quantity Label : Type}
  (B : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label)
  (h :
    ∀ h₁ h₂ : History,
      future_behavior_equiv B.history h₁ h₂ →
      B.singularExtractor h₁ = B.singularExtractor h₂) :
  singular_extractor_cannot_reintroduce_second_gate B := by
  exact h

theorem PaperContinuationBoundaryClosedStatement
  {State Time Datum LocalSol History Witness Candidate Quantity Label : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol Witness)
  (H : SameScopeHistorySystem State Time History Witness Quantity)
  (B : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label)
  (_h_packet :
    datum_entry_to_admitted_carrier S L ∧
    local_realization_on_carrier S L ∧
    restart_consistency_same_object_persistence S L ∧
    pre_horizon_slice_reentry S L ∧
    finite_horizon_witness_visibility S L)
  (_h_no_second_gate : no_second_gate_same_scope H B.continuationLabel)
  (h_cont :
    ∀ h₁ h₂ : History,
      future_behavior_equiv B.history h₁ h₂ →
      B.continuationLabel h₁ = B.continuationLabel h₂)
  (h_extract :
    ∀ h₁ h₂ : History,
      future_behavior_equiv B.history h₁ h₂ →
      B.singularExtractor h₁ = B.singularExtractor h₂)
  (h_scope :
    ∀ h : History, ∀ c : Candidate,
      B.singularExtractor h = some c →
      B.extractorSameScope c) :
  continuation_boundary_closed B := by
  exact ⟨h_cont, h_extract, h_scope⟩

end MaleyLean
