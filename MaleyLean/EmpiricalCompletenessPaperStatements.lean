import MaleyLean.EmpiricalCompletenessCore

namespace MaleyLean

theorem PaperTargetIdentityFromStabilityStatement
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (e : Report)
  (α : Assertion)
  (hconf : theory_level_confirmed_at P e α) :
  ∃ o : Target,
    ∀ e' : Report,
      same_orbit P e e' →
      P.supports e' α ∧ P.about α o := by
  rcases hconf with ⟨_, o, ho, hstable⟩
  exact ⟨o, fun e' hEq => hstable e' hEq⟩

theorem PaperOrbitFixationFromConfirmationStatement
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (e : Report)
  (α : Assertion)
  (hconf : theory_level_confirmed_at P e α) :
  orbit_target_fixed_at P e α := by
  rcases hconf with ⟨_, o, ho, hstable⟩
  exact ⟨o, fun e' hEq => (hstable e' hEq).2⟩

theorem PaperNonFixedReferenceBlocksTheoryLevelConfirmationStatement
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (hno : ∀ e : Report, ∀ α : Assertion, ¬ orbit_target_fixed_at P e α) :
  ∀ α : Assertion, ¬ theory_level_confirmed P α := by
  intro α hα
  rcases hα with ⟨e, hconf⟩
  exact hno e α (PaperOrbitFixationFromConfirmationStatement P e α hconf)

theorem PaperCompletenessDoesNotSubstituteForFixationStatement
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (hno : ∀ e : Report, ∀ α : Assertion, ¬ orbit_target_fixed_at P e α) :
  ∀ e : Report, ∀ α : Assertion,
    P.locallyComplete e α →
    ¬ theory_level_confirmed_at P e α := by
  intro e α _hcomplete hconf
  have hblocked :=
    PaperNonFixedReferenceBlocksTheoryLevelConfirmationStatement P hno α
  exact hblocked ⟨e, hconf⟩

theorem PaperAdmissibleFixationEnablesTheoryLevelConfirmationStatement
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (R : Report → Target)
  (hfix : reference_fixation P R)
  (hsupp : support_respects_admissibility P)
  (e : Report)
  (α : Assertion)
  (h_support : P.supports e α)
  (h_about : P.about α (R e)) :
  theory_level_confirmed_at P e α := by
  refine ⟨h_support, R e, h_about, ?_⟩
  intro e' heq
  constructor
  · exact hsupp heq h_support
  · have hRe : R e = R e' := hfix heq
    simpa [hRe] using h_about

theorem PaperTheoryLevelConfirmationPossibleFromFixationStatement
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (R : Report → Target)
  (hfix : reference_fixation P R)
  (hsupp : support_respects_admissibility P)
  (hw : ∃ e : Report, ∃ α : Assertion, P.supports e α ∧ P.about α (R e)) :
  theory_level_confirmation_possible P := by
  rcases hw with ⟨e, α, hsupport, habout⟩
  refine ⟨α, e, ?_⟩
  exact
    PaperAdmissibleFixationEnablesTheoryLevelConfirmationStatement
      P R hfix hsupp e α hsupport habout

theorem PaperAssignmentRelativityFromMultipleAdmissibleAssignmentsStatement
  {Assignment Report Assertion : Type}
  (admissibleAssignment : Assignment → Prop)
  (preservesReportContent : Assignment → Prop)
  (Δ : Assignment → Evidence Report → Assertion → Bool)
  (hsensitive :
    assignment_sensitive_discriminator
      admissibleAssignment
      preservesReportContent
      Δ)
  (A₁ A₂ : Assignment)
  (ha₁ : admissibleAssignment A₁)
  (ha₂ : admissibleAssignment A₂)
  (hp₁ : preservesReportContent A₁)
  (hp₂ : preservesReportContent A₂)
  (hne : A₁ ≠ A₂) :
  ∃ E : Evidence Report, ∃ α : Assertion, Δ A₁ E α ≠ Δ A₂ E α := by
  exact hsensitive A₁ A₂ ha₁ ha₂ hp₁ hp₂ hne

theorem PaperConfirmationCollapseAssignmentStatement
  {Assignment Report Assertion : Type}
  (admissibleAssignment : Assignment → Prop)
  (preservesReportContent : Assignment → Prop)
  (Δ : Assignment → Evidence Report → Assertion → Bool)
  (hsensitive :
    assignment_sensitive_discriminator
      admissibleAssignment
      preservesReportContent
      Δ)
  (A₁ A₂ : Assignment)
  (ha₁ : admissibleAssignment A₁)
  (ha₂ : admissibleAssignment A₂)
  (hp₁ : preservesReportContent A₁)
  (hp₂ : preservesReportContent A₂)
  (hne : A₁ ≠ A₂) :
  ¬ reference_invariant_discriminator admissibleAssignment Δ := by
  intro hinv
  rcases
    PaperAssignmentRelativityFromMultipleAdmissibleAssignmentsStatement
      admissibleAssignment
      preservesReportContent
      Δ
      hsensitive
      A₁
      A₂
      ha₁
      ha₂
      hp₁
      hp₂
      hne with ⟨E, α, hneq⟩
  exact hneq (hinv A₁ A₂ ha₁ ha₂ E α)

theorem PaperAssignmentRelativityOfConfirmationJudgmentsStatement
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (Δ : (Report → Target) → Evidence Report → Assertion → Bool)
  (hsensitive : fixation_sensitive_discriminator P Δ)
  (hunder : reference_underdetermination P) :
  assignment_relative Δ := by
  rcases hunder with ⟨R₁, R₂, hfix₁, hfix₂, hne⟩
  rcases hsensitive R₁ R₂ hfix₁ hfix₂ hne with ⟨E, α, hneq⟩
  exact ⟨R₁, R₂, E, α, hneq⟩

theorem PaperConfirmationCollapseDiscriminatorFailureStatement
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (Δ : (Report → Target) → Evidence Report → Assertion → Bool)
  (hsensitive : fixation_sensitive_discriminator P Δ)
  (hunder : reference_underdetermination P) :
  ¬ reference_invariant_discriminator (reference_fixation P) Δ := by
  intro hinv
  rcases hunder with ⟨R₁, R₂, hfix₁, hfix₂, hne⟩
  rcases hsensitive R₁ R₂ hfix₁ hfix₂ hne with ⟨E, α, hneq⟩
  exact hneq (hinv R₁ R₂ hfix₁ hfix₂ E α)

theorem PaperGaugeRedundancyIsNotReferenceUnderdeterminationStatement
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (R : Report → Target)
  (_hfix : reference_fixation P R)
  (huniq : ∀ R' : Report → Target, reference_fixation P R' → R' = R) :
  ¬ reference_underdetermination P := by
  intro hunder
  rcases hunder with ⟨R₁, R₂, hfix₁, hfix₂, hne⟩
  have h₁ : R₁ = R := huniq R₁ hfix₁
  have h₂ : R₂ = R := huniq R₂ hfix₂
  apply hne
  calc
    R₁ = R := h₁
    _ = R₂ := h₂.symm

end MaleyLean
