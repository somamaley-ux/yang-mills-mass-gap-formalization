namespace MaleyLean

structure ConfirmationPractice (Report Assertion Target : Type) where
  supports : Report → Assertion → Prop
  locallyComplete : Report → Assertion → Prop
  about : Assertion → Target → Prop
  admissible : Setoid Report

def same_orbit
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (e e' : Report) : Prop :=
  P.admissible.r e e'

def theory_level_confirmed_at
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (e : Report)
  (α : Assertion) : Prop :=
  P.supports e α ∧
  ∃ o : Target,
    P.about α o ∧
    ∀ e' : Report,
      same_orbit P e e' →
      P.supports e' α ∧ P.about α o

def theory_level_confirmed
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (α : Assertion) : Prop :=
  ∃ e : Report, theory_level_confirmed_at P e α

def theory_level_confirmation_possible
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target) : Prop :=
  ∃ α : Assertion, theory_level_confirmed P α

def reference_fixation
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (R : Report → Target) : Prop :=
  ∀ ⦃e e' : Report⦄, same_orbit P e e' → R e = R e'

def orbit_target_fixed_at
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (e : Report)
  (α : Assertion) : Prop :=
  ∃ o : Target,
    ∀ e' : Report,
      same_orbit P e e' →
      P.about α o

def nondegenerate_fixation
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (R : Report → Target) : Prop :=
  reference_fixation P R ∧ ∃ e₁ e₂ : Report, R e₁ ≠ R e₂

def reference_underdetermination
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target) : Prop :=
  ∃ R₁ R₂ : Report → Target,
    reference_fixation P R₁ ∧
    reference_fixation P R₂ ∧
    R₁ ≠ R₂

def support_respects_admissibility
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target) : Prop :=
  ∀ ⦃α : Assertion⦄ ⦃e e' : Report⦄,
    same_orbit P e e' →
    P.supports e α →
    P.supports e' α

def Evidence (Report : Type) := Report → Prop

def assignment_relative
  {Assignment Report Assertion : Type}
  (Δ : Assignment → Evidence Report → Assertion → Bool) : Prop :=
  ∃ A₁ A₂ : Assignment, ∃ E : Evidence Report, ∃ α : Assertion, Δ A₁ E α ≠ Δ A₂ E α

def reference_invariant_discriminator
  {Assignment Report Assertion : Type}
  (admissibleAssignment : Assignment → Prop)
  (Δ : Assignment → Evidence Report → Assertion → Bool) : Prop :=
  ∀ A₁ A₂ : Assignment,
    admissibleAssignment A₁ →
    admissibleAssignment A₂ →
    ∀ E : Evidence Report, ∀ α : Assertion, Δ A₁ E α = Δ A₂ E α

def assignment_sensitive_discriminator
  {Assignment Report Assertion : Type}
  (admissibleAssignment : Assignment → Prop)
  (preservesReportContent : Assignment → Prop)
  (Δ : Assignment → Evidence Report → Assertion → Bool) : Prop :=
  ∀ A₁ A₂ : Assignment,
    admissibleAssignment A₁ →
    admissibleAssignment A₂ →
    preservesReportContent A₁ →
    preservesReportContent A₂ →
    A₁ ≠ A₂ →
    ∃ E : Evidence Report, ∃ α : Assertion, Δ A₁ E α ≠ Δ A₂ E α

def fixation_sensitive_discriminator
  {Report Assertion Target : Type}
  (P : ConfirmationPractice Report Assertion Target)
  (Δ : (Report → Target) → Evidence Report → Assertion → Bool) : Prop :=
  ∀ R₁ R₂ : Report → Target,
    reference_fixation P R₁ →
    reference_fixation P R₂ →
    R₁ ≠ R₂ →
    ∃ E : Evidence Report, ∃ α : Assertion, Δ R₁ E α ≠ Δ R₂ E α

end MaleyLean
