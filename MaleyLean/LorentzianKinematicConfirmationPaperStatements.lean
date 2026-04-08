import MaleyLean.LorentzianKinematicConfirmationCore

namespace MaleyLean

theorem PaperNonLorentzAdmissibleKinematicsInducesFrameRelativeClaimsStatement
  {Report KinematicAssertion Frame : Type}
  (P : KinematicConfirmationPractice Report KinematicAssertion Frame)
  (h :
    ¬ P.lorentzAdmissible →
    ∃ e : Report, ∃ K K' : KinematicAssertion, ∃ f g : Frame,
      frame_relative_support P e K K' f g) :
  ¬ P.lorentzAdmissible →
  ∃ e : Report, ∃ K K' : KinematicAssertion, ∃ f g : Frame,
    frame_relative_support P e K K' f g := by
  intro hnot
  exact h hnot

theorem PaperFrameRelativeSupportIsNotTheoryLevelKinematicConfirmationStatement
  {Report KinematicAssertion Frame : Type}
  (P : KinematicConfirmationPractice Report KinematicAssertion Frame)
  (K : KinematicAssertion)
  (h :
    (∃ e : Report, ∃ K' : KinematicAssertion, ∃ f g : Frame,
      frame_relative_support P e K K' f g) →
    ¬ frame_robustly_confirmed P K) :
  (∃ e : Report, ∃ K' : KinematicAssertion, ∃ f g : Frame,
    frame_relative_support P e K K' f g) →
  ¬ frame_robustly_confirmed P K := by
  intro hrel
  exact h hrel

theorem PaperFixationLocalityOfFrameChangeStatement
  {Report KinematicAssertion Frame : Type}
  (P : KinematicConfirmationPractice Report KinematicAssertion Frame)
  (f g : Frame)
  (_h : P.frameRedescription f g) :
  internal_frame_redescription P f g := by
  trivial

theorem PaperLorentzianAdmissibilityAsEnablingConditionStatement
  {Report KinematicAssertion Frame : Type}
  (P : KinematicConfirmationPractice Report KinematicAssertion Frame)
  (K : KinematicAssertion)
  [Decidable P.lorentzAdmissible]
  (_hfinite : P.finiteSignalAssertion K)
  (h_rel :
    ¬ P.lorentzAdmissible →
    ∃ e : Report, ∃ K' : KinematicAssertion, ∃ f g : Frame,
      frame_relative_support P e K K' f g)
  (h_not_conf :
    (∃ e : Report, ∃ K' : KinematicAssertion, ∃ f g : Frame,
      frame_relative_support P e K K' f g) →
    ¬ frame_robustly_confirmed P K)
  (hconf : frame_robustly_confirmed P K) :
  P.lorentzAdmissible := by
  by_cases hlor : P.lorentzAdmissible
  · exact hlor
  · have hrelw : ∃ e : Report, ∃ K' : KinematicAssertion, ∃ f g : Frame,
        frame_relative_support P e K K' f g :=
      h_rel hlor
    exact False.elim ((h_not_conf hrelw) hconf)

theorem PaperPreferredFrameFailureModeStatement
  {Report KinematicAssertion Frame : Type}
  (P : KinematicConfirmationPractice Report KinematicAssertion Frame)
  (K : KinematicAssertion)
  (h :
    (∃ f : Frame, P.privilegedFrameRequired f) →
    ¬ frame_robustly_confirmed P K) :
  (∃ f : Frame, P.privilegedFrameRequired f) →
  ¬ frame_robustly_confirmed P K := by
  intro hpref
  exact h hpref

theorem PaperIdlePreferredStructurePermittedStatement
  {Report KinematicAssertion Frame : Type}
  (P : KinematicConfirmationPractice Report KinematicAssertion Frame)
  (h :
    (∀ f : Frame, ¬ P.privilegedFrameRequired f) →
    P.lorentzAdmissible) :
  (∀ f : Frame, ¬ P.privilegedFrameRequired f) →
  P.lorentzAdmissible := by
  intro hidle
  exact h hidle

theorem PaperDeformedKinematicsClassificationStatement
  {Report KinematicAssertion Frame : Type}
  (P : KinematicConfirmationPractice Report KinematicAssertion Frame)
  (K : KinematicAssertion)
  (h :
    (∃ e : Report, ∃ K' : KinematicAssertion, ∃ f g : Frame,
      frame_relative_support P e K K' f g) →
    ¬ frame_robustly_confirmed P K) :
  (∃ e : Report, ∃ K' : KinematicAssertion, ∃ f g : Frame,
    frame_relative_support P e K K' f g) →
  ¬ frame_robustly_confirmed P K := by
  intro hrel
  exact h hrel

theorem PaperEmergentKinematicsClassificationStatement
  {Report KinematicAssertion Frame : Type}
  (P : KinematicConfirmationPractice Report KinematicAssertion Frame)
  (K : KinematicAssertion)
  (h :
    P.lorentzAdmissible →
    frame_robustly_confirmed P K) :
  P.lorentzAdmissible →
  frame_robustly_confirmed P K := by
  intro hlor
  exact h hlor

end MaleyLean
