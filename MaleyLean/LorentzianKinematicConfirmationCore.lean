namespace MaleyLean

/--
Lightweight core for the paper
"Lorentzian Admissibility as a Condition for Kinematic Confirmation".

This file specializes the general confirmation/fixation pattern to frame-robust
kinematic confirmation. The goal is to capture the theorem spine: frame-local
support, frame-robust confirmation, Lorentz-admissibility, and the failure of
theory-level confirmation when frame change forces retargeting.
-/
structure KinematicConfirmationPractice
    (Report KinematicAssertion Frame : Type) where
  supportsInFrame : Report → KinematicAssertion → Frame → Prop
  transport : Frame → Report → Report
  frameRedescription : Frame → Frame → Prop
  sameTheoryLevelClaim : KinematicAssertion → KinematicAssertion → Prop
  finiteSignalAssertion : KinematicAssertion → Prop
  lorentzAdmissible : Prop
  privilegedFrameRequired : Frame → Prop

def frame_robustly_confirmed
  {Report KinematicAssertion Frame : Type}
  (P : KinematicConfirmationPractice Report KinematicAssertion Frame)
  (K : KinematicAssertion) : Prop :=
  ∃ e : Report, ∃ f : Frame,
    P.supportsInFrame e K f ∧
    ∀ g : Frame,
      P.frameRedescription f g →
      P.supportsInFrame (P.transport g e) K g

def frame_relative_support
  {Report KinematicAssertion Frame : Type}
  (P : KinematicConfirmationPractice Report KinematicAssertion Frame)
  (e : Report)
  (K K' : KinematicAssertion)
  (f g : Frame) : Prop :=
  P.supportsInFrame e K f ∧
  P.frameRedescription f g ∧
  P.supportsInFrame (P.transport g e) K' g ∧
  ¬ P.sameTheoryLevelClaim K K'

def internal_frame_redescription
  {Report KinematicAssertion Frame : Type}
  (_P : KinematicConfirmationPractice Report KinematicAssertion Frame)
  (_f _g : Frame) : Prop :=
  True

end MaleyLean
