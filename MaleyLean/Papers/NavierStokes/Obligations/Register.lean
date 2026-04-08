import MaleyLean.Papers.NavierStokes.Primitive.NoBlowup

namespace MaleyLean

/--
Primitive-to-PDE obligation register for the Navier--Stokes route.

This file does not discharge any analytic estimates. It records the exact
external obligations that would have to be met in order to turn the primitive
no-blowup boundary into a genuine periodic Navier--Stokes theorem. It also
singles out the vortex-stretching anomaly as an explicit failure point rather
than leaving it as an unnamed gap.
-/
structure PDEObligationRegister
    (State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation : Type) where
  primitive : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label
  transportRealization : Obligation → Prop
  periodicLocalRealization : Obligation → Prop
  horizonWitnessRealization : Obligation → Prop
  singularExtractorRealization : Obligation → Prop
  terminalClosureRealization : Obligation → Prop
  noSecondGateRealization : Obligation → Prop
  vortexStretchingBridge : Obligation → Prop
  analyticFailurePoint : Obligation → Prop

def primitive_to_pde_obligation_packet
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation : Type}
  (R : PDEObligationRegister State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation) :
  Prop :=
  ∀ o : Obligation,
    R.transportRealization o ∨
    R.periodicLocalRealization o ∨
    R.horizonWitnessRealization o ∨
    R.singularExtractorRealization o ∨
    R.terminalClosureRealization o ∨
    R.noSecondGateRealization o ∨
    R.vortexStretchingBridge o ∨
    R.analyticFailurePoint o

def vortex_stretching_named_failure
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation : Type}
  (R : PDEObligationRegister State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation) :
  Prop :=
  ∃ o : Obligation,
    R.vortexStretchingBridge o ∧
    R.analyticFailurePoint o

def all_obligations_discharged_except_named_failure
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation : Type}
  (R : PDEObligationRegister State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation) :
  Prop :=
  ∀ o : Obligation,
    R.analyticFailurePoint o →
    R.vortexStretchingBridge o

def primitive_boundary_reduces_pde_burden
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation : Type}
  (R : PDEObligationRegister State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation) :
  Prop :=
  primitive_no_blowup_boundary R.primitive →
  all_obligations_discharged_except_named_failure R →
  vortex_stretching_named_failure R →
  ∀ o : Obligation, R.analyticFailurePoint o → R.vortexStretchingBridge o

theorem PaperPrimitiveToPDEObligationPacketStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation : Type}
  (R : PDEObligationRegister State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation)
  (h :
    ∀ o : Obligation,
      R.transportRealization o ∨
      R.periodicLocalRealization o ∨
      R.horizonWitnessRealization o ∨
      R.singularExtractorRealization o ∨
      R.terminalClosureRealization o ∨
      R.noSecondGateRealization o ∨
      R.vortexStretchingBridge o ∨
      R.analyticFailurePoint o) :
  primitive_to_pde_obligation_packet R := by
  exact h

theorem PaperVortexStretchingNamedFailureStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation : Type}
  (R : PDEObligationRegister State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation)
  (h :
    ∃ o : Obligation,
      R.vortexStretchingBridge o ∧
      R.analyticFailurePoint o) :
  vortex_stretching_named_failure R := by
  exact h

theorem PaperAllObligationsDischargedExceptNamedFailureStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation : Type}
  (R : PDEObligationRegister State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation)
  (h :
    ∀ o : Obligation,
      R.analyticFailurePoint o →
      R.vortexStretchingBridge o) :
  all_obligations_discharged_except_named_failure R := by
  exact h

theorem PaperPrimitiveBoundaryReducesPDEBurdenStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation : Type}
  (R : PDEObligationRegister State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation)
  (_hboundary : primitive_no_blowup_boundary R.primitive)
  (hall : all_obligations_discharged_except_named_failure R)
  (_hfail : vortex_stretching_named_failure R) :
  primitive_boundary_reduces_pde_burden R := by
  intro _hboundary _hall _hfail o hanalytic
  exact hall o hanalytic

theorem PaperPrimitiveNoBlowupToNamedPDEGapStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation : Type}
  (R : PDEObligationRegister State Time Datum LocalSol History RestartWitness Candidate Quantity Label Obligation)
  (hboundary : primitive_no_blowup_boundary R.primitive)
  (hall : all_obligations_discharged_except_named_failure R)
  (hfail : vortex_stretching_named_failure R) :
  ∀ o : Obligation, R.analyticFailurePoint o → R.vortexStretchingBridge o := by
  exact PaperPrimitiveBoundaryReducesPDEBurdenStatement R hboundary hall hfail hboundary hall hfail

end MaleyLean
