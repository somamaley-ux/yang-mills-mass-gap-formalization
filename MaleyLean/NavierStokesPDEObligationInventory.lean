import MaleyLean.NavierStokesPDEObligationRegister

namespace MaleyLean

/--
Concrete obligation inventory for the primitive-to-PDE Navier--Stokes route.

This file turns the abstract obligation register into a finite named inventory
that can be aligned with manuscript sections. The goal is to separate what is
already structurally controlled by the primitive scaffold from what still
remains analytic, with the vortex-stretching bridge isolated as the named
failure mode.
-/
inductive NSPDEObligation
  | transportConsistency
  | periodicLocalExistence
  | preHorizonWitnessVisibility
  | singularExtractorSoundness
  | restartStableTerminalClosure
  | noTerminalSecondGate
  | vortexStretchingBridgeEstimate
  | endpointRegularityTransfer
  deriving DecidableEq, Repr

def inventory_obligation_is_structural
  (o : NSPDEObligation) : Prop :=
  o = .transportConsistency ∨
  o = .periodicLocalExistence ∨
  o = .preHorizonWitnessVisibility ∨
  o = .singularExtractorSoundness ∨
  o = .restartStableTerminalClosure ∨
  o = .noTerminalSecondGate

def inventory_obligation_is_analytic
  (o : NSPDEObligation) : Prop :=
  o = .vortexStretchingBridgeEstimate ∨
  o = .endpointRegularityTransfer

def inventory_named_failure
  (o : NSPDEObligation) : Prop :=
  o = .vortexStretchingBridgeEstimate

def inventory_endpoint_depends_on_named_failure
  (o : NSPDEObligation) : Prop :=
  o = .endpointRegularityTransfer

def obligation_inventory_complete : Prop :=
  ∀ o : NSPDEObligation,
    inventory_obligation_is_structural o ∨
    inventory_obligation_is_analytic o

def analytic_inventory_reduces_to_named_failure : Prop :=
  ∀ o : NSPDEObligation,
    inventory_obligation_is_analytic o →
    inventory_named_failure o ∨ inventory_endpoint_depends_on_named_failure o

def buildConcreteObligationRegister
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  PDEObligationRegister
      State Time Datum LocalSol History RestartWitness Candidate Quantity Label NSPDEObligation where
  primitive := G
  transportRealization o := o = .transportConsistency
  periodicLocalRealization o := o = .periodicLocalExistence
  horizonWitnessRealization o := o = .preHorizonWitnessVisibility
  singularExtractorRealization o := o = .singularExtractorSoundness
  terminalClosureRealization o := o = .restartStableTerminalClosure
  noSecondGateRealization o := o = .noTerminalSecondGate
  vortexStretchingBridge o := o = .vortexStretchingBridgeEstimate
  analyticFailurePoint o := o = .vortexStretchingBridgeEstimate ∨ o = .endpointRegularityTransfer

theorem PaperObligationInventoryCompleteStatement :
  obligation_inventory_complete := by
  intro o
  cases o
  · exact Or.inl <| Or.inl rfl
  · exact Or.inl <| Or.inr <| Or.inl rfl
  · exact Or.inl <| Or.inr <| Or.inr <| Or.inl rfl
  · exact Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
  · exact Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
  · exact Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
  · exact Or.inr <| Or.inl rfl
  · exact Or.inr <| Or.inr rfl

theorem PaperAnalyticInventoryReducesToNamedFailureStatement :
  analytic_inventory_reduces_to_named_failure := by
  intro o hanalytic
  cases o
  · rcases hanalytic with h | h <;> cases h
  · rcases hanalytic with h | h <;> cases h
  · rcases hanalytic with h | h <;> cases h
  · rcases hanalytic with h | h <;> cases h
  · rcases hanalytic with h | h <;> cases h
  · rcases hanalytic with h | h <;> cases h
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem PaperConcreteRegisterMatchesInventoryStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  primitive_to_pde_obligation_packet (buildConcreteObligationRegister G) := by
  intro o
  cases o
  · exact Or.inl rfl
  · exact Or.inr <| Or.inl rfl
  · exact Or.inr <| Or.inr <| Or.inl rfl
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr rfl

theorem PaperConcreteRegisterHasNamedFailureStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  vortex_stretching_named_failure (buildConcreteObligationRegister G) := by
  refine ⟨.vortexStretchingBridgeEstimate, ?_, ?_⟩
  · rfl
  · exact Or.inl rfl

theorem PaperConcreteRegisterReducesAnalyticBurdenStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (_hboundary : primitive_no_blowup_boundary G) :
  ∀ o : NSPDEObligation,
    (buildConcreteObligationRegister G).analyticFailurePoint o →
    (buildConcreteObligationRegister G).vortexStretchingBridge o ∨
    inventory_endpoint_depends_on_named_failure o := by
  intro o hanalytic
  cases o
  · rcases hanalytic with h | h <;> cases h
  · rcases hanalytic with h | h <;> cases h
  · rcases hanalytic with h | h <;> cases h
  · rcases hanalytic with h | h <;> cases h
  · rcases hanalytic with h | h <;> cases h
  · rcases hanalytic with h | h <;> cases h
  · exact Or.inl rfl
  · exact Or.inr rfl

end MaleyLean
