import MaleyLean.Papers.NavierStokes.Obligations.Inventory

namespace MaleyLean

/--
Paper-facing obligation ledger for the primitive Navier--Stokes route.

This file aligns manuscript-level section families with the concrete PDE
obligation inventory. The result is a section-by-section closure map showing
which parts are already structurally covered by the primitive scaffold and
which parts remain on the analytic side.
-/
inductive NSPaperSection
  | primitiveCarrierSection
  | periodicLocalTheorySection
  | horizonWitnessSection
  | singularExtractorSection
  | restartTransportSection
  | maximalLineageClosureSection
  | noSecondGateSection
  | vortexStretchingAnomalySection
  | endpointTransferSection
  deriving DecidableEq, Repr

def section_obligation
  (s : NSPaperSection) : NSPDEObligation :=
  match s with
  | .primitiveCarrierSection => .transportConsistency
  | .periodicLocalTheorySection => .periodicLocalExistence
  | .horizonWitnessSection => .preHorizonWitnessVisibility
  | .singularExtractorSection => .singularExtractorSoundness
  | .restartTransportSection => .restartStableTerminalClosure
  | .maximalLineageClosureSection => .restartStableTerminalClosure
  | .noSecondGateSection => .noTerminalSecondGate
  | .vortexStretchingAnomalySection => .vortexStretchingBridgeEstimate
  | .endpointTransferSection => .endpointRegularityTransfer

abbrev section_is_structurally_closed
  (s : NSPaperSection) : Prop :=
  inventory_obligation_is_structural (section_obligation s)

abbrev section_requires_analytic_bridge
  (s : NSPaperSection) : Prop :=
  inventory_obligation_is_analytic (section_obligation s)

abbrev section_is_named_failure_boundary
  (s : NSPaperSection) : Prop :=
  inventory_named_failure (section_obligation s)

abbrev section_depends_on_named_failure
  (s : NSPaperSection) : Prop :=
  inventory_endpoint_depends_on_named_failure (section_obligation s)

abbrev paper_obligation_ledger_complete : Prop :=
  ∀ s : NSPaperSection,
    section_is_structurally_closed s ∨
    section_requires_analytic_bridge s

abbrev paper_analytic_sections_reduce_to_named_failure : Prop :=
  ∀ s : NSPaperSection,
    section_requires_analytic_bridge s →
    section_is_named_failure_boundary s ∨
    section_depends_on_named_failure s

instance instDecidableSectionStructurallyClosed (s : NSPaperSection) :
    Decidable (section_is_structurally_closed s) := by
  unfold section_is_structurally_closed section_obligation inventory_obligation_is_structural
  infer_instance

instance instDecidableSectionRequiresAnalyticBridge (s : NSPaperSection) :
    Decidable (section_requires_analytic_bridge s) := by
  unfold section_requires_analytic_bridge section_obligation inventory_obligation_is_analytic
  infer_instance

instance instDecidableSectionNamedFailureBoundary (s : NSPaperSection) :
    Decidable (section_is_named_failure_boundary s) := by
  unfold section_is_named_failure_boundary section_obligation inventory_named_failure
  infer_instance

instance instDecidableSectionDependsOnNamedFailure (s : NSPaperSection) :
    Decidable (section_depends_on_named_failure s) := by
  unfold section_depends_on_named_failure section_obligation inventory_endpoint_depends_on_named_failure
  infer_instance

theorem PaperSectionLedgerCompleteStatement :
  ∀ s : NSPaperSection,
    inventory_obligation_is_structural (section_obligation s) ∨
    inventory_obligation_is_analytic (section_obligation s) := by
  intro s
  cases s
  · dsimp [paper_obligation_ledger_complete, section_is_structurally_closed, section_requires_analytic_bridge,
      section_obligation, inventory_obligation_is_structural, inventory_obligation_is_analytic]
    exact Or.inl (Or.inl rfl)
  · dsimp [paper_obligation_ledger_complete, section_is_structurally_closed, section_requires_analytic_bridge,
      section_obligation, inventory_obligation_is_structural, inventory_obligation_is_analytic]
    exact Or.inl (Or.inr (Or.inl rfl))
  · dsimp [paper_obligation_ledger_complete, section_is_structurally_closed, section_requires_analytic_bridge,
      section_obligation, inventory_obligation_is_structural, inventory_obligation_is_analytic]
    exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  · dsimp [paper_obligation_ledger_complete, section_is_structurally_closed, section_requires_analytic_bridge,
      section_obligation, inventory_obligation_is_structural, inventory_obligation_is_analytic]
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · dsimp [paper_obligation_ledger_complete, section_is_structurally_closed, section_requires_analytic_bridge,
      section_obligation, inventory_obligation_is_structural, inventory_obligation_is_analytic]
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · dsimp [paper_obligation_ledger_complete, section_is_structurally_closed, section_requires_analytic_bridge,
      section_obligation, inventory_obligation_is_structural, inventory_obligation_is_analytic]
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · dsimp [paper_obligation_ledger_complete, section_is_structurally_closed, section_requires_analytic_bridge,
      section_obligation, inventory_obligation_is_structural, inventory_obligation_is_analytic]
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · dsimp [paper_obligation_ledger_complete, section_is_structurally_closed, section_requires_analytic_bridge,
      section_obligation, inventory_obligation_is_structural, inventory_obligation_is_analytic]
    exact Or.inr (Or.inl rfl)
  · dsimp [paper_obligation_ledger_complete, section_is_structurally_closed, section_requires_analytic_bridge,
      section_obligation, inventory_obligation_is_structural, inventory_obligation_is_analytic]
    exact Or.inr (Or.inr rfl)

theorem PaperSectionAnalyticReductionStatement :
  paper_analytic_sections_reduce_to_named_failure := by
  intro s hs
  cases s
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem PaperPrimitiveSectionsAreStructurallyClosedStatement :
  inventory_obligation_is_structural (section_obligation .primitiveCarrierSection) ∧
  inventory_obligation_is_structural (section_obligation .periodicLocalTheorySection) ∧
  inventory_obligation_is_structural (section_obligation .horizonWitnessSection) ∧
  inventory_obligation_is_structural (section_obligation .singularExtractorSection) ∧
  inventory_obligation_is_structural (section_obligation .restartTransportSection) ∧
  inventory_obligation_is_structural (section_obligation .maximalLineageClosureSection) ∧
  inventory_obligation_is_structural (section_obligation .noSecondGateSection) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [section_is_structurally_closed, section_obligation, inventory_obligation_is_structural]
    exact Or.inl rfl
  · dsimp [section_is_structurally_closed, section_obligation, inventory_obligation_is_structural]
    exact Or.inr (Or.inl rfl)
  · dsimp [section_is_structurally_closed, section_obligation, inventory_obligation_is_structural]
    exact Or.inr (Or.inr (Or.inl rfl))
  · dsimp [section_is_structurally_closed, section_obligation, inventory_obligation_is_structural]
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · dsimp [section_is_structurally_closed, section_obligation, inventory_obligation_is_structural]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · dsimp [section_is_structurally_closed, section_obligation, inventory_obligation_is_structural]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · dsimp [section_is_structurally_closed, section_obligation, inventory_obligation_is_structural]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem PaperVortexStretchingSectionIsNamedFailureStatement :
  section_is_named_failure_boundary .vortexStretchingAnomalySection := by
  rfl

theorem PaperEndpointTransferSectionDependsOnNamedFailureStatement :
  section_depends_on_named_failure .endpointTransferSection := by
  rfl

theorem PaperLedgerMatchesConcreteInventoryStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (_hboundary : primitive_no_blowup_boundary G) :
  ∀ s : NSPaperSection,
    (buildConcreteObligationRegister G).analyticFailurePoint (section_obligation s) →
    section_is_named_failure_boundary s ∨ section_depends_on_named_failure s := by
  intro s hs
  cases s
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · rcases hs with h | h <;> cases h
  · exact Or.inl rfl
  · exact Or.inr rfl

end MaleyLean
