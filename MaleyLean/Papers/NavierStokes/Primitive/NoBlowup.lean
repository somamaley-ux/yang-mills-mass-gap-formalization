import MaleyLean.Papers.NavierStokes.Continuation.MaximalLineageClosure

namespace MaleyLean

/--
Primitive global-boundary packet for the Navier--Stokes route.

This is not a PDE smoothness proof. It records the stronger primitive-side
corollary available after the restart, quotient, and terminal-boundary layers:
if every terminal obstruction must be same-scope and transport-stable, and
terminal second gates are disallowed, then no admissible same-scope blowup
witness remains available inside the primitive route.
-/
structure PrimitiveNoBlowupSystem
    (State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type) where
  closure : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label
  blowupWitness : Candidate → Prop
  admissibleWitness : Candidate → Prop
  sameScopeWitness : Candidate → Prop

def admissible_same_scope_blowup_witness
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  Prop :=
  ∃ h : History, ∃ c : Candidate,
    G.closure.restart.horizon.boundary.singularExtractor h = some c ∧
    G.blowupWitness c ∧
    G.admissibleWitness c ∧
    G.sameScopeWitness c

def primitive_no_blowup_boundary
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  Prop :=
  ¬ admissible_same_scope_blowup_witness G

def terminal_obstruction_absorbs_blowup
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  Prop :=
  ∀ h : History, ∀ c : Candidate,
    G.closure.restart.horizon.boundary.singularExtractor h = some c →
    G.blowupWitness c →
    G.admissibleWitness c →
    G.sameScopeWitness c →
    G.closure.terminalBoundary c ∧
    G.closure.restart.horizon.continuationObstructing c

def no_admissible_same_scope_blowup_from_terminal_closure
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  Prop :=
  ∀ h : History, ∀ c : Candidate,
    G.closure.restart.horizon.boundary.singularExtractor h = some c →
    G.blowupWitness c →
    G.admissibleWitness c →
    G.sameScopeWitness c →
    G.closure.restart.sameObjectTransport h (G.closure.restart.reenteredHistory h) →
    False

theorem PaperAdmissibleSameScopeBlowupWitnessStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (h :
    ∃ h0 : History, ∃ c : Candidate,
      G.closure.restart.horizon.boundary.singularExtractor h0 = some c ∧
      G.blowupWitness c ∧
      G.admissibleWitness c ∧
      G.sameScopeWitness c) :
  admissible_same_scope_blowup_witness G := by
  exact h

theorem PaperTerminalObstructionAbsorbsBlowupStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (h :
    ∀ h0 : History, ∀ c : Candidate,
      G.closure.restart.horizon.boundary.singularExtractor h0 = some c →
      G.blowupWitness c →
      G.admissibleWitness c →
      G.sameScopeWitness c →
      G.closure.terminalBoundary c ∧
      G.closure.restart.horizon.continuationObstructing c) :
  terminal_obstruction_absorbs_blowup G := by
  exact h

theorem PaperNoAdmissibleSameScopeBlowupFromTerminalClosureStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (h :
    ∀ h0 : History, ∀ c : Candidate,
      G.closure.restart.horizon.boundary.singularExtractor h0 = some c →
      G.blowupWitness c →
      G.admissibleWitness c →
      G.sameScopeWitness c →
      G.closure.restart.sameObjectTransport h0 (G.closure.restart.reenteredHistory h0) →
      False) :
  no_admissible_same_scope_blowup_from_terminal_closure G := by
  exact h

theorem PaperPrimitiveNoBlowupBoundaryStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (hcollapse : terminal_obstruction_absorbs_blowup G)
  (htransport :
    ∀ h : History,
      G.closure.restart.sameObjectTransport h (G.closure.restart.reenteredHistory h))
  (hno :
    no_admissible_same_scope_blowup_from_terminal_closure G) :
  primitive_no_blowup_boundary G := by
  intro hblowup
  rcases hblowup with ⟨h, c, hextract, hblow, hadm, hscope⟩
  have _ := hcollapse h c hextract hblow hadm hscope
  have hcontra :
      G.closure.restart.sameObjectTransport h (G.closure.restart.reenteredHistory h) → False :=
    fun htr => hno h c hextract hblow hadm hscope htr
  exact hcontra (htransport h)

theorem PaperPrimitiveRestartClosureBlocksBlowupStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (G : PrimitiveNoBlowupSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (_h_restart_packet :
    restart_preserves_same_scope G.closure.restart ∧
    obstruction_persists_under_restart G.closure.restart ∧
    failed_restart_transport_collapses_obstruction G.closure.restart)
  (_h_closure_packet :
    maximal_lineage_closure_principle G.closure ∧
    no_terminal_second_gate G.closure)
  (hcollapse : terminal_obstruction_absorbs_blowup G)
  (htransport :
    ∀ h : History,
      G.closure.restart.sameObjectTransport h (G.closure.restart.reenteredHistory h))
  (hno : no_admissible_same_scope_blowup_from_terminal_closure G) :
  primitive_no_blowup_boundary G := by
  exact PaperPrimitiveNoBlowupBoundaryStatement G hcollapse htransport hno

end MaleyLean
