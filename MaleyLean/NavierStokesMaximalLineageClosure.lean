import MaleyLean.NavierStokesRestartTransport

namespace MaleyLean

/--
Maximal-lineage closure packet for the primitive Navier--Stokes route.

This layer asks whether restart-compatible obstruction can accumulate into a
genuine terminal boundary for a realized maximal lineage. The structural answer
recorded here is that any such terminal boundary must remain same-scope and
transport-stable; otherwise it is only a terminal second gate in disguise.
-/
structure MaximalLineageClosureSystem
    (State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type) where
  restart : RestartTransportSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label
  terminalBoundary : Candidate → Prop
  closesLineage : Candidate → Prop
  terminalSecondGate : Candidate → Prop

def terminal_obstruction_on_maximal_lineage
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (M : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  Prop :=
  ∃ h : History, ∃ c : Candidate,
    M.restart.horizon.boundary.singularExtractor h = some c ∧
    M.restart.horizon.continuationObstructing c ∧
    M.terminalBoundary c ∧
    M.closesLineage c

def no_terminal_second_gate
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (M : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  Prop :=
  ∀ c : Candidate,
    M.terminalSecondGate c →
    ¬ M.terminalBoundary c

def maximal_lineage_closure_principle
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (M : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  Prop :=
  ∀ h : History, ∀ c : Candidate,
    M.restart.horizon.boundary.singularExtractor h = some c →
    M.restart.sameObjectTransport h (M.restart.reenteredHistory h) →
    M.terminalBoundary c →
    M.restart.horizon.boundary.extractorSameScope c ∧
    (M.restart.horizon.continuationObstructing c →
      M.closesLineage c)

def failed_terminal_transport_is_second_gate
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (M : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  Prop :=
  ∀ h : History, ∀ c : Candidate,
    M.restart.horizon.boundary.singularExtractor h = some c →
    M.terminalBoundary c →
    M.restart.sameObjectTransport h (M.restart.reenteredHistory h) →
    M.restart.horizon.boundary.singularExtractor (M.restart.reenteredHistory h) ≠ some c →
    M.terminalSecondGate c

theorem PaperTerminalObstructionOnMaximalLineageStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (M : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (h :
    ∃ h0 : History, ∃ c : Candidate,
      M.restart.horizon.boundary.singularExtractor h0 = some c ∧
      M.restart.horizon.continuationObstructing c ∧
      M.terminalBoundary c ∧
      M.closesLineage c) :
  terminal_obstruction_on_maximal_lineage M := by
  exact h

theorem PaperNoTerminalSecondGateStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (M : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (h :
    ∀ c : Candidate,
      M.terminalSecondGate c →
      ¬ M.terminalBoundary c) :
  no_terminal_second_gate M := by
  exact h

theorem PaperMaximalLineageClosurePrincipleStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (M : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (h :
    ∀ h0 : History, ∀ c : Candidate,
      M.restart.horizon.boundary.singularExtractor h0 = some c →
      M.restart.sameObjectTransport h0 (M.restart.reenteredHistory h0) →
      M.terminalBoundary c →
      M.restart.horizon.boundary.extractorSameScope c ∧
      (M.restart.horizon.continuationObstructing c →
        M.closesLineage c)) :
  maximal_lineage_closure_principle M := by
  exact h

theorem PaperFailedTerminalTransportIsSecondGateStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (M : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (h :
    ∀ h0 : History, ∀ c : Candidate,
      M.restart.horizon.boundary.singularExtractor h0 = some c →
      M.terminalBoundary c →
      M.restart.sameObjectTransport h0 (M.restart.reenteredHistory h0) →
      M.restart.horizon.boundary.singularExtractor (M.restart.reenteredHistory h0) ≠ some c →
      M.terminalSecondGate c) :
  failed_terminal_transport_is_second_gate M := by
  exact h

theorem PaperTerminalBoundaryOrSecondGateStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (M : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (hclose : maximal_lineage_closure_principle M)
  (_hfail : failed_terminal_transport_is_second_gate M)
  (_hguard : no_terminal_second_gate M)
  (_h :
    ∀ h0 : History, ∀ c : Candidate,
      M.restart.horizon.boundary.singularExtractor h0 = some c →
      M.terminalBoundary c →
      M.restart.sameObjectTransport h0 (M.restart.reenteredHistory h0)) :
  ∀ h0 : History, ∀ c : Candidate,
    M.restart.horizon.boundary.singularExtractor h0 = some c →
    M.terminalBoundary c →
    M.restart.sameObjectTransport h0 (M.restart.reenteredHistory h0) →
    M.restart.horizon.boundary.extractorSameScope c := by
  intro h0 c hextract hterminal htransport
  exact (hclose h0 c hextract htransport hterminal).1

theorem PaperRestartCompatibleTerminalObstructionClosesLineageStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (M : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (hclose : maximal_lineage_closure_principle M) :
  ∀ h : History, ∀ c : Candidate,
    M.restart.horizon.boundary.singularExtractor h = some c →
    M.restart.sameObjectTransport h (M.restart.reenteredHistory h) →
    M.terminalBoundary c →
    M.restart.horizon.continuationObstructing c →
    M.closesLineage c := by
  intro h c hextract htransport hterminal hobstruct
  exact (hclose h c hextract htransport hterminal).2 hobstruct

theorem PaperPrimitiveRestartToMaximalLineageClosureStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (M : MaximalLineageClosureSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (_h_restart_packet :
    restart_preserves_same_scope M.restart ∧
    obstruction_persists_under_restart M.restart ∧
    failed_restart_transport_collapses_obstruction M.restart)
  (hclose : maximal_lineage_closure_principle M)
  (_hguard : no_terminal_second_gate M) :
  ∀ h : History, ∀ c : Candidate,
    M.restart.horizon.boundary.singularExtractor h = some c →
    M.restart.sameObjectTransport h (M.restart.reenteredHistory h) →
    M.terminalBoundary c →
    M.restart.horizon.boundary.extractorSameScope c := by
  intro h c hextract htransport hterminal
  exact (hclose h c hextract htransport hterminal).1

end MaleyLean
