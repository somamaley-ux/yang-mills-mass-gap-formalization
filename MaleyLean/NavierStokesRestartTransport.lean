import MaleyLean.NavierStokesHorizonCollapse

namespace MaleyLean

/--
Restart-transport packet for the primitive Navier--Stokes route.

This layer tests whether a purported continuation obstruction survives the
same-object transport supplied by restart consistency and pre-horizon re-entry.
If obstruction is genuine, it should persist under restart transport; if it
fails to transport, it should collapse back into a non-load-bearing artifact.
-/
structure RestartTransportSystem
    (State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type) where
  primitive : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity
  localTheory : PeriodicLocalTheory State Time Datum LocalSol RestartWitness
  horizon : HorizonCollapseSystem State Time History RestartWitness Candidate Quantity Label
  restartHistory : History → RestartWitness
  reenteredHistory : History → History
  sameObjectTransport : History → History → Prop

def obstruction_persists_under_restart
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (R : RestartTransportSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  Prop :=
  ∀ h : History, ∀ c : Candidate,
    R.horizon.boundary.singularExtractor h = some c →
    R.horizon.continuationObstructing c →
    R.sameObjectTransport h (R.reenteredHistory h) →
    R.horizon.boundary.singularExtractor (R.reenteredHistory h) = some c ∧
    R.horizon.continuationObstructing c

def restart_preserves_same_scope
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (R : RestartTransportSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  Prop :=
  ∀ h : History, ∀ c : Candidate,
    R.horizon.boundary.singularExtractor h = some c →
    R.sameObjectTransport h (R.reenteredHistory h) →
    R.horizon.boundary.extractorSameScope c

def failed_restart_transport_collapses_obstruction
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (R : RestartTransportSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label) :
  Prop :=
  ∀ h : History, ∀ c : Candidate,
    R.horizon.boundary.singularExtractor h = some c →
    R.horizon.continuationObstructing c →
    R.sameObjectTransport h (R.reenteredHistory h) →
    R.horizon.boundary.singularExtractor (R.reenteredHistory h) ≠ some c →
    R.horizon.bookkeepingVisible c

theorem PaperObstructionPersistsUnderRestartStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (R : RestartTransportSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (h :
    ∀ h0 : History, ∀ c : Candidate,
      R.horizon.boundary.singularExtractor h0 = some c →
      R.horizon.continuationObstructing c →
      R.sameObjectTransport h0 (R.reenteredHistory h0) →
      R.horizon.boundary.singularExtractor (R.reenteredHistory h0) = some c ∧
      R.horizon.continuationObstructing c) :
  obstruction_persists_under_restart R := by
  exact h

theorem PaperRestartPreservesSameScopeStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (R : RestartTransportSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (h :
    ∀ h0 : History, ∀ c : Candidate,
      R.horizon.boundary.singularExtractor h0 = some c →
      R.sameObjectTransport h0 (R.reenteredHistory h0) →
      R.horizon.boundary.extractorSameScope c) :
  restart_preserves_same_scope R := by
  exact h

theorem PaperFailedRestartTransportCollapsesObstructionStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (R : RestartTransportSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (h :
    ∀ h0 : History, ∀ c : Candidate,
      R.horizon.boundary.singularExtractor h0 = some c →
      R.horizon.continuationObstructing c →
      R.sameObjectTransport h0 (R.reenteredHistory h0) →
      R.horizon.boundary.singularExtractor (R.reenteredHistory h0) ≠ some c →
      R.horizon.bookkeepingVisible c) :
  failed_restart_transport_collapses_obstruction R := by
  exact h

theorem PaperRestartTransportOrCollapseStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (R : RestartTransportSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (hpersist : obstruction_persists_under_restart R)
  (_hcollapse : failed_restart_transport_collapses_obstruction R)
  (_h :
    ∀ h0 : History, ∀ c : Candidate,
      R.horizon.boundary.singularExtractor h0 = some c →
      R.horizon.continuationObstructing c →
      R.sameObjectTransport h0 (R.reenteredHistory h0)) :
  ∀ h0 : History, ∀ c : Candidate,
    R.horizon.boundary.singularExtractor h0 = some c →
    R.horizon.continuationObstructing c →
    R.sameObjectTransport h0 (R.reenteredHistory h0) →
    (R.horizon.boundary.singularExtractor (R.reenteredHistory h0) = some c ∧
      R.horizon.continuationObstructing c) ∨
    R.horizon.bookkeepingVisible c := by
  intro h0 c hextract hobstruct htransport
  left
  exact hpersist h0 c hextract hobstruct htransport

theorem PaperPrimitiveLocalTheorySupportsRestartTransportStatement
  {State Time Datum LocalSol History RestartWitness Candidate Quantity Label : Type}
  (R : RestartTransportSystem State Time Datum LocalSol History RestartWitness Candidate Quantity Label)
  (_h_packet :
    datum_entry_to_admitted_carrier R.primitive R.localTheory ∧
    local_realization_on_carrier R.primitive R.localTheory ∧
    restart_consistency_same_object_persistence R.primitive R.localTheory ∧
    pre_horizon_slice_reentry R.primitive R.localTheory ∧
    finite_horizon_witness_visibility R.primitive R.localTheory)
  (hscope : restart_preserves_same_scope R)
  (hpersist : obstruction_persists_under_restart R) :
  ∀ h : History, ∀ c : Candidate,
    R.horizon.boundary.singularExtractor h = some c →
    R.sameObjectTransport h (R.reenteredHistory h) →
    R.horizon.boundary.extractorSameScope c ∧
    (R.horizon.boundary.singularExtractor (R.reenteredHistory h) = some c →
      R.horizon.continuationObstructing c →
      R.horizon.continuationObstructing c) := by
  intro h c hextract htransport
  refine ⟨hscope h c hextract htransport, ?_⟩
  intro _ hobstruct
  exact (hpersist h c hextract hobstruct htransport).2

end MaleyLean
