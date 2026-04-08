import MaleyLean.Papers.NavierStokes.Primitive.Core

namespace MaleyLean

/--
Primitive-to-periodic-local-theory interface.

This file does not formalize Navier--Stokes analysis. It records the exact
local-theory bridge objects the primitive route needs before any global PDE
claim can be attempted: local realization, restart consistency, pre-horizon
slice re-entry, and finite-horizon witness visibility.
-/
structure PeriodicLocalTheory
    (State Time Datum LocalSol RestartWitness : Type) where
  officialDatum : Datum → Prop
  admittedCarrierDatum : Datum → Prop
  localSolution : Datum → LocalSol
  localStateAt : LocalSol → Time → State
  maximalTime : LocalSol → Time
  restartData : LocalSol → Time → RestartWitness
  restartConsistent : RestartWitness → Prop
  preHorizonSlice : LocalSol → Time → Prop
  finiteHorizonWitness : LocalSol → Time → Prop

def datum_entry_to_admitted_carrier
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (_S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness) : Prop :=
  ∀ d : Datum, L.officialDatum d → L.admittedCarrierDatum d

def local_realization_on_carrier
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness) : Prop :=
  ∀ d : Datum, L.admittedCarrierDatum d →
    ∀ t : Time, S.sameScopeContinuation t →
      S.carrier.admitted (L.localStateAt (L.localSolution d) t)

def restart_consistency_same_object_persistence
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness) : Prop :=
  ∀ d : Datum, L.admittedCarrierDatum d →
    ∀ t : Time, S.sameScopeContinuation t →
      L.restartConsistent (L.restartData (L.localSolution d) t)

def pre_horizon_slice_reentry
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness) : Prop :=
  ∀ d : Datum, L.admittedCarrierDatum d →
    ∀ t : Time, S.sameScopeContinuation t →
      L.preHorizonSlice (L.localSolution d) t

def finite_horizon_witness_visibility
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness) : Prop :=
  ∀ d : Datum, L.admittedCarrierDatum d →
    ∀ t : Time, S.sameScopeContinuation t →
      L.finiteHorizonWitness (L.localSolution d) t

theorem PaperDatumEntryToAdmittedCarrierStatement
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness)
  (h : ∀ d : Datum, L.officialDatum d → L.admittedCarrierDatum d) :
  datum_entry_to_admitted_carrier S L := by
  exact h

theorem PaperLocalRealizationOnCarrierStatement
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness)
  (h :
    ∀ d : Datum, L.admittedCarrierDatum d →
      ∀ t : Time, S.sameScopeContinuation t →
        S.carrier.admitted (L.localStateAt (L.localSolution d) t)) :
  local_realization_on_carrier S L := by
  exact h

theorem PaperRestartConsistencySameObjectPersistenceStatement
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness)
  (h :
    ∀ d : Datum, L.admittedCarrierDatum d →
      ∀ t : Time, S.sameScopeContinuation t →
        L.restartConsistent (L.restartData (L.localSolution d) t)) :
  restart_consistency_same_object_persistence S L := by
  exact h

theorem PaperPreHorizonSliceReentryStatement
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness)
  (h :
    ∀ d : Datum, L.admittedCarrierDatum d →
      ∀ t : Time, S.sameScopeContinuation t →
        L.preHorizonSlice (L.localSolution d) t) :
  pre_horizon_slice_reentry S L := by
  exact h

theorem PaperFiniteHorizonWitnessVisibilityStatement
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness)
  (h :
    ∀ d : Datum, L.admittedCarrierDatum d →
      ∀ t : Time, S.sameScopeContinuation t →
        L.finiteHorizonWitness (L.localSolution d) t) :
  finite_horizon_witness_visibility S L := by
  exact h

theorem PaperPrimitivePeriodicLocalTheoryPacketStatement
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness)
  (h_entry : datum_entry_to_admitted_carrier S L)
  (h_local : local_realization_on_carrier S L)
  (h_restart : restart_consistency_same_object_persistence S L)
  (h_reentry : pre_horizon_slice_reentry S L)
  (h_witness : finite_horizon_witness_visibility S L) :
  datum_entry_to_admitted_carrier S L ∧
  local_realization_on_carrier S L ∧
  restart_consistency_same_object_persistence S L ∧
  pre_horizon_slice_reentry S L ∧
  finite_horizon_witness_visibility S L := by
  exact ⟨h_entry, h_local, h_restart, h_reentry, h_witness⟩

theorem PaperPrimitiveBridgeCompatibleWithAnomalyBoundaryStatement
  {State Time Datum LocalSol RestartWitness Quantity Candidate : Type}
  (S : PrimitiveNavierStokesSystem State Time RestartWitness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol RestartWitness)
  (_h_packet :
    datum_entry_to_admitted_carrier S L ∧
    local_realization_on_carrier S L ∧
    restart_consistency_same_object_persistence S L ∧
    pre_horizon_slice_reentry S L ∧
    finite_horizon_witness_visibility S L)
  (hskin : metric_divergence_skin_only S) :
  ¬ vortex_stretching_anomaly_boundary S := by
  intro hanom
  rcases hanom with ⟨q, hmetric, hnotbook, hillicit⟩
  rcases hskin q hmetric with hbook | hnotgate
  · exact hnotbook hbook
  · exact hnotgate hillicit

end MaleyLean
