import MaleyLean.Core

namespace MaleyLean

/--
Primitive same-scope core for a Navier--Stokes-style structural route.

This is intentionally not a PDE proof. It captures the manuscript's
primitive-side objects: carrier, realized maximal lineage, same-scope
continuation, horizon witness, singular candidates, and the distinction
between standing-bearing structural witnesses and downstream metric
bookkeeping.
-/
structure PrimitiveCarrier (State : Type) where
  admitted : State → Prop
  fixedScope : Prop

structure RealizedLineage (State Time : Type) where
  stateAt : Time → State
  realized : Prop
  maximal : Prop

structure HorizonWitness (State Time Witness : Type) where
  witnessAt : Time → Witness
  carrierVisible : Witness → Prop
  quotientVisible : Witness → Prop
  horizonBearing : Witness → Prop

structure SingularCandidate (State Time Candidate : Type) where
  candidateAt : Time → Candidate
  carrierVisible : Candidate → Prop
  sameScope : Candidate → Prop

structure PrimitiveNavierStokesSystem
    (State Time Witness Candidate Quantity : Type) where
  carrier : PrimitiveCarrier State
  lineage : RealizedLineage State Time
  horizonWitness : HorizonWitness State Time Witness
  singularCandidate : SingularCandidate State Time Candidate
  standing : State → Prop
  sameScopeContinuation : Time → Prop
  preservesRelevantInvariants : State → Prop
  metricQuantity : Quantity → Prop
  quotientVisibleWitnessBookkeeping : Quantity → Prop
  illicitMetricGate : Quantity → Prop

def standing_positive_lineage
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  ∀ t : Time, S.sameScopeContinuation t → S.standing (S.lineage.stateAt t)

def carrier_to_lineage_binding
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  S.lineage.realized ∧
  S.lineage.maximal ∧
  S.carrier.fixedScope

def no_admissibility_dynamics
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  ∀ t₁ t₂ : Time,
    S.sameScopeContinuation t₁ →
    S.sameScopeContinuation t₂ →
    (S.standing (S.lineage.stateAt t₁) ↔ S.standing (S.lineage.stateAt t₂))

def pre_horizon_witness_exists
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  ∃ t : Time, S.sameScopeContinuation t ∧
    ∃ w : Witness,
      S.horizonWitness.carrierVisible w ∧
      S.horizonWitness.quotientVisible w ∧
      S.horizonWitness.horizonBearing w

def singular_image_same_scope
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  ∃ t : Time, S.sameScopeContinuation t ∧
    ∃ c : Candidate,
      S.singularCandidate.carrierVisible c ∧
      S.singularCandidate.sameScope c

def metric_divergence_skin_only
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  ∀ q : Quantity,
    S.metricQuantity q →
    S.quotientVisibleWitnessBookkeeping q ∨ ¬ S.illicitMetricGate q

def vortex_stretching_anomaly_boundary
  {State Time Witness Candidate Quantity : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity) : Prop :=
  ∃ q : Quantity,
    S.metricQuantity q ∧
    ¬ S.quotientVisibleWitnessBookkeeping q ∧
    S.illicitMetricGate q

end MaleyLean
