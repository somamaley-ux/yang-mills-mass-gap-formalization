namespace MaleyLean

/--
Lightweight core for the paper
"Meta-Necessity of Admissibility: A Proof-of-Proof for the Maley Corpus".

This surface is intentionally abstract. The manuscript argues at a meta-level
about any non-degenerate irreversible decision system, so the Lean layer tracks
only the structural predicates needed for the theorem spine.
-/
structure IrreversibleDecisionSystem (Claim State : Type) where
  accepts : State → Claim → Prop
  compose : List Claim → Claim
  nextState : State → Claim → State
  irreversible_decision : Prop
  nondegenerate : Prop
  unrestricted_composition : Prop

def standing_preserving_invariant
  {Claim State : Type}
  (Sys : IrreversibleDecisionSystem Claim State)
  (standing : State → Claim → Prop) : Prop :=
  ∀ s : State, ∀ c : Claim,
    Sys.accepts s c → standing s c

def irreversibility_defined
  {Claim State : Type}
  (Sys : IrreversibleDecisionSystem Claim State) : Prop :=
  ∃ s : State, ∃ c : Claim, Sys.accepts s c

def temporal_asymmetry_artifact
  {Claim State : Type}
  (_Sys : IrreversibleDecisionSystem Claim State) : Prop :=
  True

def admissible_interior_supports_reference
  {Claim State : Type}
  (_Sys : IrreversibleDecisionSystem Claim State) : Prop :=
  True

def informational_primitive
  (Info : Type) (_i : Info) : Prop :=
  False

def admissible_quantity
  {Q : Type}
  (_q : Q) : Prop :=
  False

def recovers_temporal_primitivity
  {Q : Type}
  (qs : List Q) : Prop :=
  ∃ q : Q, q ∈ qs ∧ admissible_quantity q

def preserves_reference_stability
  {Info : Type}
  (_i : Info) : Prop :=
  True

def preserves_redescription_invariant_encoding
  {Info : Type}
  (_i : Info) : Prop :=
  True

def relabeling_recovers_primitivity
  {Info Label : Type}
  (_i : Info)
  (_l : Label) : Prop :=
  True

def promoted_to_ontic_status
  {Label : Type}
  (_l : Label) : Prop :=
  True

def global_temporal_boundary_condition
  {Boundary : Type}
  (_b : Boundary) : Prop :=
  True

def violates_standing_conservation
  {Boundary : Type}
  (_b : Boundary) : Prop :=
  True

inductive CorpusGateRole where
  | maleyGate
  | claimModalityGate
  | scopeEnvelopeGovernor
  | standingEnforcementGate
  | redescriptionStabilityChecker
  | laGovernor
  | impossibilityGate
  | ametricBoundary
deriving DecidableEq, Repr

def induces_canonical_gate_roles
  {Claim State : Type}
  (_Sys : IrreversibleDecisionSystem Claim State) : Prop :=
  True

end MaleyLean
