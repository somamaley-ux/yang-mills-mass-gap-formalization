namespace MaleyLean

/--
Lightweight core for the paper
"Claim Modality and the Structure of Assertion".

The manuscript isolates assertion force as a distinct admissibility layer over
stable content. This Lean surface keeps only the structural notions needed for
the theorem spine: content stability, scope-sensitive modality, weakening, and
modal overreach.
-/
structure ClaimModalitySystem (Claim Scope Modality : Type) where
  contentStable : Claim → Prop
  admissibleScope : Scope → Prop
  assertedModality : Claim → Modality
  admissibleModality : Claim → Scope → Modality → Prop
  weakensTo : Scope → Scope → Prop
  weakerOrEqual : Modality → Modality → Prop
  standing : Claim → Prop
  error : Claim → Prop

def scope_alignment
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality)
  (c : Claim)
  (σ : Scope) : Prop :=
  S.admissibleModality c σ (S.assertedModality c)

def redescription_monotonicity
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality) : Prop :=
  ∀ c : Claim, ∀ σ σ' : Scope,
    S.weakensTo σ σ' →
    S.admissibleModality c σ (S.assertedModality c) →
    S.weakerOrEqual (S.assertedModality c) (S.assertedModality c)

def non_amplification
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality) : Prop :=
  ∀ c : Claim, ∀ σ σ' : Scope,
    S.weakensTo σ σ' →
    ¬ S.weakerOrEqual (S.assertedModality c) (S.assertedModality c) →
    False

def fail_closed_behavior
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality) : Prop :=
  ∀ c : Claim, ∀ σ : Scope,
    ¬ S.admissibleScope σ →
    S.admissibleModality c σ (S.assertedModality c) → False

def modal_overreach
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality)
  (c : Claim)
  (σ σ' : Scope) : Prop :=
  S.contentStable c ∧
  S.weakensTo σ σ' ∧
  S.admissibleModality c σ (S.assertedModality c) ∧
  ¬ S.admissibleModality c σ' (S.assertedModality c)

def unrestricted_assertion_force
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality) : Prop :=
  ∀ c : Claim, ∀ σ : Scope,
    S.admissibleScope σ →
    S.admissibleModality c σ (S.assertedModality c)

def permits_assertion
  {Claim Scope Modality : Type}
  (S : ClaimModalitySystem Claim Scope Modality) : Prop :=
  ∃ c : Claim, ∃ σ : Scope,
    S.admissibleScope σ ∧
    S.admissibleModality c σ (S.assertedModality c)

inductive EpistemicModalityRole where
  | claimModalityGate
  | modalityLiabilitySuppression
  | standingEnforcement
  | redescriptionStabilityChecking
deriving DecidableEq, Repr

def induces_claim_modality_gate
  {Claim Scope Modality : Type}
  (_S : ClaimModalitySystem Claim Scope Modality) : Prop :=
  True

end MaleyLean
