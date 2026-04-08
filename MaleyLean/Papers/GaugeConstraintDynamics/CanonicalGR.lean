import MaleyLean.Papers.GaugeConstraintDynamics.SymplecticGeometry

namespace MaleyLean

/--
Minimal canonical-GR realization package for the paper's Stage-III/IV claims.

This is still a structural interface rather than a full ADM development: it
records the ingredients needed for weak first-class closure and multiplier-type
Hamiltonian rigidity in the constrained Hamiltonian reading of GR.
-/
structure CanonicalGRSystem
  (PhasePoint Vec Generator BracketTerm Presentation Hamiltonian : Type) where
  geometry : LocalPresymplecticGeometry PhasePoint Vec
  bracketTerm : Generator -> Generator -> BracketTerm
  vanishesOnStanding : BracketTerm -> Prop
  inConstraintIdeal : BracketTerm -> Prop
  physicalHamiltonian : Hamiltonian -> Prop
  weaklyFactorsThrough : Presentation -> Hamiltonian -> Prop

/-- Weak first-class closure witness for the canonical-GR generator family. -/
structure CanonicalGRFirstClassWitness
  {PhasePoint Vec Generator BracketTerm Presentation Hamiltonian : Type}
  (S : CanonicalGRSystem
    PhasePoint Vec Generator BracketTerm Presentation Hamiltonian) where
  weakClosure :
    weakly_first_class
      S.bracketTerm
      S.vanishesOnStanding
      S.inConstraintIdeal

/-- Multiplier rigidity witness for the canonical Hamiltonian presentations. -/
structure CanonicalGRMultiplierWitness
  {PhasePoint Vec Generator BracketTerm Presentation Hamiltonian : Type}
  (S : CanonicalGRSystem
    PhasePoint Vec Generator BracketTerm Presentation Hamiltonian) where
  rigidity :
    local_multiplier_rigidity
      S.physicalHamiltonian
      S.weaklyFactorsThrough

/-- Weak first-class closure descends immediately to the paper-facing Stage-III surface. -/
theorem canonical_gr_supports_first_class_closure
  {PhasePoint Vec Generator BracketTerm Presentation Hamiltonian : Type}
  (S : CanonicalGRSystem
    PhasePoint Vec Generator BracketTerm Presentation Hamiltonian)
  (h_fc : CanonicalGRFirstClassWitness S) :
  weakly_first_class
    S.bracketTerm
    S.vanishesOnStanding
    S.inConstraintIdeal := by
  exact h_fc.weakClosure

/-- Multiplier rigidity descends immediately to the paper-facing Stage-IV surface. -/
theorem canonical_gr_supports_multiplier_rigidity
  {PhasePoint Vec Generator BracketTerm Presentation Hamiltonian : Type}
  (S : CanonicalGRSystem
    PhasePoint Vec Generator BracketTerm Presentation Hamiltonian)
  (h_mult : CanonicalGRMultiplierWitness S) :
  local_multiplier_rigidity
    S.physicalHamiltonian
    S.weaklyFactorsThrough := by
  exact h_mult.rigidity

/--
Joint Stage-III/IV canonical-GR package: the same system can carry both weak
first-class closure and multiplier rigidity.
-/
theorem canonical_gr_supports_constraint_dynamics_core
  {PhasePoint Vec Generator BracketTerm Presentation Hamiltonian : Type}
  (S : CanonicalGRSystem
    PhasePoint Vec Generator BracketTerm Presentation Hamiltonian)
  (h_fc : CanonicalGRFirstClassWitness S)
  (h_mult : CanonicalGRMultiplierWitness S) :
  weakly_first_class
    S.bracketTerm
    S.vanishesOnStanding
    S.inConstraintIdeal /\
  local_multiplier_rigidity
    S.physicalHamiltonian
    S.weaklyFactorsThrough := by
  exact And.intro
    (canonical_gr_supports_first_class_closure S h_fc)
    (canonical_gr_supports_multiplier_rigidity S h_mult)

/--
If the underlying presymplectic geometry is coisotropic with identified
characteristic directions and the canonical generators are first-class, then the
system carries the paper's Stage-II/III structural spine.
-/
theorem canonical_gr_with_geometry_supports_stageIII
  {PhasePoint Vec Generator BracketTerm Presentation Hamiltonian : Type}
  (S : CanonicalGRSystem
    PhasePoint Vec Generator BracketTerm Presentation Hamiltonian)
  (h_id : CharacteristicIdentificationWitness S.geometry)
  (N : CoisotropicNormalForm (Generator := Generator) S.geometry.characteristic)
  (h_fc : CanonicalGRFirstClassWitness S) :
  generated_by_family S.geometry.vertical N.spans /\
  weakly_first_class
    S.bracketTerm
    S.vanishesOnStanding
    S.inConstraintIdeal := by
  exact And.intro
    (local_presymplectic_geometry_supports_constraint_span S.geometry h_id N)
    (canonical_gr_supports_first_class_closure S h_fc)

/-- Tiny toy phase point for the canonical-GR witness. -/
inductive ToyGRPhasePoint where
  | sigma0
deriving DecidableEq, Repr

/-- Tiny toy vector space reusing one gauge and one transverse direction. -/
abbrev ToyGRVec := ToyPhaseVec

/-- Toy canonical generators mimicking Hamiltonian and momentum constraints. -/
inductive ToyGRGenerator where
  | hamiltonian
  | momentum
deriving DecidableEq, Repr

/-- Toy bracket terms. -/
inductive ToyGRBracketTerm where
  | zero
deriving DecidableEq, Repr

/-- Toy canonical presentations. -/
inductive ToyGRPresentation where
  | lapseShiftA
  | lapseShiftB
deriving DecidableEq, Repr

/-- Toy Hamiltonians. -/
inductive ToyGRHamiltonian where
  | physical
deriving DecidableEq, Repr

/-- Tiny canonical-GR system packaged over the toy local presymplectic geometry. -/
def toyCanonicalGRSystem :
  CanonicalGRSystem
    ToyGRPhasePoint
    ToyGRVec
    ToyGRGenerator
    ToyGRBracketTerm
    ToyGRPresentation
    ToyGRHamiltonian where
  geometry :=
    { tangentSpace := fun _ _ => True
      vertical := fun _ v => v = ToyPhaseVec.gaugeDir
      characteristic := fun _ v => v = ToyPhaseVec.gaugeDir }
  bracketTerm := fun _ _ => ToyGRBracketTerm.zero
  vanishesOnStanding := fun _ => True
  inConstraintIdeal := fun _ => True
  physicalHamiltonian := fun H => H = ToyGRHamiltonian.physical
  weaklyFactorsThrough := fun _ H => H = ToyGRHamiltonian.physical

/-- The toy canonical generators are weakly first-class. -/
def toyCanonicalGRFirstClassWitness :
  CanonicalGRFirstClassWitness toyCanonicalGRSystem where
  weakClosure := by
    intro a b
    exact And.intro trivial trivial

/-- The toy canonical presentations all weakly factor through the physical Hamiltonian. -/
def toyCanonicalGRMultiplierWitness :
  CanonicalGRMultiplierWitness toyCanonicalGRSystem where
  rigidity := by
    refine ⟨ToyGRHamiltonian.physical, rfl, ?_⟩
    intro alpha
    rfl

/-- Characteristic identification for the toy canonical-GR geometry. -/
def toyCanonicalGRCharacteristicIdentification :
  CharacteristicIdentificationWitness toyCanonicalGRSystem.geometry where
  vertical_to_characteristic := by
    intro x v hv
    exact hv
  characteristic_to_vertical := by
    intro x v hv
    exact hv

/-- Toy coisotropic normal form for the canonical-GR geometry. -/
def toyCanonicalGRNormalForm :
  CoisotropicNormalForm
    (Generator := ToyGRGenerator)
    toyCanonicalGRSystem.geometry.characteristic where
  spans g x v :=
    match g with
    | ToyGRGenerator.hamiltonian => v = ToyPhaseVec.gaugeDir
    | ToyGRGenerator.momentum => False
  complete := by
    intro x v
    constructor
    · intro hv
      refine ⟨ToyGRGenerator.hamiltonian, ?_⟩
      exact hv
    · intro hv
      rcases hv with ⟨g, hg⟩
      cases g with
      | hamiltonian =>
          exact hg
      | momentum =>
          exact False.elim hg

/-- Concrete weak first-class closure for the toy canonical-GR system. -/
theorem toy_canonical_gr_first_class :
  weakly_first_class
    toyCanonicalGRSystem.bracketTerm
    toyCanonicalGRSystem.vanishesOnStanding
    toyCanonicalGRSystem.inConstraintIdeal := by
  exact canonical_gr_supports_first_class_closure
    toyCanonicalGRSystem
    toyCanonicalGRFirstClassWitness

/-- Concrete multiplier rigidity for the toy canonical-GR system. -/
theorem toy_canonical_gr_multiplier_rigidity :
  local_multiplier_rigidity
    toyCanonicalGRSystem.physicalHamiltonian
    toyCanonicalGRSystem.weaklyFactorsThrough := by
  exact canonical_gr_supports_multiplier_rigidity
    toyCanonicalGRSystem
    toyCanonicalGRMultiplierWitness

/-- Combined toy Stage-III/IV canonical-GR witness. -/
theorem toy_canonical_gr_constraint_dynamics_core :
  weakly_first_class
      toyCanonicalGRSystem.bracketTerm
      toyCanonicalGRSystem.vanishesOnStanding
      toyCanonicalGRSystem.inConstraintIdeal /\
  local_multiplier_rigidity
      toyCanonicalGRSystem.physicalHamiltonian
      toyCanonicalGRSystem.weaklyFactorsThrough := by
  exact canonical_gr_supports_constraint_dynamics_core
    toyCanonicalGRSystem
    toyCanonicalGRFirstClassWitness
    toyCanonicalGRMultiplierWitness

/-- Toy combined geometric/canonical witness for the Stage-III spine. -/
theorem toy_canonical_gr_stageIII :
  generated_by_family
      toyCanonicalGRSystem.geometry.vertical
      toyCanonicalGRNormalForm.spans /\
  weakly_first_class
      toyCanonicalGRSystem.bracketTerm
      toyCanonicalGRSystem.vanishesOnStanding
      toyCanonicalGRSystem.inConstraintIdeal := by
  exact canonical_gr_with_geometry_supports_stageIII
    toyCanonicalGRSystem
    toyCanonicalGRCharacteristicIdentification
    toyCanonicalGRNormalForm
    toyCanonicalGRFirstClassWitness

end MaleyLean
