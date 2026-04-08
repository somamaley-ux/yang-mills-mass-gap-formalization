import MaleyLean.Papers.GaugeConstraintDynamics.PaperStatements

namespace MaleyLean

/--
Minimal local presymplectic package used to sharpen the paper's Stage-II and
Stage-III surfaces.

This remains intentionally lightweight: the goal is to expose the structural
interfaces needed by the manuscript without pretending that a full symplectic
manifold library already exists in the repo.
-/
structure LocalPresymplecticGeometry (Point Vec : Type) where
  tangentSpace : Point -> Vec -> Prop
  vertical : Point -> Vec -> Prop
  characteristic : Point -> Vec -> Prop

/-- Standing witness that the vertical and characteristic directions coincide. -/
structure CharacteristicIdentificationWitness
  {Point Vec : Type}
  (G : LocalPresymplecticGeometry Point Vec) where
  vertical_to_characteristic :
    pointwise_subdistribution G.vertical G.characteristic
  characteristic_to_vertical :
    pointwise_subdistribution G.characteristic G.vertical

/-- Local coisotropic witness for a presymplectic standing surface. -/
structure CoisotropicWitness
  {Point Vec : Type}
  (G : LocalPresymplecticGeometry Point Vec) where
  characteristic_in_tangent :
    pointwise_subdistribution G.characteristic G.tangentSpace

/-- Local generator chart witnessing a coisotropic normal form. -/
structure CoisotropicNormalForm
  {Point Vec Generator : Type}
  (characteristic : Point -> Vec -> Prop)
  where
  spans : Generator -> Point -> Vec -> Prop
  complete : generated_by_family characteristic spans

/-- A nondegenerate standing form blocks every characteristic direction. -/
def standing_form_nondegenerate
  {Point Vec : Type}
  (characteristic : Point -> Vec -> Prop) : Prop :=
  forall x v, Not (characteristic x v)

/-- Characteristic identification packaged as pointwise equality. -/
theorem characteristic_identification_of_witness
  {Point Vec : Type}
  (G : LocalPresymplecticGeometry Point Vec)
  (h_id : CharacteristicIdentificationWitness G) :
  pointwise_distribution_eq G.vertical G.characteristic := by
  exact And.intro h_id.vertical_to_characteristic h_id.characteristic_to_vertical

/-- A coisotropic witness promotes characteristic directions into tangent ones. -/
theorem coisotropic_surface_of_witness
  {Point Vec : Type}
  (G : LocalPresymplecticGeometry Point Vec)
  (h_coiso : CoisotropicWitness G) :
  coisotropic_surface G.characteristic G.tangentSpace := by
  intro x v hv
  exact h_coiso.characteristic_in_tangent x v hv

/-- Stage-II support: identification plus coisotropic witness yields the paper surface. -/
theorem local_presymplectic_geometry_supports_stageII
  {Point Vec : Type}
  (G : LocalPresymplecticGeometry Point Vec)
  (h_id : CharacteristicIdentificationWitness G)
  (h_coiso : CoisotropicWitness G) :
  pointwise_distribution_eq G.vertical G.characteristic /\
  coisotropic_surface G.characteristic G.tangentSpace := by
  exact And.intro
    (characteristic_identification_of_witness G h_id)
    (coisotropic_surface_of_witness G h_coiso)

/-- A local normal-form chart immediately certifies generator span. -/
theorem coisotropic_normal_form_supports_generator_span
  {Point Vec Generator : Type}
  (characteristic : Point -> Vec -> Prop)
  (N : CoisotropicNormalForm (Generator := Generator) characteristic) :
  generated_by_family characteristic N.spans := by
  exact N.complete

/--
Combining characteristic identification with a normal-form chart yields the
paper's admissible-generator span conclusion.
-/
theorem local_presymplectic_geometry_supports_constraint_span
  {Point Vec Generator : Type}
  (G : LocalPresymplecticGeometry Point Vec)
  (h_id : CharacteristicIdentificationWitness G)
  (N : CoisotropicNormalForm (Generator := Generator) G.characteristic) :
  generated_by_family G.vertical N.spans := by
  exact
    PaperAERConstraintGeneratorsSpanStatement
      G.vertical
      G.characteristic
      N.spans
      (characteristic_identification_of_witness G h_id)
      N.complete

/-- If the standing form is nondegenerate, redescription becomes trivial. -/
theorem standing_form_nondegenerate_forces_trivial_redescription
  {Point Vec : Type}
  (G : LocalPresymplecticGeometry Point Vec)
  (h_id : CharacteristicIdentificationWitness G)
  (h_nondeg : standing_form_nondegenerate G.characteristic) :
  trivial_redescription G.vertical := by
  exact
    PaperAERSecondClassExclusionStatement
      G.vertical
      G.characteristic
      (characteristic_identification_of_witness G h_id)
      h_nondeg

/-- Finite toy carrier for a tiny local coisotropic chart. -/
inductive ToyPhasePoint where
  | p0
deriving DecidableEq, Repr

/-- Two local directions: one vertical/characteristic, one transverse. -/
inductive ToyPhaseVec where
  | gaugeDir
  | transverseDir
deriving DecidableEq, Repr

/-- A single local generator for the toy coisotropic chart. -/
inductive ToyConstraintGenerator where
  | phi
deriving DecidableEq, Repr

/-- Tiny toy presymplectic geometry with a one-dimensional characteristic kernel. -/
def toyLocalPresymplecticGeometry :
  LocalPresymplecticGeometry ToyPhasePoint ToyPhaseVec where
  tangentSpace _ _ := True
  vertical _ v := v = ToyPhaseVec.gaugeDir
  characteristic _ v := v = ToyPhaseVec.gaugeDir

/-- The toy geometry has identified vertical and characteristic directions. -/
def toyCharacteristicIdentificationWitness :
  CharacteristicIdentificationWitness toyLocalPresymplecticGeometry where
  vertical_to_characteristic := by
    intro x v hv
    exact hv
  characteristic_to_vertical := by
    intro x v hv
    exact hv

/-- The toy geometry is trivially coisotropic because all tangent directions are admitted. -/
def toyCoisotropicWitness :
  CoisotropicWitness toyLocalPresymplecticGeometry where
  characteristic_in_tangent := by
    intro x v hv
    trivial

/-- The toy characteristic direction is generated by a single constraint. -/
def toyCoisotropicNormalForm :
  CoisotropicNormalForm
    (Generator := ToyConstraintGenerator)
    toyLocalPresymplecticGeometry.characteristic where
  spans g x v :=
    g = ToyConstraintGenerator.phi /\ v = ToyPhaseVec.gaugeDir
  complete := by
    intro x v
    constructor
    · intro hv
      refine ⟨ToyConstraintGenerator.phi, ?_⟩
      exact And.intro rfl hv
    · intro hv
      rcases hv with ⟨g, hg, hv⟩
      exact hv

/-- Concrete Stage-II witness from the toy local presymplectic chart. -/
theorem toy_stageII_geometry :
  pointwise_distribution_eq
      toyLocalPresymplecticGeometry.vertical
      toyLocalPresymplecticGeometry.characteristic /\
  coisotropic_surface
      toyLocalPresymplecticGeometry.characteristic
      toyLocalPresymplecticGeometry.tangentSpace := by
  exact
    local_presymplectic_geometry_supports_stageII
      toyLocalPresymplecticGeometry
      toyCharacteristicIdentificationWitness
      toyCoisotropicWitness

/-- Concrete Stage-III generator-span witness from the toy local chart. -/
theorem toy_constraint_generator_span :
  generated_by_family
    toyLocalPresymplecticGeometry.vertical
    toyCoisotropicNormalForm.spans := by
  exact
    local_presymplectic_geometry_supports_constraint_span
      toyLocalPresymplecticGeometry
      toyCharacteristicIdentificationWitness
      toyCoisotropicNormalForm

end MaleyLean
