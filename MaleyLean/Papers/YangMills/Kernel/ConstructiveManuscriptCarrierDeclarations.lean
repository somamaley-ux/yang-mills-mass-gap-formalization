import MaleyLean.Papers.YangMills.Kernel.ConstructiveManuscriptCarrierBase

namespace MaleyLean

/--
Concrete manuscript-facing constructive carrier declarations.

These are object-level declarations only: carrier types, chosen inhabitants,
and basic operations needed to instantiate the constructive packet's manuscript
base. They do not add theorem-strengthening proof data.
-/
axiom ConstructiveFiniteCapWindow : Type
axiom ConstructiveFiniteCapExtensionData : Type
axiom ConstructivePositiveBridgeMap : Type
axiom ConstructiveBoundedBaseCarrier : Type
axiom ConstructiveBoundedStateData : Type
axiom ConstructiveInductiveUnionData : Type

axiom constructive_extend_finite_cap :
  ConstructiveFiniteCapWindow ->
  ConstructivePositiveBridgeMap ->
  ConstructiveFiniteCapExtensionData

axiom constructive_assemble_sharp_local_state :
  ConstructiveBoundedBaseCarrier ->
  ConstructiveBoundedStateData ->
  ConstructiveInductiveUnionData ->
  YMSharpLocalState

axiom DeltaMax : ConstructiveFiniteCapWindow
axiom constructive_finite_cap_bridge : ConstructivePositiveBridgeMap
axiom constructive_bounded_base_one : ConstructiveBoundedBaseCarrier
axiom constructive_omega_bd : ConstructiveBoundedStateData
axiom constructive_omega_sharp : ConstructiveInductiveUnionData

noncomputable def ym_constructive_manuscript_carrier_base :
  YMConstructiveManuscriptCarrierBase :=
  { FiniteCapWindow := ConstructiveFiniteCapWindow
    FiniteCapExtensionData := ConstructiveFiniteCapExtensionData
    PositiveBridgeMap := ConstructivePositiveBridgeMap
    BoundedBaseCarrier := ConstructiveBoundedBaseCarrier
    BoundedStateData := ConstructiveBoundedStateData
    InductiveUnionData := ConstructiveInductiveUnionData
    extend_finite_cap := constructive_extend_finite_cap
    assemble_sharp_local_state := constructive_assemble_sharp_local_state
    DeltaMax := DeltaMax
    finite_cap_bridge := constructive_finite_cap_bridge
    bounded_base_one := constructive_bounded_base_one
    omega_bd := constructive_omega_bd
    omega_sharp := constructive_omega_sharp }

theorem ym_constructive_manuscript_carrier_base_named_inhabitants :
  ym_constructive_manuscript_carrier_base.DeltaMax = DeltaMax /\
  ym_constructive_manuscript_carrier_base.finite_cap_bridge = constructive_finite_cap_bridge /\
  ym_constructive_manuscript_carrier_base.bounded_base_one = constructive_bounded_base_one /\
  ym_constructive_manuscript_carrier_base.omega_bd = constructive_omega_bd /\
  ym_constructive_manuscript_carrier_base.omega_sharp = constructive_omega_sharp := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end MaleyLean
