import MaleyLean.Papers.YangMills.Kernel.EndpointManuscriptCarrierBase

namespace MaleyLean

/--
Concrete manuscript-facing endpoint carrier declarations.

These are object-level declarations only: the carrier types, chosen inhabitants,
and basic operations needed to instantiate the endpoint packet's manuscript
base. They do not add any theorem-strengthening proof data.
-/
axiom EndpointEuclideanInput : Type
axiom EndpointReconstructedHilbert : Type
axiom EndpointFieldFamily : Type
axiom EndpointTestFunctionSpace : Type
axiom EndpointSmearedFieldOperator : Type
axiom EndpointVacuumCorrelationFamily : Type
axiom EndpointLocalNet : Type
axiom EndpointVacuumSector : Type

axiom endpoint_smear_field :
  EndpointTestFunctionSpace ->
  EndpointFieldFamily ->
  EndpointSmearedFieldOperator

axiom endpoint_evaluate_vacuum_correlation :
  EndpointReconstructedHilbert ->
  EndpointSmearedFieldOperator ->
  EndpointVacuumCorrelationFamily

/-- Reconstructed vacuum vector from the Appendix M reconstruction package. -/
axiom Omega_loc : EndpointReconstructedHilbert

/-- Canonical witness test function from the non-triviality witness theorem. -/
axiom phi_star : EndpointTestFunctionSpace

/-- Canonical centered CP-even dimension-4 scalar witness field. -/
axiom E_ren : EndpointFieldFamily

noncomputable def ym_endpoint_manuscript_carrier_base :
  YMEndpointManuscriptCarrierBase :=
  { EndpointEuclideanInput := EndpointEuclideanInput
    EndpointReconstructedHilbert := EndpointReconstructedHilbert
    EndpointFieldFamily := EndpointFieldFamily
    EndpointTestFunctionSpace := EndpointTestFunctionSpace
    EndpointSmearedFieldOperator := EndpointSmearedFieldOperator
    EndpointVacuumCorrelationFamily := EndpointVacuumCorrelationFamily
    EndpointLocalNet := EndpointLocalNet
    EndpointVacuumSector := EndpointVacuumSector
    smear_field := endpoint_smear_field
    evaluate_vacuum_correlation := endpoint_evaluate_vacuum_correlation
    Omega_loc := Omega_loc
    phi_star := phi_star
    E_ren := E_ren }

theorem ym_endpoint_manuscript_carrier_base_named_outputs :
  ym_endpoint_manuscript_carrier_base.Omega_loc = Omega_loc /\
  ym_endpoint_manuscript_carrier_base.phi_star = phi_star /\
  ym_endpoint_manuscript_carrier_base.E_ren = E_ren := by
  exact ⟨rfl, rfl, rfl⟩

end MaleyLean
