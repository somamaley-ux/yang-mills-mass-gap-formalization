import MaleyLean.Papers.YangMills.Kernel.VacuumGapManuscriptCarrierBase

namespace MaleyLean

axiom VacuumTransportState : Type
axiom VacuumLatticeObservableFamily : Type
axiom VacuumTransportMap : Type
axiom VacuumReconstructedSector : Type
axiom VacuumOSSector : Type
axiom VacuumMinkowskiGapFunctional : Type
axiom VacuumOSCorrelationFamily : Type

axiom vacuum_transport_observable :
  VacuumTransportMap ->
  VacuumLatticeObservableFamily ->
  VacuumTransportState

axiom vacuum_realize_os_sector :
  VacuumReconstructedSector ->
  VacuumOSCorrelationFamily ->
  VacuumOSSector

axiom vacuum_evaluate_minkowski_gap :
  VacuumMinkowskiGapFunctional ->
  VacuumOSSector ->
  Prop

axiom vacuum_transport : VacuumTransportMap
axiom vacuum_H : VacuumLatticeObservableFamily
axiom vacuum_Hloc : VacuumReconstructedSector
axiom vacuum_corr : VacuumOSCorrelationFamily
axiom vacuum_gapf : VacuumMinkowskiGapFunctional
axiom vacuum_hgap :
  vacuum_evaluate_minkowski_gap
    vacuum_gapf
    (vacuum_realize_os_sector vacuum_Hloc vacuum_corr)

noncomputable def ym_vacuum_gap_manuscript_carrier_base :
  YMVacuumGapManuscriptCarrierBase :=
  { TransportState := VacuumTransportState
    LatticeObservableFamily := VacuumLatticeObservableFamily
    TransportMap := VacuumTransportMap
    ReconstructedSector := VacuumReconstructedSector
    OSSector := VacuumOSSector
    MinkowskiGapFunctional := VacuumMinkowskiGapFunctional
    OSCorrelationFamily := VacuumOSCorrelationFamily
    transport_observable := vacuum_transport_observable
    realize_os_sector := vacuum_realize_os_sector
    evaluate_minkowski_gap := vacuum_evaluate_minkowski_gap
    transport := vacuum_transport
    H := vacuum_H
    Hloc := vacuum_Hloc
    corr := vacuum_corr
    gapf := vacuum_gapf
    hgap := vacuum_hgap }

theorem ym_vacuum_gap_manuscript_carrier_base_named_inhabitants :
  ym_vacuum_gap_manuscript_carrier_base.transport = vacuum_transport /\
  ym_vacuum_gap_manuscript_carrier_base.H = vacuum_H /\
  ym_vacuum_gap_manuscript_carrier_base.Hloc = vacuum_Hloc /\
  ym_vacuum_gap_manuscript_carrier_base.corr = vacuum_corr /\
  ym_vacuum_gap_manuscript_carrier_base.gapf = vacuum_gapf /\
  ym_vacuum_gap_manuscript_carrier_base.hgap = vacuum_hgap := by
  exact And.intro rfl <| And.intro rfl <| And.intro rfl <| And.intro rfl <| And.intro rfl rfl

end MaleyLean
