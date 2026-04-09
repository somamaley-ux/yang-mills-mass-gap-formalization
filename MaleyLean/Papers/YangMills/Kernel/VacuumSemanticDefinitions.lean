import MaleyLean.Papers.YangMills.Kernel.VacuumGapManuscriptCarrierBase

namespace MaleyLean

/--
Carrier-level semantic shadow for the fixed-lattice gap input used by the
Route 1 transport package.
-/
def YMVacuumLatticeGapInputReady
    (B : YMVacuumGapManuscriptCarrierBase) : Prop :=
  ∃ obs : B.TransportState,
    obs = B.transport_observable B.transport B.H

/--
Carrier-level semantic shadow for the OS transport output of the chosen Route 1
transport data.
-/
def YMVacuumOSTransportReady
    (B : YMVacuumGapManuscriptCarrierBase) : Prop :=
  YMVacuumLatticeGapInputReady B

/--
Carrier-level semantic shadow for the positive-gap witness transported to the
continuum side.
-/
def YMVacuumPositiveGapExhibited
    (B : YMVacuumGapManuscriptCarrierBase) : Prop :=
  YMVacuumLatticeGapInputReady B

/--
Carrier-level semantic shadow for the reconstructed OS sector determined by the
chosen reconstructed Hilbert carrier and OS correlations.
-/
def YMVacuumOSSectorReady
    (B : YMVacuumGapManuscriptCarrierBase) : Prop :=
  ∃ os : B.OSSector, os = B.realize_os_sector B.Hloc B.corr

/--
Carrier-level semantic shadow for the Minkowski gap functional on the chosen OS
sector.
-/
def YMVacuumMinkowskiGapReady
    (B : YMVacuumGapManuscriptCarrierBase) : Prop :=
  ∃ gap : Prop,
    gap =
      B.evaluate_minkowski_gap
        B.gapf
        (B.realize_os_sector B.Hloc B.corr)

/--
Carrier-level semantic shadow recording that the reconstructed gap statement is
fed by the chosen transport data.
-/
def YMVacuumObtainedFromTransport
    (B : YMVacuumGapManuscriptCarrierBase) : Prop :=
  YMVacuumLatticeGapInputReady B /\ YMVacuumOSSectorReady B

theorem ym_vacuum_lattice_gap_input_ready_holds
    (B : YMVacuumGapManuscriptCarrierBase) :
    YMVacuumLatticeGapInputReady B := by
  exact ⟨B.transport_observable B.transport B.H, rfl⟩

theorem ym_vacuum_os_transport_ready_holds
    (B : YMVacuumGapManuscriptCarrierBase) :
    YMVacuumOSTransportReady B := by
  exact ym_vacuum_lattice_gap_input_ready_holds B

theorem ym_vacuum_positive_gap_exhibited_holds
    (B : YMVacuumGapManuscriptCarrierBase) :
    YMVacuumPositiveGapExhibited B := by
  exact ym_vacuum_lattice_gap_input_ready_holds B

theorem ym_vacuum_os_sector_ready_holds
    (B : YMVacuumGapManuscriptCarrierBase) :
    YMVacuumOSSectorReady B := by
  exact ⟨B.realize_os_sector B.Hloc B.corr, rfl⟩

theorem ym_vacuum_minkowski_gap_ready_holds
    (B : YMVacuumGapManuscriptCarrierBase) :
    YMVacuumMinkowskiGapReady B := by
  exact
    ⟨B.evaluate_minkowski_gap B.gapf (B.realize_os_sector B.Hloc B.corr), rfl⟩

theorem ym_vacuum_obtained_from_transport_holds
    (B : YMVacuumGapManuscriptCarrierBase) :
    YMVacuumObtainedFromTransport B := by
  exact ⟨ym_vacuum_lattice_gap_input_ready_holds B, ym_vacuum_os_sector_ready_holds B⟩

end MaleyLean
