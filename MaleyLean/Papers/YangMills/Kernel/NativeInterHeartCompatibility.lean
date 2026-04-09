import MaleyLean.Papers.YangMills.Kernel.NativeLawAssembly

namespace MaleyLean

/--
Native inter-heart relation from the constructive native-law package to the
vacuum-gap native-law package.
-/
def YMNativeConstructiveToVacuumGapCompatibility
  (RC : YMConstructiveRoute)
  (RD : YMVacuumGapRoute) : Prop :=
  RC.sharp_local_package.sharp_local_state.extends_bounded_base ->
  RD.reconstruction_package.minkowski_gap_ready

/--
Native inter-heart relation from the vacuum-gap native-law package to the
endpoint native-law package.
-/
def YMNativeVacuumGapToEndpointCompatibility
  (RD : YMVacuumGapRoute)
  (RE : YMEndpointCore) : Prop :=
  RD.reconstruction_package.minkowski_gap_ready ->
  RE.endpoint_object.exact_local_net_endpoint

/--
Native inter-heart relation from the constructive native-law package directly
to the endpoint native-law package.
-/
def YMNativeConstructiveToEndpointCompatibility
  (RC : YMConstructiveRoute)
  (RE : YMEndpointCore) : Prop :=
  RC.sharp_local_package.sharp_local_state.extends_bounded_base ->
  RE.endpoint_object.exact_local_net_endpoint

/--
Native state-level bridge from constructive sharp-local states to vacuum-gap
readiness.
-/
def YMNativeConstructiveStateToVacuumGapReadiness
  (RD : YMVacuumGapRoute) : Type 1 :=
  YMSharpLocalState -> PLift RD.reconstruction_package.minkowski_gap_ready

structure YMNativeInterHeartCompatibility
    (RC : YMConstructiveRoute)
    (RD : YMVacuumGapRoute)
    (RE : YMEndpointCore) where
  constructive_to_vacuum_gap : YMNativeConstructiveToVacuumGapCompatibility RC RD
  constructive_state_to_vacuum_gap : YMNativeConstructiveStateToVacuumGapReadiness RD
  vacuum_gap_to_endpoint : YMNativeVacuumGapToEndpointCompatibility RD RE
  constructive_to_endpoint : YMNativeConstructiveToEndpointCompatibility RC RE

def YangMillsNativeConstructiveToVacuumGapCompatibilityData
  (RC : YMConstructiveRoute)
  (RD : YMVacuumGapRoute)
  (RE : YMEndpointCore)
  (A : YMNativeLawAssembly RC RD RE) :
  YMNativeConstructiveToVacuumGapCompatibility RC RD := by
  intro _
  exact A.vacuum_gap.minkowski_gap_witness

def YangMillsNativeVacuumGapToEndpointCompatibilityData
  (RC : YMConstructiveRoute)
  (RD : YMVacuumGapRoute)
  (RE : YMEndpointCore)
  (A : YMNativeLawAssembly RC RD RE) :
  YMNativeVacuumGapToEndpointCompatibility RD RE := by
  intro _
  exact A.endpoint.exact_endpoint_witness

def YangMillsNativeConstructiveToEndpointCompatibilityData
  (RC : YMConstructiveRoute)
  (RD : YMVacuumGapRoute)
  (RE : YMEndpointCore)
  (A : YMNativeLawAssembly RC RD RE) :
  YMNativeConstructiveToEndpointCompatibility RC RE := by
  intro _
  exact A.endpoint.exact_endpoint_witness

def YangMillsNativeConstructiveStateToVacuumGapReadinessData
  (RC : YMConstructiveRoute)
  (RD : YMVacuumGapRoute)
  (RE : YMEndpointCore)
  (A : YMNativeLawAssembly RC RD RE) :
  YMNativeConstructiveStateToVacuumGapReadiness RD :=
  fun _ => ⟨A.vacuum_gap.minkowski_gap_witness⟩

def YangMillsNativeInterHeartCompatibilityData
  (RC : YMConstructiveRoute)
  (RD : YMVacuumGapRoute)
  (RE : YMEndpointCore)
  (htrunc : RC.finite_truncation_ready)
  (hext : RC.finite_cap_extension_ready)
  (hcompat : RC.bounded_state_compatibility_ready)
  (hunion : RC.inductive_union_ready)
  (cwin : (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).finite_cap_window)
  (cbridge :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).positive_bridge_map)
  (cbase :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).bounded_base_carrier)
  (cstate :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).bounded_state_data)
  (cunion :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).inductive_union_data)
  (hww : RD.weak_window_certificate_ready)
  (vtm : (YangMillsVacuumGapSemanticBundleData RD hww).transport_map)
  (vobs : (YangMillsVacuumGapSemanticBundleData RD hww).lattice_observable_family)
  (vrsec : (YangMillsVacuumGapSemanticBundleData RD hww).reconstructed_sector)
  (vcorr : (YangMillsVacuumGapSemanticBundleData RD hww).os_correlation_family)
  (vgapf : (YangMillsVacuumGapSemanticBundleData RD hww).minkowski_gap_functional)
  (vhgap :
    (YangMillsVacuumGapSemanticBundleData RD hww).evaluate_minkowski_gap
      vgapf
      ((YangMillsVacuumGapSemanticBundleData RD hww).realize_os_sector vrsec vcorr))
  (hE : RE.euclidean_dossier_ready)
  (hP : RE.endpoint_packet_ready)
  (evac : (YangMillsEndpointSemanticBundleData RE hE hP).vacuum_vector)
  (etest : (YangMillsEndpointSemanticBundleData RE hE hP).test_function_space)
  (efield : (YangMillsEndpointSemanticBundleData RE hE hP).field_family) :
  YMNativeInterHeartCompatibility RC RD RE := by
  let A := YangMillsNativeLawAssemblyData
    RC RD RE
    htrunc hext hcompat hunion cwin cbridge cbase cstate cunion
    hww vtm vobs vrsec vcorr vgapf vhgap
    hE hP evac etest efield
  refine
    { constructive_to_vacuum_gap :=
        YangMillsNativeConstructiveToVacuumGapCompatibilityData RC RD RE A
      constructive_state_to_vacuum_gap :=
        YangMillsNativeConstructiveStateToVacuumGapReadinessData RC RD RE A
      vacuum_gap_to_endpoint :=
        YangMillsNativeVacuumGapToEndpointCompatibilityData RC RD RE A
      constructive_to_endpoint :=
        YangMillsNativeConstructiveToEndpointCompatibilityData RC RD RE A }

theorem YangMillsNativeInterHeartCompatibilityExistsStatement
  (RC : YMConstructiveRoute)
  (RD : YMVacuumGapRoute)
  (RE : YMEndpointCore)
  (htrunc : RC.finite_truncation_ready)
  (hext : RC.finite_cap_extension_ready)
  (hcompat : RC.bounded_state_compatibility_ready)
  (hunion : RC.inductive_union_ready)
  (cwin : (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).finite_cap_window)
  (cbridge :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).positive_bridge_map)
  (cbase :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).bounded_base_carrier)
  (cstate :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).bounded_state_data)
  (cunion :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).inductive_union_data)
  (hww : RD.weak_window_certificate_ready)
  (vtm : (YangMillsVacuumGapSemanticBundleData RD hww).transport_map)
  (vobs : (YangMillsVacuumGapSemanticBundleData RD hww).lattice_observable_family)
  (vrsec : (YangMillsVacuumGapSemanticBundleData RD hww).reconstructed_sector)
  (vcorr : (YangMillsVacuumGapSemanticBundleData RD hww).os_correlation_family)
  (vgapf : (YangMillsVacuumGapSemanticBundleData RD hww).minkowski_gap_functional)
  (vhgap :
    (YangMillsVacuumGapSemanticBundleData RD hww).evaluate_minkowski_gap
      vgapf
      ((YangMillsVacuumGapSemanticBundleData RD hww).realize_os_sector vrsec vcorr))
  (hE : RE.euclidean_dossier_ready)
  (hP : RE.endpoint_packet_ready)
  (evac : (YangMillsEndpointSemanticBundleData RE hE hP).vacuum_vector)
  (etest : (YangMillsEndpointSemanticBundleData RE hE hP).test_function_space)
  (efield : (YangMillsEndpointSemanticBundleData RE hE hP).field_family) :
  Nonempty (YMNativeInterHeartCompatibility RC RD RE) := by
  exact ⟨YangMillsNativeInterHeartCompatibilityData
    RC RD RE
    htrunc hext hcompat hunion cwin cbridge cbase cstate cunion
    hww vtm vobs vrsec vcorr vgapf vhgap
    hE hP evac etest efield⟩

theorem YangMillsNativeInterHeartCompatibilityWitnessStatement
  (RC : YMConstructiveRoute)
  (RD : YMVacuumGapRoute)
  (RE : YMEndpointCore)
  (htrunc : RC.finite_truncation_ready)
  (hext : RC.finite_cap_extension_ready)
  (hcompat : RC.bounded_state_compatibility_ready)
  (hunion : RC.inductive_union_ready)
  (cwin : (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).finite_cap_window)
  (cbridge :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).positive_bridge_map)
  (cbase :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).bounded_base_carrier)
  (cstate :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).bounded_state_data)
  (cunion :
    (YangMillsConstructiveSemanticBundleData RC htrunc hext hcompat hunion).inductive_union_data)
  (hww : RD.weak_window_certificate_ready)
  (vtm : (YangMillsVacuumGapSemanticBundleData RD hww).transport_map)
  (vobs : (YangMillsVacuumGapSemanticBundleData RD hww).lattice_observable_family)
  (vrsec : (YangMillsVacuumGapSemanticBundleData RD hww).reconstructed_sector)
  (vcorr : (YangMillsVacuumGapSemanticBundleData RD hww).os_correlation_family)
  (vgapf : (YangMillsVacuumGapSemanticBundleData RD hww).minkowski_gap_functional)
  (vhgap :
    (YangMillsVacuumGapSemanticBundleData RD hww).evaluate_minkowski_gap
      vgapf
      ((YangMillsVacuumGapSemanticBundleData RD hww).realize_os_sector vrsec vcorr))
  (hE : RE.euclidean_dossier_ready)
  (hP : RE.endpoint_packet_ready)
  (evac : (YangMillsEndpointSemanticBundleData RE hE hP).vacuum_vector)
  (etest : (YangMillsEndpointSemanticBundleData RE hE hP).test_function_space)
  (efield : (YangMillsEndpointSemanticBundleData RE hE hP).field_family) :
  Nonempty (YMNativeInterHeartCompatibility RC RD RE) /\
  YMNativeConstructiveToVacuumGapCompatibility RC RD /\
  YMNativeVacuumGapToEndpointCompatibility RD RE /\
  YMNativeConstructiveToEndpointCompatibility RC RE := by
  let C := YangMillsNativeInterHeartCompatibilityData
    RC RD RE
    htrunc hext hcompat hunion cwin cbridge cbase cstate cunion
    hww vtm vobs vrsec vcorr vgapf vhgap
    hE hP evac etest efield
  exact And.intro ⟨C⟩ <|
    And.intro C.constructive_to_vacuum_gap <|
      And.intro C.vacuum_gap_to_endpoint C.constructive_to_endpoint

end MaleyLean
