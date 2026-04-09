import MaleyLean.Papers.YangMills.Kernel.ClosedInstantiatedManuscript

namespace MaleyLean

/--
Manuscript-facing names for the closed instantiated Yang--Mills manuscript
objects.

These do not yet create a closed manuscript constant. They do, however, give
explicit Lean names to the constructive, vacuum-gap, and endpoint chosen-site
objects that the manuscript draft refers to informally as `Delta_max`,
`omega_bd`, `omega_sharp`, `Hloc`, `Omega_loc`, `phi_star`, `E_ren`, and
related symbols.
-/

def ym_DeltaMax
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsConstructiveSemanticBundleData
    I.blueprint.objects.RC
    I.blueprint.witnesses.htrunc
    I.blueprint.witnesses.hext
    I.blueprint.witnesses.hcompat
    I.blueprint.witnesses.hunion).finite_cap_window :=
  I.chosen_sites.constructive.win

def ym_finite_cap_bridge
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsConstructiveSemanticBundleData
    I.blueprint.objects.RC
    I.blueprint.witnesses.htrunc
    I.blueprint.witnesses.hext
    I.blueprint.witnesses.hcompat
    I.blueprint.witnesses.hunion).positive_bridge_map :=
  I.chosen_sites.constructive.bridge

def ym_bounded_base_one
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsConstructiveSemanticBundleData
    I.blueprint.objects.RC
    I.blueprint.witnesses.htrunc
    I.blueprint.witnesses.hext
    I.blueprint.witnesses.hcompat
    I.blueprint.witnesses.hunion).bounded_base_carrier :=
  I.chosen_sites.constructive.base

def ym_omega_bd
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsConstructiveSemanticBundleData
    I.blueprint.objects.RC
    I.blueprint.witnesses.htrunc
    I.blueprint.witnesses.hext
    I.blueprint.witnesses.hcompat
    I.blueprint.witnesses.hunion).bounded_state_data :=
  I.chosen_sites.constructive.state

def ym_omega_sharp
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsConstructiveSemanticBundleData
    I.blueprint.objects.RC
    I.blueprint.witnesses.htrunc
    I.blueprint.witnesses.hext
    I.blueprint.witnesses.hcompat
    I.blueprint.witnesses.hunion).inductive_union_data :=
  I.chosen_sites.constructive.unionData

def ym_transport
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsVacuumGapSemanticBundleData
    I.blueprint.objects.RD
    I.blueprint.witnesses.hww).transport_map :=
  I.chosen_sites.vacuum_gap.tm

def ym_H
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsVacuumGapSemanticBundleData
    I.blueprint.objects.RD
    I.blueprint.witnesses.hww).lattice_observable_family :=
  I.chosen_sites.vacuum_gap.obs

def ym_Hloc
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsVacuumGapSemanticBundleData
    I.blueprint.objects.RD
    I.blueprint.witnesses.hww).reconstructed_sector :=
  I.chosen_sites.vacuum_gap.rsec

def ym_corr
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsVacuumGapSemanticBundleData
    I.blueprint.objects.RD
    I.blueprint.witnesses.hww).os_correlation_family :=
  I.chosen_sites.vacuum_gap.corr

def ym_gapf
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsVacuumGapSemanticBundleData
    I.blueprint.objects.RD
    I.blueprint.witnesses.hww).minkowski_gap_functional :=
  I.chosen_sites.vacuum_gap.gapf

def ym_hgap_statement
  (I : YMClosedInstantiatedManuscript) : Prop :=
  (YangMillsVacuumGapSemanticBundleData
    I.blueprint.objects.RD
    I.blueprint.witnesses.hww).evaluate_minkowski_gap
      (ym_gapf I)
      ((YangMillsVacuumGapSemanticBundleData
        I.blueprint.objects.RD
        I.blueprint.witnesses.hww).realize_os_sector
          (ym_Hloc I)
          (ym_corr I))

def ym_hgap
  (I : YMClosedInstantiatedManuscript) :
  ym_hgap_statement I :=
  I.chosen_sites.vacuum_gap.hgap

def ym_Omega_loc
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsEndpointSemanticBundleData
    I.blueprint.objects.RE
    I.blueprint.witnesses.hE
    I.blueprint.witnesses.hP).vacuum_vector :=
  I.chosen_sites.endpoint.vac

def ym_phi_star
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsEndpointSemanticBundleData
    I.blueprint.objects.RE
    I.blueprint.witnesses.hE
    I.blueprint.witnesses.hP).test_function_space :=
  I.chosen_sites.endpoint.testFn

def ym_E_ren
  (I : YMClosedInstantiatedManuscript) :
  (YangMillsEndpointSemanticBundleData
    I.blueprint.objects.RE
    I.blueprint.witnesses.hE
    I.blueprint.witnesses.hP).field_family :=
  I.chosen_sites.endpoint.field

theorem YangMillsManuscriptNamedObjectsStatement
  (I : YMClosedInstantiatedManuscript) :
  ym_DeltaMax I = I.chosen_sites.constructive.win /\
  ym_finite_cap_bridge I = I.chosen_sites.constructive.bridge /\
  ym_bounded_base_one I = I.chosen_sites.constructive.base /\
  ym_omega_bd I = I.chosen_sites.constructive.state /\
  ym_omega_sharp I = I.chosen_sites.constructive.unionData /\
  ym_transport I = I.chosen_sites.vacuum_gap.tm /\
  ym_H I = I.chosen_sites.vacuum_gap.obs /\
  ym_Hloc I = I.chosen_sites.vacuum_gap.rsec /\
  ym_corr I = I.chosen_sites.vacuum_gap.corr /\
  ym_gapf I = I.chosen_sites.vacuum_gap.gapf /\
  ym_hgap_statement I /\
  ym_Omega_loc I = I.chosen_sites.endpoint.vac /\
  ym_phi_star I = I.chosen_sites.endpoint.testFn /\
  ym_E_ren I = I.chosen_sites.endpoint.field := by
  exact And.intro rfl <|
    And.intro rfl <|
      And.intro rfl <|
        And.intro rfl <|
          And.intro rfl <|
            And.intro rfl <|
              And.intro rfl <|
                And.intro rfl <|
                  And.intro rfl <|
                    And.intro rfl <|
                      And.intro (ym_hgap I) <|
                        And.intro rfl <|
                          And.intro rfl rfl

end MaleyLean
