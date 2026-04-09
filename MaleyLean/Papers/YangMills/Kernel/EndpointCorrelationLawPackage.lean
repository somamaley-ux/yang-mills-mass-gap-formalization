import MaleyLean.Papers.YangMills.Kernel.EndpointRelationalInterface

namespace MaleyLean

/--
Structured endpoint-side law package organizing the composed
smear-then-correlate operation around one chosen relational evaluation site.
-/
structure YMEndpointCorrelationLawPackage (R : YMEndpointCore) where
  interface : YMEndpointRelationalInterface R
  correlate_smeared_field :
    interface.bundle.vacuum_vector ->
    interface.bundle.test_function_space ->
    interface.bundle.field_family ->
    interface.bundle.vacuum_correlation_family
  chosen_site_law :
    correlate_smeared_field
      interface.chosen_vacuum_vector
      interface.chosen_test_function
      interface.chosen_field =
      interface.chosen_vacuum_correlation
  exact_endpoint_from_correlations :
    R.reconstruction_package.vacuum_correlations_defined ->
    R.endpoint_object.exact_local_net_endpoint
  exact_endpoint_witness : R.endpoint_object.exact_local_net_endpoint

def YangMillsEndpointCorrelationLawPackageData
  (R : YMEndpointCore)
  (hE : R.euclidean_dossier_ready)
  (hP : R.endpoint_packet_ready)
  (vac : (YangMillsEndpointSemanticBundleData R hE hP).vacuum_vector)
  (testFn : (YangMillsEndpointSemanticBundleData R hE hP).test_function_space)
  (field : (YangMillsEndpointSemanticBundleData R hE hP).field_family) :
  YMEndpointCorrelationLawPackage R := by
  let I := YangMillsEndpointRelationalInterfaceData R hE hP vac testFn field
  refine
    { interface := I
      correlate_smeared_field := fun vac' testFn' field' =>
        I.bundle.evaluate_vacuum_correlation vac' (I.bundle.smear_field testFn' field')
      chosen_site_law := by
        calc
          I.bundle.evaluate_vacuum_correlation
              I.chosen_vacuum_vector
              (I.bundle.smear_field I.chosen_test_function I.chosen_field)
              =
            I.bundle.evaluate_vacuum_correlation
              I.chosen_vacuum_vector
              I.chosen_smeared_operator := by
                rw [I.smearing_relation]
          _ = I.chosen_vacuum_correlation := I.vacuum_correlation_relation
      exact_endpoint_from_correlations := by
        intro _
        exact I.bundle.exact_endpoint
      exact_endpoint_witness := I.bundle.exact_endpoint }

theorem YangMillsEndpointCorrelationLawPackageExistsStatement
  (R : YMEndpointCore)
  (hE : R.euclidean_dossier_ready)
  (hP : R.endpoint_packet_ready)
  (vac : (YangMillsEndpointSemanticBundleData R hE hP).vacuum_vector)
  (testFn : (YangMillsEndpointSemanticBundleData R hE hP).test_function_space)
  (field : (YangMillsEndpointSemanticBundleData R hE hP).field_family) :
  Nonempty (YMEndpointCorrelationLawPackage R) := by
  exact Nonempty.intro (YangMillsEndpointCorrelationLawPackageData R hE hP vac testFn field)

theorem YangMillsEndpointCorrelationLawPackageWitnessStatement
  (R : YMEndpointCore)
  (hE : R.euclidean_dossier_ready)
  (hP : R.endpoint_packet_ready)
  (vac : (YangMillsEndpointSemanticBundleData R hE hP).vacuum_vector)
  (testFn : (YangMillsEndpointSemanticBundleData R hE hP).test_function_space)
  (field : (YangMillsEndpointSemanticBundleData R hE hP).field_family) :
  let P := YangMillsEndpointCorrelationLawPackageData R hE hP vac testFn field
  Nonempty (YMEndpointCorrelationLawPackage R) /\
  P.correlate_smeared_field vac testFn field = P.interface.chosen_vacuum_correlation /\
  R.endpoint_object.exact_local_net_endpoint := by
  let P := YangMillsEndpointCorrelationLawPackageData R hE hP vac testFn field
  exact And.intro
    (Nonempty.intro P)
    (And.intro P.chosen_site_law P.exact_endpoint_witness)

end MaleyLean
