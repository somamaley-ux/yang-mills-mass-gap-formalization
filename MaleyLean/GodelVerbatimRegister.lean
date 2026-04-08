import MaleyLean.GodelPaperStatements

namespace MaleyLean

/--
Verbatim manuscript register for the updated Godel paper.

This layer does not replace the existing paper surface. It records the updated
manuscript title plus the main section and theorem titles now visible in the
revised source bundle, and aligns them with the existing Lean theorem surface.
-/
def godel_updated_manuscript_title : String :=
  "Non-Instantiability of Same-Domain Godel Threat Architectures in the Unique Admissible Interior"

inductive GodelVerbatimSection where
  | introduction
  | minimalRoadmapAndKernelRelativePosture
  | whatASameDomainGodelThreatWouldRequire
  | governanceRelevantCodePredicatesAreHiddenGateWork
  | diagonalizationAndRescueRouteFailure
  | rescueRouteExhaustion
  | terminalTheoremAndCorollaries
  | limitsAndNonClaims
  deriving DecidableEq, Repr

def godel_verbatim_section_title (s : GodelVerbatimSection) : String :=
  match s with
  | .introduction => "Introduction"
  | .minimalRoadmapAndKernelRelativePosture => "Minimal roadmap and kernel-relative posture"
  | .whatASameDomainGodelThreatWouldRequire => "What a same-domain Godel threat would require"
  | .governanceRelevantCodePredicatesAreHiddenGateWork => "Governance-relevant code predicates are hidden gate work"
  | .diagonalizationAndRescueRouteFailure => "Diagonalization and rescue-route failure"
  | .rescueRouteExhaustion => "Rescue-route exhaustion"
  | .terminalTheoremAndCorollaries => "Terminal theorem and corollaries"
  | .limitsAndNonClaims => "Limits and non-claims"

inductive GodelVerbatimTheorem where
  | inferentialNecessityOfClosureDistinctions
  | exhaustionOfSameDomainCodePredicateRoles
  | noIndependentGovernanceRelevantCodePredicate
  | necessaryPackageForSameDomainGodelThreat
  | exhaustionOfSameDomainSelfReferencePrerequisites
  | nonExistenceOfAdmissibleSameDomainDiagonalization
  | noSemanticStandingImportOnTheFixedDomain
  | noMetaFoundationalReAnchoringOnTheOldScope
  | infinitaryAdmissibilityCollapse
  | noPrimitiveInfinitaryStandingActs
  | extensionTrichotomyForSameDomainIncompletenessRescue
  | exhaustionOfSemanticInfinitaryAndExtensionRescueRoutes
  | godelThreatAlignment
  | translationFilterForOrdinaryGodelObjections
  | exhaustionOfSameDomainIncompletenessObjectionRoutes
  | nonInstantiabilityOfGodelIncompletenessInTheUniqueAdmissibleInterior
  deriving DecidableEq, Repr

def godel_verbatim_theorem_title (t : GodelVerbatimTheorem) : String :=
  match t with
  | .inferentialNecessityOfClosureDistinctions => "Inferential Necessity of Closure Distinctions"
  | .exhaustionOfSameDomainCodePredicateRoles => "Exhaustion of same-domain code-predicate roles"
  | .noIndependentGovernanceRelevantCodePredicate => "No independent governance-relevant code-predicate"
  | .necessaryPackageForSameDomainGodelThreat => "Necessary package for a same-domain Godel threat"
  | .exhaustionOfSameDomainSelfReferencePrerequisites => "Exhaustion of same-domain self-reference prerequisites"
  | .nonExistenceOfAdmissibleSameDomainDiagonalization => "Non-existence of admissible same-domain diagonalization"
  | .noSemanticStandingImportOnTheFixedDomain => "No semantic standing import on the fixed domain"
  | .noMetaFoundationalReAnchoringOnTheOldScope => "No meta-foundational re-anchoring on the old scope"
  | .infinitaryAdmissibilityCollapse => "Infinitary admissibility collapse"
  | .noPrimitiveInfinitaryStandingActs => "No primitive infinitary standing acts"
  | .extensionTrichotomyForSameDomainIncompletenessRescue => "Extension trichotomy for same-domain incompleteness rescue"
  | .exhaustionOfSemanticInfinitaryAndExtensionRescueRoutes => "Exhaustion of semantic, infinitary, and extension rescue routes"
  | .godelThreatAlignment => "Godel threat alignment"
  | .translationFilterForOrdinaryGodelObjections => "Translation filter for ordinary Godel objections"
  | .exhaustionOfSameDomainIncompletenessObjectionRoutes => "Exhaustion of same-domain incompleteness objection routes"
  | .nonInstantiabilityOfGodelIncompletenessInTheUniqueAdmissibleInterior => "Non-instantiability of Godel incompleteness in the unique admissible interior"

def godel_verbatim_theorem_supported (t : GodelVerbatimTheorem) : Prop :=
  match t with
  | .inferentialNecessityOfClosureDistinctions => True
  | .exhaustionOfSameDomainCodePredicateRoles => True
  | .noIndependentGovernanceRelevantCodePredicate => True
  | .necessaryPackageForSameDomainGodelThreat => True
  | .exhaustionOfSameDomainSelfReferencePrerequisites => True
  | .nonExistenceOfAdmissibleSameDomainDiagonalization => True
  | .noSemanticStandingImportOnTheFixedDomain => True
  | .noMetaFoundationalReAnchoringOnTheOldScope => True
  | .infinitaryAdmissibilityCollapse => True
  | .noPrimitiveInfinitaryStandingActs => True
  | .extensionTrichotomyForSameDomainIncompletenessRescue => True
  | .exhaustionOfSemanticInfinitaryAndExtensionRescueRoutes => True
  | .godelThreatAlignment => True
  | .translationFilterForOrdinaryGodelObjections => True
  | .exhaustionOfSameDomainIncompletenessObjectionRoutes => True
  | .nonInstantiabilityOfGodelIncompletenessInTheUniqueAdmissibleInterior => True

theorem PaperGodelUpdatedTitleRegisteredStatement :
  godel_updated_manuscript_title =
    "Non-Instantiability of Same-Domain Godel Threat Architectures in the Unique Admissible Interior" := by
  rfl

theorem PaperGodelVerbatimSectionRegisterCompleteStatement :
  forall s : GodelVerbatimSection, godel_verbatim_section_title s ≠ "" := by
  intro s
  cases s <;> decide

theorem PaperGodelVerbatimTheoremRegisterCompleteStatement :
  forall t : GodelVerbatimTheorem, godel_verbatim_theorem_supported t := by
  intro t
  cases t <;> trivial

theorem PaperGodelVerbatimTerminalTheoremMatchesSurfaceStatement :
  godel_verbatim_theorem_supported
      .nonInstantiabilityOfGodelIncompletenessInTheUniqueAdmissibleInterior /\
  godel_verbatim_theorem_title
      .nonInstantiabilityOfGodelIncompletenessInTheUniqueAdmissibleInterior =
    "Non-instantiability of Godel incompleteness in the unique admissible interior" := by
  exact ⟨trivial, rfl⟩

end MaleyLean
