import MaleyLean.Papers.YangMills.Verbatim.TheoremRegister
import MaleyLean.Papers.YangMills.Kernel.ConstructiveCore
import MaleyLean.Papers.YangMills.Kernel.VacuumGapCore
import MaleyLean.Papers.YangMills.Kernel.EndpointCore

namespace MaleyLean

/--
Register-keyed Lane A claim family taken as the paper-facing Part C boundary.
-/
def ym_laneA_verbatim_claim_family : Prop :=
  ym_verbatim_theorem_section .finiteCapSharpLocalExtension =
      .laneASharpLocalConstruction /\
    ym_verbatim_theorem_section .passageToFullSharpLocalInductiveUnion =
      .laneASharpLocalConstruction /\
    ym_verbatim_theorem_section
        .boundedBaseCyclicityInReconstructedSharpLocalHilbertSpace =
      .laneASharpLocalConstruction /\
    ym_verbatim_theorem_owner .finiteCapSharpLocalExtension =
      .laneASharpLocalConstruction /\
    ym_verbatim_theorem_owner .passageToFullSharpLocalInductiveUnion =
      .laneASharpLocalConstruction /\
    ym_verbatim_theorem_owner
        .boundedBaseCyclicityInReconstructedSharpLocalHilbertSpace =
      .laneASharpLocalConstruction

/--
Register-keyed Route 1 / QE3 claim family taken as the paper-facing Part D
boundary.
-/
def ym_route1_verbatim_claim_family : Prop :=
  ym_verbatim_theorem_section .continuumVacuumGapTransport = .qe3Transport /\
    ym_verbatim_theorem_section .continuumSharpLocalVacuumGap = .qe3Transport /\
    ym_verbatim_theorem_owner .continuumVacuumGapTransport =
      .ultravioletGateAndRoute1 /\
    ym_verbatim_theorem_owner .continuumSharpLocalVacuumGap =
      .ultravioletGateAndRoute1

/--
Register-keyed endpoint claim family taken as the paper-facing endpoint
boundary.
-/
def ym_endpoint_verbatim_claim_family : Prop :=
  ym_verbatim_theorem_section .wightmanHaagKastlerReconstruction =
      .endpointPacket /\
    ym_verbatim_theorem_section .fieldCorrespondence = .endpointPacket /\
    ym_verbatim_theorem_section .minkowskiHamiltonianInheritsGap =
      .endpointPacket /\
    ym_verbatim_theorem_section
        .exactLocalNetEndpointAndExclusionOfExtendedSupportSectorData =
      .endpointPacket /\
    ym_verbatim_theorem_section .groupOnlyRestatementOfEndpointTheorem =
      .endpointPacket /\
    ym_verbatim_theorem_owner .wightmanHaagKastlerReconstruction =
      .reconstructionAndUniversality /\
    ym_verbatim_theorem_owner .fieldCorrespondence =
      .reconstructionAndUniversality /\
    ym_verbatim_theorem_owner .minkowskiHamiltonianInheritsGap =
      .reconstructionAndUniversality /\
    ym_verbatim_theorem_owner
        .exactLocalNetEndpointAndExclusionOfExtendedSupportSectorData =
      .reconstructionAndUniversality /\
    ym_verbatim_theorem_owner .groupOnlyRestatementOfEndpointTheorem =
      .reconstructionAndUniversality

def ym_paper_partC_statement (RC : YMConstructiveRoute) : Prop :=
  ym_laneA_verbatim_claim_family /\ ym_laneA_explicit_statement RC

def ym_paper_partD_statement (RD : YMVacuumGapRoute) : Prop :=
  ym_route1_verbatim_claim_family /\ ym_route1_explicit_statement RD

def ym_paper_endpoint_statement (RE : YMEndpointCore) : Prop :=
  ym_endpoint_verbatim_claim_family /\ ym_endpoint_explicit_statement RE

theorem YangMillsLaneAVerbatimClaimFamilyStatement :
  ym_laneA_verbatim_claim_family := by
  exact And.intro rfl <| And.intro rfl <| And.intro rfl <| And.intro rfl <|
    And.intro rfl rfl

theorem YangMillsRoute1VerbatimClaimFamilyStatement :
  ym_route1_verbatim_claim_family := by
  exact And.intro rfl <| And.intro rfl <| And.intro rfl rfl

theorem YangMillsEndpointVerbatimClaimFamilyStatement :
  ym_endpoint_verbatim_claim_family := by
  exact And.intro rfl <| And.intro rfl <| And.intro rfl <| And.intro rfl <|
    And.intro rfl <| And.intro rfl <| And.intro rfl <| And.intro rfl <|
      And.intro rfl rfl

theorem YangMillsLaneAPaperClaimIffExplicitStatement
  (RC : YMConstructiveRoute) :
  ym_paper_partC_statement RC ↔ ym_laneA_explicit_statement RC := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact And.intro YangMillsLaneAVerbatimClaimFamilyStatement h

theorem YangMillsRoute1PaperClaimIffExplicitStatement
  (RD : YMVacuumGapRoute) :
  ym_paper_partD_statement RD ↔ ym_route1_explicit_statement RD := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact And.intro YangMillsRoute1VerbatimClaimFamilyStatement h

theorem YangMillsEndpointPaperClaimIffExplicitStatement
  (RE : YMEndpointCore) :
  ym_paper_endpoint_statement RE ↔ ym_endpoint_explicit_statement RE := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact And.intro YangMillsEndpointVerbatimClaimFamilyStatement h

end MaleyLean
