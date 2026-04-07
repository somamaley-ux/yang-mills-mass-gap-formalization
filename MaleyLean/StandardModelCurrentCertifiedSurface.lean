import MaleyLean.StandardModelL1SupportBundle
import MaleyLean.StandardModelUmbrellaVerifiedCore

namespace MaleyLean

/--
Top-level certified surface currently available for the Standard Model
manuscript in this repo.

This combines the integrated L1 support stack with the integrated umbrella
verified core.
-/
structure StandardModelCurrentCertifiedSurface
    {alpha beta : Type}
    {CY WY : Type}
    {CE WE : Type}
    {CN MN RN : Type}
    {CL WL : Type}
    {CA WA : Type}
    {CU WU : Type}
    {CR WR : Type}
    {CF WF : Type}
    {CH WH : Type}
    {UVCC LowCC ExtCC WCC VCC : Type}
    {GQ UVQ WQ : Type}
    {GCC : Type}
    {EX : Type}
    [Mul GCC] [Div GCC] [OfNat GCC 2] [OfNat GCC 4] [OfNat GCC 8] [One GCC]
    (A : RedescriptionAction alpha)
    (B : InvariantBundle alpha)
    (S : System alpha)
    (rel : alpha -> alpha -> Prop)
    (Admitted : alpha -> Prop)
    (licensed_same_scope_continuation : Redescription alpha alpha -> Prop)
    (preserves_relevant_invariants : alpha -> Redescription alpha alpha -> Prop)
    (QD I1 I2 : alpha -> Prop)
    (S2 : System beta)
    (f : Redescription alpha beta)
    (g : Redescription beta beta)
    (DY : YukawaMassWitnessData CY WY)
    (DE : EMCouplingWitnessData CE WE)
    (DN : NeutrinoWitnessPairData CN MN RN)
    (DL : LongitudinalGoldstoneWitnessData CL WL)
    (DA : AnomalyYukawaWitnessData CA WA)
    (DU : UnitaryMixingWitnessData CU WU)
    (DR : RephasingWitnessData CR WR)
    (DF : FCNCWitnessData CF WF)
    (DH : HyperchargeWitnessData CH WH)
    (DCC : ChargedCurrentTransportData UVCC LowCC ExtCC WCC VCC)
    (opsQ : CPoddPhaseOpsClean GQ)
    (DQCD : QCDCPoddDataClean UVQ WQ)
    (DX : EquivalenceExhaustionData EX) where
  l1_support :
    StandardModelL1SupportBundle
      DY DE DN DL DA DU DR DF DH DCC opsQ DQCD DX
  umbrella_core :
    StandardModelUmbrellaVerifiedCoreBundle
      A B S rel Admitted licensed_same_scope_continuation preserves_relevant_invariants
      QD I1 I2 S2 f g DY DE DN DL DA DU DR DF DH DCC opsQ DQCD DX

/--
Top-level paper-facing theorem for the currently certified Standard Model
surface in this repo.

This is intentionally a theorem of existence of the certified surface, not a
claim that the full field-level manuscript is already encoded.
-/
theorem PaperStandardModelCurrentCertifiedSurfaceStatement
    {alpha beta : Type}
    {CY WY : Type}
    {CE WE : Type}
    {CN MN RN : Type}
    {CL WL : Type}
    {CA WA : Type}
    {CU WU : Type}
    {CR WR : Type}
    {CF WF : Type}
    {CH WH : Type}
    {UVCC LowCC ExtCC WCC VCC : Type}
    {GQ UVQ WQ : Type}
    {GCC : Type}
    {EX : Type}
    [Mul GCC] [Div GCC] [OfNat GCC 2] [OfNat GCC 4] [OfNat GCC 8] [One GCC]
    (A : RedescriptionAction alpha)
    (B : InvariantBundle alpha)
    (S : System alpha)
    (rel : alpha -> alpha -> Prop)
    (Admitted : alpha -> Prop)
    (licensed_same_scope_continuation : Redescription alpha alpha -> Prop)
    (preserves_relevant_invariants : alpha -> Redescription alpha alpha -> Prop)
    (QD I1 I2 : alpha -> Prop)
    (S2 : System beta)
    (f : Redescription alpha beta)
    (g : Redescription beta beta)
    (DY : YukawaMassWitnessData CY WY)
    (DE : EMCouplingWitnessData CE WE)
    (DN : NeutrinoWitnessPairData CN MN RN)
    (DL : LongitudinalGoldstoneWitnessData CL WL)
    (DA : AnomalyYukawaWitnessData CA WA)
    (DU : UnitaryMixingWitnessData CU WU)
    (DR : RephasingWitnessData CR WR)
    (DF : FCNCWitnessData CF WF)
    (DH : HyperchargeWitnessData CH WH)
    (DCC : ChargedCurrentTransportData UVCC LowCC ExtCC WCC VCC)
    (opsQ : CPoddPhaseOpsClean GQ)
    (DQCD : QCDCPoddDataClean UVQ WQ)
    (DX : EquivalenceExhaustionData EX)
    (h_orbit : orbit_agrees_with_invariants A B)
    (h_transport : action_transport_closure A rel)
    (h_ext :
      forall a : alpha,
        reuse_stably_admissible
          Admitted
          licensed_same_scope_continuation
          preserves_relevant_invariants
          a ->
        standing S a)
    (h_toStanding : forall a : alpha, QD a -> standing S a)
    (h_fromStanding : forall a : alpha, standing S a -> QD a)
    (hI1 : forall a, I1 a -> standing S a)
    (hI2 : forall a, I2 a -> standing S a)
    (h_complete_I1 : forall a, standing S a -> I1 a)
    (h_complete_I2 : forall a, standing S a -> I2 a)
    (hirr : irrecoverable_failure S S2 f)
    (hsp : standing_preserving_redescription S2 S2 g)
    (hY_mass : forall c : CY, DY.massWitness c = DY.witness c)
    (hY_yukawa : forall c : CY, DY.yukawaWitness c = DY.witness c)
    (hE_ew : forall c : CE, DE.ewWitness c = DE.witness c)
    (hE_em : forall c : CE, DE.emWitness c = DE.witness c)
    (hN_mass : forall c : CN, DN.sourceMass c = DN.witnessMass c)
    (hN_mix : forall c : CN, DN.sourceMix c = DN.witnessMix c)
    (hL_long : forall c : CL, DL.longitudinalWitness c = DL.witness c)
    (hL_gold : forall c : CL, DL.goldstoneWitness c = DL.witness c)
    (hA_anom : forall c : CA, DA.anomalyWitness c = DA.witness c)
    (hA_yuk : forall c : CA, DA.yukawaWitness c = DA.witness c)
    (hU_op : forall c : CU, DU.operatorWitness c = DU.witness c)
    (hU_res : forall c : CU, DU.residualWitness c = DU.witness c)
    (hR_op : forall c : CR, DR.operatorWitness c = DR.witness c)
    (hR_res : forall c : CR, DR.residualWitness c = DR.witness c)
    (hF_align : forall c : CF, DF.alignmentWitness c = DF.witness c)
    (hF_fcnc : forall c : CF, DF.fcncWitness c = DF.witness c)
    (hH_shared :
      forall c : CH,
        DH.normalizedByWitness (DH.witness c) <->
          DH.chargeQuantizedByWitness (DH.witness c)) :
    Nonempty
      (StandardModelCurrentCertifiedSurface
        A B S rel Admitted licensed_same_scope_continuation preserves_relevant_invariants
        QD I1 I2 S2 f g DY DE DN DL DA DU DR DF DH DCC opsQ DQCD DX) := by
  refine ⟨{
    l1_support := by
      exact
        PaperStandardModelL1SupportBundleStatement
          DY DE DN DL DA DU DR DF DH DCC opsQ DQCD DX
          hY_mass hY_yukawa hE_ew hE_em hN_mass hN_mix hL_long hL_gold
          hA_anom hA_yuk hU_op hU_res hR_op hR_res hF_align hF_fcnc hH_shared
    umbrella_core := by
      exact
        PaperStandardModelUmbrellaVerifiedCoreStatement
          A B S rel Admitted licensed_same_scope_continuation preserves_relevant_invariants
          QD I1 I2 S2 f g
          DY DE DN DL DA DU DR DF DH DCC opsQ DQCD DX
          h_orbit h_transport h_ext h_toStanding h_fromStanding
          hI1 hI2 h_complete_I1 h_complete_I2 hirr hsp
          hY_mass hY_yukawa hE_ew hE_em hN_mass hN_mix hL_long hL_gold
          hA_anom hA_yuk hU_op hU_res hR_op hR_res hF_align hF_fcnc hH_shared
  }⟩

end MaleyLean
