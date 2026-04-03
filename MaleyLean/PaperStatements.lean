import MaleyLean.InvariantBundle
import MaleyLean.TargetToRedescription
import MaleyLean.TheoremRegister
import MaleyLean.EnvelopeInvariants

namespace MaleyLean

theorem PaperBivalenceInterfaceStatement
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_red_collapse :
    ∀ u v : β,
      same_side_split GoodD u v →
      ¬ redescription_dependent_split rel StatusD u v)
  (h_eff_collapse :
    ∀ u v : β,
      same_side_split GoodD u v →
      ¬ effective_split StatusD GoodD scope_preserving u v) :
  binary_admissibility_interface rel StatusD GoodD scope_preserving := by
  exact
    BivalenceInterfaceTheorem
      rel StatusD GoodD scope_preserving h_red_collapse h_eff_collapse

theorem PaperSameSideSplitCollapseSummaryStatement
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_bin : binary_admissibility_interface rel StatusD GoodD scope_preserving)
  (u v : β)
  (hs : same_side_split GoodD u v) :
  ¬ redescription_dependent_split rel StatusD u v ∧
  ¬ effective_split StatusD GoodD scope_preserving u v := by
  exact
    SameSideSplitCollapseSummaryTheorem
      rel StatusD GoodD scope_preserving h_bin u v hs

theorem PaperStandingEmergenceStatement
  {α : Type}
  (B : InvariantBundle α)
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  [DecidablePred (fun a : α => standing S a)]
  (h_env_preserves :
    envelope_preserves_invariants B RefStatus scope_preserving)
  (h_rel_interface :
    same_target_rel_interface B rel)
  (h_adm :
    ∀ (a : α), standing S a → Admitted a)
  (h_pres :
    ∀ (a : α),
      standing S a →
      ∀ (f : Redescription α α),
        licensed_same_scope_continuation f →
        preserves_relevant_invariants a f)
  (h_internal :
    internally_fixed_auxiliary_datum rel RefStatus)
  (h_status_admitted_only :
    ∀ (a : α),
      admitted_only S Admitted a →
      RefStatus a = StandingRefinementLabel.admittedOnly)
  (h_status_standing :
    ∀ (a : α),
      standing S a →
      RefStatus a = StandingRefinementLabel.standingBearing)
  (h_substantive_if_admitted_only :
    ∀ (a : α),
      admitted_only S Admitted a →
      substantive_positive_refinement S Admitted RefStatus scope_preserving) :
  ∀ (a : α),
    standing S a ↔
      reuse_stably_admissible
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a :=
by
  intro a
  constructor
  · intro ha
    exact
      standing_implies_reuse_stably_admissible
        S
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        h_adm
        h_pres
        a
        ha
  · intro ha
    by_cases hs : standing S a
    · exact hs
    · have hao : admitted_only S Admitted a := ⟨ha.left, hs⟩
      have h_sub :
          substantive_positive_refinement
            S
            Admitted
            RefStatus
            scope_preserving :=
        h_substantive_if_admitted_only a hao
      have h_bridge :
          substantive_positive_redescription_refinement_bridge
            S
            rel
            Admitted
            RefStatus
            scope_preserving :=
        substantive_positive_redescription_refinement_bridge_of_witness
          B
          S
          rel
          Admitted
          RefStatus
          scope_preserving
          h_env_preserves
          h_rel_interface
          h_status_admitted_only
          h_status_standing
      have h_ext : external_auxiliary_datum rel RefStatus :=
        same_side_redescription_effective_refinement_implies_external_auxiliary_datum
          rel
          RefStatus
          scope_preserving
          StandingRefinementLabel.admittedOnly
          StandingRefinementLabel.standingBearing
          admitted_only_ne_standing_bearing
          (h_bridge h_sub)
      exact False.elim (h_ext h_internal)

theorem PaperNoSameActRepairStatement
  {α : Type}
  (S : System α)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (T : Redescription α α)
  (a : α)
  (h_fail : ¬ standing S a)
  (h_repair :
    standing S (T a) →
    a = T a) :
  ¬ standing S (T a) := by
  exact
    NoSameActRepairTheorem
      S
      licensed_same_scope_continuation
      preserves_relevant_invariants
      T
      a
      h_fail
      h_repair

theorem PaperNoGeneratorsStatement
  {α : Type}
  (S : System α)
  (T : Redescription α α)
  (a : α) :
  ¬ standing S a → standing S (T a) → T a = a → False :=
by
  intro h_fail h_gen hEq
  have hA : standing S a := by
    simpa [hEq] using h_gen
  exact h_fail hA

theorem PaperNoPrimitiveCarriersStandingFormStatement
  {α : Type}
  (S : System α)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (QD : α → Prop)
  (h_emergence :
    ∀ a : α,
      standing S a ↔
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a)
  (h_gatework :
    ∀ a : α,
      QD a →
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a)
  (h_ext :
    ∀ a : α,
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      QD a) :
  ∀ a : α,
    QD a ↔ standing S a := by
  exact
    NoPrimitiveCarriersStandingFormTheorem
      S
      licensed_same_scope_continuation
      preserves_relevant_invariants
      QD
      h_emergence
      h_gatework
      h_ext

theorem PaperUniquenessOfAdmissibleInteriorStatement
  {α : Type}
  (S : System α)
  (I₁ I₂ : α → Prop)
  (h₁ : ∀ a, I₁ a → standing S a)
  (h₂ : ∀ a, I₂ a → standing S a)
  (h_complete₁ : ∀ a, standing S a → I₁ a)
  (h_complete₂ : ∀ a, standing S a → I₂ a) :
  lawfully_equivalent_interiors I₁ I₂ := by
  exact
    UniquenessOfAdmissibleInteriorTheorem
      S I₁ I₂ h₁ h₂ h_complete₁ h_complete₂

theorem PaperStandingConservationStatement
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (h_ext :
    ∀ a : α,
      reuse_stably_admissible
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      standing S a) :
  ∀ a : α,
    ¬ standing S a →
    ¬ reuse_stably_admissible
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      a := by
  exact
    StandingConservationTheorem
      S
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      h_ext

end MaleyLean
