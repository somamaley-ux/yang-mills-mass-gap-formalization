import MaleyLean.Papers.NavierStokes.Continuation.Boundary

namespace MaleyLean

/--
Horizon-collapse packet for the primitive Navier--Stokes route.

This layer distinguishes mere horizon-visible singular images from genuine
continuation obstructions. The structural point is that obstruction must be
typed at the same scope and must respect the already-fixed quotient boundary;
otherwise it is only bookkeeping-visible and cannot close continuation.
-/
structure HorizonCollapseSystem
    (State Time History Witness Candidate Quantity Label : Type) where
  boundary : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label
  horizonVisible : Candidate → Prop
  continuationObstructing : Candidate → Prop
  bookkeepingVisible : Candidate → Prop

def horizon_singular_image
  {State Time History Witness Candidate Quantity Label : Type}
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label) :
  Prop :=
  ∃ h : History, ∃ c : Candidate,
    Z.boundary.singularExtractor h = some c ∧
    Z.horizonVisible c

def genuine_continuation_obstruction
  {State Time History Witness Candidate Quantity Label : Type}
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label) :
  Prop :=
  ∃ h : History, ∃ c : Candidate,
    Z.boundary.singularExtractor h = some c ∧
    Z.horizonVisible c ∧
    Z.boundary.extractorSameScope c ∧
    Z.continuationObstructing c

def bookkeeping_only_horizon_image
  {State Time History Witness Candidate Quantity Label : Type}
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label) :
  Prop :=
  ∃ h : History, ∃ c : Candidate,
    Z.boundary.singularExtractor h = some c ∧
    Z.horizonVisible c ∧
    Z.bookkeepingVisible c ∧
    ¬ Z.continuationObstructing c

def horizon_collapse_boundary
  {State Time History Witness Candidate Quantity Label : Type}
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label) :
  Prop :=
  ∀ h : History, ∀ c : Candidate,
    Z.boundary.singularExtractor h = some c →
    Z.horizonVisible c →
    Z.bookkeepingVisible c ∨
    (Z.boundary.extractorSameScope c ∧ Z.continuationObstructing c)

def bookkeeping_visibility_blocks_obstruction
  {State Time History Witness Candidate Quantity Label : Type}
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label) :
  Prop :=
  ∀ c : Candidate, Z.bookkeepingVisible c → ¬ Z.continuationObstructing c

theorem PaperHorizonSingularImageStatement
  {State Time History Witness Candidate Quantity Label : Type}
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label)
  (h :
    ∃ h0 : History, ∃ c : Candidate,
      Z.boundary.singularExtractor h0 = some c ∧
      Z.horizonVisible c) :
  horizon_singular_image Z := by
  exact h

theorem PaperGenuineContinuationObstructionStatement
  {State Time History Witness Candidate Quantity Label : Type}
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label)
  (h :
    ∃ h0 : History, ∃ c : Candidate,
      Z.boundary.singularExtractor h0 = some c ∧
      Z.horizonVisible c ∧
      Z.boundary.extractorSameScope c ∧
      Z.continuationObstructing c) :
  genuine_continuation_obstruction Z := by
  exact h

theorem PaperHorizonCollapseBoundaryStatement
  {State Time History Witness Candidate Quantity Label : Type}
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label)
  (h :
    ∀ h0 : History, ∀ c : Candidate,
      Z.boundary.singularExtractor h0 = some c →
      Z.horizonVisible c →
      Z.bookkeepingVisible c ∨
      (Z.boundary.extractorSameScope c ∧ Z.continuationObstructing c)) :
  horizon_collapse_boundary Z := by
  exact h

theorem PaperBookkeepingVisibilityBlocksObstructionStatement
  {State Time History Witness Candidate Quantity Label : Type}
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label)
  (h : ∀ c : Candidate, Z.bookkeepingVisible c → ¬ Z.continuationObstructing c) :
  bookkeeping_visibility_blocks_obstruction Z := by
  exact h

theorem PaperBookkeepingOnlyHorizonImageNotObstructionStatement
  {State Time History Witness Candidate Quantity Label : Type}
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label)
  (hblock : bookkeeping_visibility_blocks_obstruction Z)
  (h :
    ∃ h0 : History, ∃ c : Candidate,
      Z.boundary.singularExtractor h0 = some c ∧
      Z.horizonVisible c ∧
      Z.bookkeepingVisible c) :
  bookkeeping_only_horizon_image Z := by
  rcases h with ⟨h0, c, hextract, hhorizon, hbook⟩
  exact ⟨h0, c, hextract, hhorizon, hbook, hblock c hbook⟩

theorem PaperHorizonVisibleVsGenuineObstructionStatement
  {State Time History Witness Candidate Quantity Label : Type}
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label)
  (hboundary : horizon_collapse_boundary Z)
  (hblock : bookkeeping_visibility_blocks_obstruction Z)
  (h :
    ∃ h0 : History, ∃ c : Candidate,
      Z.boundary.singularExtractor h0 = some c ∧
      Z.horizonVisible c) :
  bookkeeping_only_horizon_image Z ∨ genuine_continuation_obstruction Z := by
  rcases h with ⟨h0, c, hextract, hhorizon⟩
  rcases hboundary h0 c hextract hhorizon with hbook | hobs
  · left
    exact ⟨h0, c, hextract, hhorizon, hbook, hblock c hbook⟩
  · right
    rcases hobs with ⟨hscope, hobstruct⟩
    exact ⟨h0, c, hextract, hhorizon, hscope, hobstruct⟩

theorem PaperPrimitiveBoundaryToHorizonCollapseStatement
  {State Time Datum LocalSol History Witness Candidate Quantity Label : Type}
  (S : PrimitiveNavierStokesSystem State Time Witness Candidate Quantity)
  (L : PeriodicLocalTheory State Time Datum LocalSol Witness)
  (B : ContinuationBoundarySystem State Time History Witness Candidate Quantity Label)
  (Z : HorizonCollapseSystem State Time History Witness Candidate Quantity Label)
  (_h_packet :
    datum_entry_to_admitted_carrier S L ∧
    local_realization_on_carrier S L ∧
    restart_consistency_same_object_persistence S L ∧
    pre_horizon_slice_reentry S L ∧
    finite_horizon_witness_visibility S L)
  (_h_closed : continuation_boundary_closed B)
  (hboundary : horizon_collapse_boundary Z)
  (hblock : bookkeeping_visibility_blocks_obstruction Z)
  (h :
    ∃ h0 : History, ∃ c : Candidate,
      Z.boundary.singularExtractor h0 = some c ∧
      Z.horizonVisible c) :
  bookkeeping_only_horizon_image Z ∨ genuine_continuation_obstruction Z := by
  exact PaperHorizonVisibleVsGenuineObstructionStatement Z hboundary hblock h

end MaleyLean
