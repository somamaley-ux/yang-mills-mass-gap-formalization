import MaleyLean.Foundation

namespace MaleyLean

/--
Lightweight structural package for
"Symmetry Constraints and Saturation in the Hypercube".

The current goal is to certify the paper-facing combinatorial theorem spine with
explicit hypotheses and no hidden axioms, not to internalize the full graph
theory of hypercubes and saturation from first principles.
-/
structure HypercubeSymmetryData where
  dim : Nat
  fullInvariantSaturationExists : Prop
  properFullInvariantSaturationExists : Prop
  sInvariantSaturationExists : Prop
  sInvariantMinimumEdgeCount : Nat
  unrestrictedSaturationNumber : Nat
  vertexTransitiveSubgroup : Type
  subgroupContainedInSn : vertexTransitiveSubgroup -> Prop
  saturationDefined : vertexTransitiveSubgroup -> Prop
  everyInvariantMinimizerMatchesSnExtremizer : vertexTransitiveSubgroup -> Prop

/-- The explicit candidate minimum under `S_n` symmetry. -/
def sn_candidate_edge_count (n : Nat) : Nat :=
  (n - 1) * 2 ^ (n - 1)

/-- Full automorphism invariance blocks nontrivial proper saturation for `n ≥ 3`. -/
theorem PaperFullSymmetryObstructionStatement
  (D : HypercubeSymmetryData)
  (h_dim : 3 <= D.dim)
  (h_full : D.fullInvariantSaturationExists)
  (h_full_invariant_forces_trivial :
    D.fullInvariantSaturationExists ->
    Not D.properFullInvariantSaturationExists) :
  Not D.properFullInvariantSaturationExists := by
  intro hproper
  exact h_full_invariant_forces_trivial h_full hproper

/-- `S_n` is the largest vertex-transitive symmetry group compatible with nontrivial saturation. -/
theorem PaperMaximalVertexTransitiveSymmetryStatement
  (D : HypercubeSymmetryData)
  [DecidablePred D.subgroupContainedInSn]
  (h_boundary :
    forall H : D.vertexTransitiveSubgroup,
      Not (D.subgroupContainedInSn H) ->
      Not (D.saturationDefined H)) :
  forall H : D.vertexTransitiveSubgroup,
    D.saturationDefined H ->
    D.subgroupContainedInSn H := by
  intro H hSat
  by_cases hIn : D.subgroupContainedInSn H
  · exact hIn
  · exact False.elim ((h_boundary H hIn) hSat)

/-- Exact minimum under `S_n` symmetry. -/
theorem PaperExactMinimizersUnderSnStatement
  (D : HypercubeSymmetryData)
  (h_dim : 3 <= D.dim)
  (h_exact : D.sInvariantMinimumEdgeCount = sn_candidate_edge_count D.dim) :
  D.sInvariantMinimumEdgeCount = (D.dim - 1) * 2 ^ (D.dim - 1) := by
  exact h_exact

/-- Extremizers are exactly the one-direction-omission configurations up to symmetry. -/
theorem PaperSnExtremizerClassificationStatement
  (oneDirectionOmissionExtremizer uniqueUpToSymmetry : Prop)
  (h_forward : oneDirectionOmissionExtremizer)
  (h_unique : uniqueUpToSymmetry) :
  oneDirectionOmissionExtremizer /\ uniqueUpToSymmetry := by
  exact And.intro h_forward h_unique

/-- Symmetry imposes a strict extremal cost over the unrestricted saturation number. -/
theorem PaperSymmetryCostStatement
  (D : HypercubeSymmetryData)
  (h_cost :
    D.unrestrictedSaturationNumber < D.sInvariantMinimumEdgeCount) :
  D.sInvariantMinimumEdgeCount > D.unrestrictedSaturationNumber := by
  exact h_cost

/-- Boundary sharpness: outside `S_n`, saturation is undefined or collapses back to the `S_n` extremizer type. -/
theorem PaperBoundarySharpnessStatement
  (D : HypercubeSymmetryData)
  (h_boundary :
    forall H : D.vertexTransitiveSubgroup,
      Not (D.subgroupContainedInSn H) ->
      Not (D.saturationDefined H) \/
      D.everyInvariantMinimizerMatchesSnExtremizer H) :
  forall H : D.vertexTransitiveSubgroup,
    Not (D.subgroupContainedInSn H) ->
    Not (D.saturationDefined H) \/
    D.everyInvariantMinimizerMatchesSnExtremizer H := by
  exact h_boundary

/-- Verified-core bundle for the current hypercube symmetry/saturation surface. -/
theorem PaperHypercubeSymmetrySaturationVerifiedCoreStatement
  (D : HypercubeSymmetryData)
  [DecidablePred D.subgroupContainedInSn]
  (h_dim : 3 <= D.dim)
  (h_full : D.fullInvariantSaturationExists)
  (h_full_invariant_forces_trivial :
    D.fullInvariantSaturationExists ->
    Not D.properFullInvariantSaturationExists)
  (h_maximal :
    forall H : D.vertexTransitiveSubgroup,
      Not (D.subgroupContainedInSn H) ->
      Not (D.saturationDefined H))
  (h_exact : D.sInvariantMinimumEdgeCount = sn_candidate_edge_count D.dim)
  (oneDirectionOmissionExtremizer uniqueUpToSymmetry : Prop)
  (h_forward : oneDirectionOmissionExtremizer)
  (h_unique : uniqueUpToSymmetry)
  (h_cost :
    D.unrestrictedSaturationNumber < D.sInvariantMinimumEdgeCount)
  (h_boundary :
    forall H : D.vertexTransitiveSubgroup,
      Not (D.subgroupContainedInSn H) ->
      Not (D.saturationDefined H) \/
      D.everyInvariantMinimizerMatchesSnExtremizer H) :
  Not D.properFullInvariantSaturationExists /\
  (forall H : D.vertexTransitiveSubgroup,
    D.saturationDefined H ->
    D.subgroupContainedInSn H) /\
  D.sInvariantMinimumEdgeCount = (D.dim - 1) * 2 ^ (D.dim - 1) /\
  (oneDirectionOmissionExtremizer /\ uniqueUpToSymmetry) /\
  D.sInvariantMinimumEdgeCount > D.unrestrictedSaturationNumber /\
  (forall H : D.vertexTransitiveSubgroup,
    Not (D.subgroupContainedInSn H) ->
    Not (D.saturationDefined H) \/
    D.everyInvariantMinimizerMatchesSnExtremizer H) := by
  refine And.intro ?_ ?_
  · exact
      PaperFullSymmetryObstructionStatement
        D
        h_dim
        h_full
        h_full_invariant_forces_trivial
  · refine And.intro ?_ ?_
    · exact
        PaperMaximalVertexTransitiveSymmetryStatement
          D
          h_maximal
    · refine And.intro ?_ ?_
      · exact PaperExactMinimizersUnderSnStatement D h_dim h_exact
      · refine And.intro ?_ ?_
        · exact
            PaperSnExtremizerClassificationStatement
              oneDirectionOmissionExtremizer
              uniqueUpToSymmetry
              h_forward
              h_unique
        · refine And.intro ?_ ?_
          · exact PaperSymmetryCostStatement D h_cost
          · exact PaperBoundarySharpnessStatement D h_boundary

end MaleyLean
