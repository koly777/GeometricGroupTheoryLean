/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import Mathlib.Topology.MetricSpace.IsometricSMul

import CoarseSpace.Group.Basic
import CoarseSpace.Metric.Basic
import CoarseSpace.Order
/-!
# Left-Invariant Metrics and Coarse Structures on Groups

This file establishes the relationship between two coarse structures on a group `G`:
1. The **leftMul coarse structure** from `CoarseSpace.Group.Basic`, where controlled sets
   are determined by finite subsets of `G`
2. The **metric coarse structure** from `CoarseSpace.Metric.Basic`, where controlled sets
   have uniformly bounded distances

## Main Results

* `leftMulCoarseSpace_le_metricCoarseSpace`: For any group with a left-invariant metric,
  the leftMul structure is coarser than the metric structure (leftMul-controlled implies
  metric-controlled).

* `metricCoarseSpace_le_leftMulCoarseSpace`: Under `[DiscreteTopology G] [ProperSpace G]`,
  the converse holds: metric-controlled implies leftMul-controlled.

* `leftMulCoarseSpace_eq_metricCoarseSpace`: Combining the above, the two coarse structures
  coincide for discrete proper groups with left-invariant metrics.

* `coarseEquiv_leftMul_metric`: The identity map is a coarse
  equivalence between the two structures.

## Implementation Notes

The key technical lemmas translate between the two notions of "controlled":
* `leftMulEntourage_subset_metricEntourage`: A leftMul entourage from a finite set `K` is
  contained in the metric entourage of radius `sup_{k ∈ K} d(1, k)`.
* `metricEntourage_subset_leftMulEntourage`: The metric entourage of radius `r` is contained
  in the leftMul entourage of the closed ball of radius `r` around `1`.

The assumptions `[DiscreteTopology G] [ProperSpace G]` ensure that closed balls are finite,
which is essential for the reverse direction.
-/

open Set Entourage NNReal

open scoped Entourage NNReal

namespace CoarseSpace

variable {G : Type*} [Group G] [PseudoMetricSpace G]

/-- The identity map from `G` with the metric structure to `G` with the `leftMul` structure
is coarsely proper. A finite set is always metric-bounded. -/
@[to_additive]
theorem coarselyProper_id_metric_to_leftMul :
    @CoarselyProper G G _ (instCoarseSpaceLeftMulRel G) id := by
  intro s hs
  have hfin := finite_of_isCoarselyBounded hs
  exact hfin.isBounded.isCoarselyBounded

/-! ### Left-invariance -/

variable [IsIsometricSMul G G]

/-- For a left-invariant metric, `dist x y = dist 1 (x⁻¹ * y)`. -/
@[to_additive]
private theorem dist_eq_dist_one_inv_mul (x y : G) : dist x y = dist 1 (x⁻¹ * y) := by
  have h := IsIsometricSMul.isometry_smul G x⁻¹
  rw [← Isometry.dist_eq h x y]
  simp only [smul_eq_mul, inv_mul_cancel]

/-- For a left-invariant metric, `nndist x y = nndist 1 (x⁻¹ * y)`. -/
@[to_additive]
private theorem nndist_eq_nndist_one_inv_mul (x y : G) : nndist x y = nndist 1 (x⁻¹ * y) := by
  rw [← NNReal.coe_inj, coe_nndist, coe_nndist, dist_eq_dist_one_inv_mul]

/-- For a left-invariant metric, `edist x y = edist 1 (x⁻¹ * y)`. -/
@[to_additive]
private theorem edist_eq_edist_one_inv_mul (x y : G) : edist x y = edist 1 (x⁻¹ * y) := by
  repeat rw [edist_nndist, nndist_eq_nndist_one_inv_mul]

/-- The `leftMulEntourage` of a finite set is contained in the metric entourage of the
supremum of distances from the identity. -/
@[to_additive]
theorem leftMulEntourage_subset_metricEntourage (K : Finset G) :
    leftMulEntourage (K : Set G) ⊆
      metricEntourage G (K.sup fun k => nndist 1 k) := by
  intro ⟨x, y⟩ hxy
  rw [mem_leftMulEntourage] at hxy
  rw [mem_metricEntourage, edist_eq_edist_one_inv_mul, edist_nndist]
  exact ENNReal.coe_le_coe.mpr (Finset.le_sup (f := fun k => nndist 1 k) hxy)

/-- The metric entourage of radius `r` is contained in the `leftMulEntourage` of the
closed ball of radius `r` around `1`. -/
@[to_additive]
theorem metricEntourage_subset_leftMulEntourage (r : ℝ≥0) :
    metricEntourage G r ⊆ leftMulEntourage (Metric.closedBall (1 : G) r) := by
  intro ⟨x, y⟩ hxy
  rw [mem_metricEntourage, edist_eq_edist_one_inv_mul, edist_nndist] at hxy
  rw [mem_leftMulEntourage, Metric.mem_closedBall, dist_comm, dist_nndist]
  exact_mod_cast ENNReal.coe_le_coe.mp hxy

/-- An entourage that is controlled in the `leftMul` coarse structure is also controlled
in the metric coarse structure. -/
@[to_additive]
theorem isControlled_metric_of_isControlled_leftMul {E : Entourage G}
    (hE : IsControlled[instCoarseSpaceLeftMulRel G] E) :
    IsControlled[instCoarseSpaceOfPseudoEMetricSpace G] E := by
  obtain ⟨K, hK⟩ := exists_finset_leftMulEntourage_of_isControlled hE
  exact (isControlled_metricEntourage G _).subset
    (hK.trans (leftMulEntourage_subset_metricEntourage K))

/-- The `leftMul` coarse structure is coarser than the metric coarse structure.
This holds unconditionally for any group with a left-invariant metric. -/
@[to_additive]
theorem leftMulCoarseSpace_le_metricCoarseSpace :
    instCoarseSpaceLeftMulRel (G := G) ≤ instCoarseSpaceOfPseudoEMetricSpace G :=
  fun _ hE => isControlled_metric_of_isControlled_leftMul hE

/-- The identity map from `G` with the `leftMul` coarse structure to `G` with the metric
coarse structure is controlled. -/
@[to_additive]
theorem controlled_id_leftMul_to_metric :
    @Controlled G G (instCoarseSpaceLeftMulRel G) (instCoarseSpaceOfPseudoEMetricSpace G) id :=
  (controlled_id_iff_le _ _).mpr leftMulCoarseSpace_le_metricCoarseSpace

/-! ### Discrete proper spaces -/

section DiscreteProper

variable [DiscreteTopology G] [ProperSpace G]

omit [IsIsometricSMul G G] in
/-- The identity map from `G` with the `leftMul` structure to `G` with the metric structure
is coarsely proper. A metric-bounded set is finite in the leftMul structure. -/
@[to_additive]
theorem coarselyProper_id_leftMul_to_metric :
    @CoarselyProper G G (instCoarseSpaceLeftMulRel G) _ id := by
  intro s hs
  have hbdd : Bornology.IsBounded s := hs.isBounded
  have hfin : s.Finite := by
    rw [Metric.isBounded_iff_subset_closedBall 1] at hbdd
    obtain ⟨r, hsr⟩ := hbdd
    have : (Metric.closedBall (1 : G) r).Finite :=
      (isCompact_closedBall 1 r).finite (DiscreteTopology.isDiscrete)
    exact Finite.subset this hsr
  exact hfin.coe_toFinset ▸ isCoarselyBounded_of_finset hfin.toFinset

/-- An entourage that is controlled in the metric coarse structure is also controlled
in the `leftMul` coarse structure, assuming finite metric balls. -/
@[to_additive]
theorem isControlled_leftMul_of_isControlled_metric {E : Entourage G}
    (hE : IsControlled[instCoarseSpaceOfPseudoEMetricSpace G] E) :
    IsControlled[instCoarseSpaceLeftMulRel G] E := by
  obtain ⟨r, hr⟩ := hE
  have hBfin : (Metric.closedBall (1 : G) r).Finite :=
    (isCompact_closedBall 1 r).finite (DiscreteTopology.isDiscrete)
  have hsub : E ⊆ leftMulEntourage (Metric.closedBall (1 : G) r) := by
    intro ⟨x, y⟩ hxy
    exact metricEntourage_subset_leftMulEntourage r (hr x y hxy)
  letI := instCoarseSpaceLeftMulRel G
  exact (isControlled_leftMulEntourage (G := G) hBfin.toFinset).subset
    (hsub.trans (leftMulEntourage_mono (Set.Finite.coe_toFinset hBfin).superset))

/-- The metric coarse structure is coarser than the `leftMul` coarse structure,
assuming finite metric balls. -/
@[to_additive]
theorem metricCoarseSpace_le_leftMulCoarseSpace :
    instCoarseSpaceOfPseudoEMetricSpace G ≤ instCoarseSpaceLeftMulRel (G := G) :=
  fun _ hE => isControlled_leftMul_of_isControlled_metric hE

/-- For a group with a left-invariant metric and finite metric balls,
the metric coarse structure equals the `leftMul` coarse structure. -/
@[to_additive]
theorem leftMulCoarseSpace_eq_metricCoarseSpace :
    instCoarseSpaceLeftMulRel (G := G) = instCoarseSpaceOfPseudoEMetricSpace G :=
  le_antisymm leftMulCoarseSpace_le_metricCoarseSpace metricCoarseSpace_le_leftMulCoarseSpace

/-- The identity map from `G` with the metric coarse structure to `G` with the `leftMul`
coarse structure is controlled, assuming finite metric balls. -/
@[to_additive]
theorem controlled_id_metric_to_leftMul :
    @Controlled G G (instCoarseSpaceOfPseudoEMetricSpace G) (instCoarseSpaceLeftMulRel G) id :=
  (controlled_id_iff_le _ _).mpr metricCoarseSpace_le_leftMulCoarseSpace

/-! ### Coarse maps and equivalences -/

@[to_additive, fun_prop]
theorem coarse_id_leftMul_to_metric :
    @Coarse G G (instCoarseSpaceLeftMulRel G) (instCoarseSpaceOfPseudoEMetricSpace G) id :=
  @Coarse.mk G G (instCoarseSpaceLeftMulRel G) (instCoarseSpaceOfPseudoEMetricSpace G) id
    controlled_id_leftMul_to_metric coarselyProper_id_leftMul_to_metric

@[to_additive, fun_prop]
theorem coarse_id_metric_to_leftMul :
    @Coarse G G (instCoarseSpaceOfPseudoEMetricSpace G) (instCoarseSpaceLeftMulRel G) id :=
  @Coarse.mk G G (instCoarseSpaceOfPseudoEMetricSpace G) (instCoarseSpaceLeftMulRel G) id
    controlled_id_metric_to_leftMul coarselyProper_id_metric_to_leftMul

variable (G : Type*) [Group G] [PseudoMetricSpace G]
variable [DiscreteTopology G] [ProperSpace G]
variable [IsIsometricSMul G G]

/-- The identity map is a coarse equivalence between `G` with the `leftMul` coarse structure
and `G` with the metric coarse structure. -/
@[to_additive]
def coarseEquiv_leftMul_metric :
    @CoarseEquiv G G (instCoarseSpaceLeftMulRel G) (instCoarseSpaceOfPseudoEMetricSpace G) :=
  @CoarseEquiv.mk G G (instCoarseSpaceLeftMulRel G) (instCoarseSpaceOfPseudoEMetricSpace G)
    id id coarse_id_leftMul_to_metric coarse_id_metric_to_leftMul
    (@isClose_of_eq G G (instCoarseSpaceOfPseudoEMetricSpace G) _ _ rfl)
    (@isClose_of_eq G G (instCoarseSpaceLeftMulRel G) _ _ rfl)

/-- The identity map is a coarse equivalence between `G` with the metric coarse structure
and `G` with the `leftMul` coarse structure. -/
@[to_additive]
def coarseEquiv_metric_leftMul :
    @CoarseEquiv G G (instCoarseSpaceOfPseudoEMetricSpace G) (instCoarseSpaceLeftMulRel G) :=
  @CoarseEquiv.mk G G (instCoarseSpaceOfPseudoEMetricSpace G) (instCoarseSpaceLeftMulRel G)
    id id coarse_id_metric_to_leftMul coarse_id_leftMul_to_metric
    (@isClose_of_eq G G (instCoarseSpaceLeftMulRel G) _ _ rfl)
    (@isClose_of_eq G G (instCoarseSpaceOfPseudoEMetricSpace G) _ _ rfl)

end DiscreteProper

end CoarseSpace
