/-
Copyright (c) 2026 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import Mathlib.Topology.MetricSpace.Bounded

import CoarseSpace.Basic

/-!
# Metric Coarse Spaces

Every extended pseudo metric space carries a canonical coarse structure in which a relation `s` on
`α × α` is controlled if and only if the distances of its pairs are uniformly bounded:
`∃ r : ℝ≥0, ∀ p ∈ s, edist p.1 p.2 ≤ r`.

## Main Results

* `PseudoEMetricSpace → CoarseSpace`: the canonical coarse structure on a pseudo-extended-metric
  space, constructed via `CoarseSpace.ofControlled`.
* `Metric.isControlled_iff_bounded_edist`: characterisation of controlled sets via `edist`.
* `Metric.isControlled_iff_bounded_dist`: characterisation of controlled sets via `dist`.
* `isCoarselyBounded_iff_isBounded`: coarsely bounded sets coincide with `Bornology.IsBounded`
  sets in a pseudo-metric space.

## Implementation Notes

The instance is built using `CoarseSpace.ofControlled` with the family
`{ s | ∃ r : ℝ≥0, ∀ p ∈ s, edist p.1 p.2 ≤ r }` rather than going through the filter
directly. The bound is taken in `ℝ≥0` rather than `ℝ≥0∞` so that controlled sets exclude
pairs at infinite distance.

## Tags

coarse space, metric space, bounded, controlled set, bornology
-/

open Set Filter Metric
open scoped SetRel NNReal ENNReal

instance (α : Type*) [PseudoEMetricSpace α] : CoarseSpace α :=
  CoarseSpace.ofControlled
    { s | ∃ r : ℝ≥0, ∀ p ∈ s, edist p.1 p.2 ≤ r }
    (fun _ ⟨r, hr⟩ _ hs ↦ ⟨r, fun p hp ↦ hr p <| hs hp⟩)
    (fun _ ⟨r₁, h₁⟩ _ ⟨r₂, h₂⟩ ↦ ⟨max r₁ r₂, fun p hp ↦ hp.elim
      (fun h ↦ (h₁ p h).trans <| ENNReal.coe_le_coe.mpr <| le_max_left _ _)
      (fun h ↦ (h₂ p h).trans <| ENNReal.coe_le_coe.mpr <| le_max_right _ _)⟩)
    ⟨0, fun ⟨x, _⟩ h ↦ h ▸ (edist_self x).le⟩
    (fun _ ⟨r, hr⟩ ↦ ⟨r, fun ⟨x, y⟩ h ↦ edist_comm y x ▸ hr ⟨y, x⟩ h⟩)
    (fun _ ⟨r, hr⟩ ↦ ⟨r + r, fun ⟨x, z⟩ ⟨y, hxy, hyz⟩ ↦
      (edist_triangle x y z).trans (add_le_add (hr _ hxy) (hr _ hyz))⟩)

@[simp]
theorem Metric.isControlled_iff_bounded_edist {α : Type*} [PseudoEMetricSpace α] {s : SetRel α α} :
    IsControlled s ↔ ∃ r : ℝ≥0, ∀ p ∈ s, edist p.1 p.2 ≤ r :=
  isControlled_ofControlled_iff _

@[simp]
theorem Metric.isControlled_iff_bounded_dist {α : Type*} [PseudoMetricSpace α] {s : SetRel α α} :
    IsControlled s ↔ ∃ r : ℝ, ∀ p ∈ s, dist p.1 p.2 ≤ r :=
  isControlled_iff_bounded_edist.trans
    ⟨fun ⟨r, hr⟩ ↦ ⟨r, fun p hp ↦
      dist_edist (α := α) .. ▸ ENNReal.toReal_le_coe_of_le_coe <| hr p hp⟩,
     fun ⟨r, hr⟩ ↦ ⟨r.toNNReal, fun p hp ↦
      edist_dist (α := α) .. ▸ ENNReal.ofReal_le_ofReal (hr p hp)⟩⟩

section PseudoMetricSpace

variable {α : Type*} [PseudoMetricSpace α]

/-- A coarsely bounded set in a pseudo-metric space is metrically bounded. -/
theorem IsCoarselyBounded.isBounded {s : Set α} (hs : IsCoarselyBounded s) :
    Bornology.IsBounded s :=
    match s.eq_empty_or_nonempty with
    | .inl h =>  (h ▸ Bornology.isBounded_empty)
    | .inr ⟨x₀, hx₀⟩ =>
      let ⟨r, hr⟩ := isControlled_iff_bounded_edist.mp hs
      have (x : α) (hx : x ∈ s) : x ∈ closedBall x₀ ↑r :=
        mem_closedBall.mpr <| dist_comm x x₀ ▸ dist_edist x₀ x ▸
        ENNReal.toReal_le_coe_of_le_coe <| hr ⟨x₀, x⟩ ⟨hx₀, hx⟩
      (isBounded_iff_subset_closedBall x₀).mpr ⟨r, fun x hx ↦ this x hx⟩

/-- A metrically bounded set in a pseudo-metric space is coarsely bounded. -/
theorem Bornology.IsBounded.isCoarselyBounded {s : Set α} (hs : Bornology.IsBounded s) :
    IsCoarselyBounded s :=
  let ⟨C, hC⟩ := isBounded_iff.mp hs
  isControlled_iff_bounded_edist.mpr
    ⟨C.toNNReal, fun _ ⟨hx, hy⟩ ↦ mod_cast (hC hx hy).trans (le_max_left C 0)⟩

@[simp]
theorem isCoarselyBounded_iff_isBounded {s : Set α} :
    IsCoarselyBounded s ↔ Bornology.IsBounded s :=
  ⟨IsCoarselyBounded.isBounded, Bornology.IsBounded.isCoarselyBounded⟩

end PseudoMetricSpace
