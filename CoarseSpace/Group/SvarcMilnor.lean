/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.IsometricSMul

import CoarseSpace.CoarseEquiv.Lemmas
import CoarseSpace.CoarseSMul
import CoarseSpace.Group.LeftInvariant
import CoarseSpace.Metric.TransferQI

/-!
# Švarc-Milnor Lemma

This file proves the Švarc-Milnor lemma.

## Main Results

* `smul_closedBall_eq_univ`: Under a cocompact action, some closed ball has orbit covering `X`.
* `CoarseSpace.instUniformlyControlledSMul`: Isometric actions are uniformly controlled.
* `CoarseSpace.instIsCoarseSMul`: Properly discontinuous isometric actions on proper spaces
  are coarse actions.
* `CoarseSpace.instCocompactSMul`: Compact quotient implies cocompact action.
* `mulOrbitQuasiIsometryEquiv`: **Švarc-Milnor** — the orbit map `g ↦ g • x₀` is a
  quasi-isometry equivalence `G ≃qi X`.
* `mulOrbit_quasiIsometry`: The orbit map is a quasi-isometry.

## Implementation notes

The classical statement of Švarc-Milnor assumes the group is equipped with a word metric from
a finite generating set. We deliberately avoid this, instead requiring typeclass assumptions
that any word metric would satisfy:

* `[DiscreteTopology G]`: the metric is discrete
* `[ProperSpace G]`: closed balls are compact (finite for discrete spaces)
* `[IsIsometricSMul G G]`: the metric is left-invariant

This approach has several advantages, particularly:

1. **No explicit word metric construction**: Many groups come with natural metrics
   that happen to be quasi-isometric to word metrics. We don't force everything through
   one construction.

2. **Generator independence**: Different generating sets give different word metrics, but all
   satisfy the same typeclasses. The quasi-isometry class is independent of this choice by
   construction, not by a separate theorem.

The proof factors through the coarse Švarc-Milnor lemma (`mulOrbitCoarseEquiv`), which
establishes `G ≃ᶜ X` using only coarse-geometric hypotheses. The upgrade to a quasi-isometry
equivalence requires `HasCoarseMidpoints`, a purely metric condition that lets us avoid working
with geodesics or length space assumptions.

To derive that `G` is finitely generated, one can use the coarse Švarc-Milnor lemma
(`CoarseSpace.mulOrbitCoarseEquiv`) which requires only:

* `G` is a group acting on `X`
* `X` is a proper metric space with coarse midpoints
* The action is by isometries, properly discontinuous, and cocompact

Under these hypotheses, `G ≃ᶜ X`. Since `HasCoarseMidpoints X` implies `X` is
finitely generated as a coarse space, and finite generation transfers across
the coarse equivalence to `G`: first as a coarse space, then as a group.

The file uses `to_additive` throughout to generate additive versions automatically.

## References

* J. Roe, "Lectures on Coarse Geometry"

## Tags

coarse geometry, group action, Švarc-Milnor lemma, quasi-isometry
-/

open Metric
open scoped Pointwise

variable {G : Type*} [Group G] {X : Type*}
variable [PseudoMetricSpace X] [MulAction G X] [IsIsometricSMul G X]
variable [CompactSpace (MulAction.orbitRel.Quotient G X)]

/-- If a group `G` acts on a pseudo metric space `X` such that the quotient space
`MulAction.orbitRel.Quotient G X` is compact, then the distance from a point to
`MulAction.orbit G x₀` is bounded above, where `x₀` is a given basepoint. -/
@[to_additive]
theorem bddAbove_range_infDist_mulAction_orbit (x₀ : X) :
    BddAbove <| Set.range <| fun x ↦ Metric.infDist x (MulAction.orbit G x₀) :=
  -- infDist to the orbit is constant on orbits, so descends to quotient
  have orbit_eq : ∀ a b : X, MulAction.orbitRel G X a b →
      infDist a (MulAction.orbit G x₀) = infDist b (MulAction.orbit G x₀) :=
    fun a b ⟨g, hg⟩ ↦
      calc infDist a (MulAction.orbit G x₀)
          = infDist (g • b) (MulAction.orbit G x₀) := congrArg (infDist · _) hg.symm
        _ = infDist (g • b) (g • MulAction.orbit G x₀) :=
              congrArg _ (MulAction.smul_orbit g x₀).symm
        _ = infDist b (MulAction.orbit G x₀) :=
              Set.image_smul (α := G) (β := X) (a := g) ▸ infDist_image (isometry_smul X g)
  -- Define the descended function on the quotient
  let dist' : MulAction.orbitRel.Quotient G X → ℝ :=
    Quotient.lift (fun x ↦ infDist x (MulAction.orbit G x₀)) orbit_eq
  -- dist' is continuous
  have hdist'_cont : Continuous dist' :=
    Continuous.quotient_lift (continuous_infDist_pt _) orbit_eq
  -- By compactness, dist' attains a maximum
  let ⟨q, ⟨_, (hq : IsMaxOn dist' Set.univ q)⟩⟩ := CompactSpace.isCompact_univ.exists_isMaxOn
    (Set.nonempty_iff_univ_nonempty.mp <|
      (nonempty_quotient_iff (MulAction.orbitRel G X)).mpr ⟨x₀⟩)
    hdist'_cont.continuousOn
  -- The maximum value bounds the range
  ⟨dist' q, fun _ ⟨y, hy⟩ ↦ hy ▸ hq (Set.mem_univ (Quotient.mk _ y))⟩

/-- For any point `x` in a pseudo metric space with a cocompact group action, there exists a
group element `g` such that the distance from `x` to `g • x₀` is strictly less than one plus
the supremum of distances to the orbit. -/
@[to_additive
/-- For any point `x` in a pseudo metric space with a cocompact additive group action, there
exists a group element `g` such that the distance from `x` to `g +ᵥ x₀` is strictly less than
one plus the supremum of distances to the orbit. -/]
lemma dist_smul_lt_one_add_sSup_range_infDist_orbit (x x₀ : X) :
    ∃ g : G, dist x (g • x₀) <
      1 + sSup (Set.range fun x ↦ infDist x (MulAction.orbit G x₀)) :=
  let R := sSup (Set.range fun x ↦ infDist x (MulAction.orbit G x₀))
  -- infDist x (orbit) ≤ R since x is in the range
  have hR : infDist x (MulAction.orbit G x₀) ≤ R :=
    le_csSup (bddAbove_range_infDist_mulAction_orbit x₀) ⟨x, rfl⟩
  -- So infDist x (orbit) < 1 + R
  have hlt : infDist x (MulAction.orbit G x₀) < 1 + R :=
    lt_add_of_pos_of_le one_pos hR
  -- By definition of infDist, there exists y in orbit with dist x y < 1 + R
  let ⟨_, hy_mem, hy_dist⟩ :=
    (infDist_lt_iff ⟨x₀, MulAction.mem_orbit_self x₀⟩).mp hlt
  -- Since y ∈ orbit, we have y = g • x₀ for some g
  let ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy_mem
  ⟨g, hg ▸ hy_dist⟩

/-- Under a cocompact group action, there exists a radius `R` such that the orbit of the closed
ball `closedBall x₀ R` under the full group covers the entire space. -/
@[to_additive
/-- Under a cocompact additive group action, there exists a radius `R` such that the orbit of the
closed ball `closedBall x₀ R` under the full group covers the entire space. -/]
theorem smul_closedBall_eq_univ (x₀ : X) :
    ∃ R : ℝ, (Set.univ : Set G) • closedBall x₀ R = Set.univ :=
  ⟨1 + sSup (Set.range fun x ↦ infDist x (MulAction.orbit G x₀)),
    Set.eq_univ_iff_forall.mpr fun x ↦
      let ⟨g, hg⟩ := dist_smul_lt_one_add_sSup_range_infDist_orbit (G := G) x x₀
      Set.mem_smul.mpr ⟨g, Set.mem_univ g, g⁻¹ • x,
        mem_closedBall.mpr (((isometry_smul X g).dist_eq ..).symm ▸
        (smul_inv_smul g x).symm ▸ le_of_lt hg), smul_inv_smul g x⟩⟩

namespace CoarseSpace

/-- Isometric group actions are uniformly controlled in the coarse structure. -/
@[to_additive
/-- Isometric additive group actions are uniformly controlled in the coarse structure. -/]
instance : UniformlyControlledSMul G X where
  uniformly_controlled hE :=
    let ⟨r, hr⟩ := hE
    ⟨metricEntourage X r, isControlled_metricEntourage X r,
     fun g _ ⟨⟨x, y⟩, hxy, heq⟩ ↦
       heq ▸ ((isometry_smul X g).edist_eq x y).trans_le (hr x y hxy)⟩

variable [ProperSpace X] [ProperlyDiscontinuousSMul G X]

/-- When a group acts properly discontinuously by isometries on a proper pseudo metric space,
the action is a coarse action. -/
@[to_additive]
instance : IsCoarseSMul G X where
  coarse_smul x :=
    ⟨fun {E} hE ↦
      let ⟨K, hK⟩ := exists_finset_leftMulEntourage_of_isControlled hE
      match K.eq_empty_or_nonempty with
      | .inl hK_empty =>
          have hE_empty : E = ∅ :=
            Set.subset_empty_iff.mp (leftMulEntourage_empty (G := G) ▸
              Finset.coe_empty (α := G) ▸ (hK_empty ▸ hK))
          hE_empty ▸ (Entourage.map_empty _).symm ▸ isControlled_empty
      | .inr hKne =>
          ⟨K.sup' hKne (fun k ↦ nndist x (k • x)), fun _ _ ⟨⟨g, h⟩, hgh, heq⟩ ↦
            let ⟨ha, hb⟩ := Prod.mk.inj heq
            ha ▸ hb ▸ by
              rw [edist_nndist, ← (isometry_smul X g⁻¹).nndist_eq, inv_smul_smul, smul_smul]
              exact ENNReal.coe_le_coe.mpr <| Finset.le_sup' (fun k ↦ nndist x (k • x)) (hK hgh)⟩,
      coarselyProper_smul' G (fun t ht ↦
        let hcpt := Metric.isCompact_of_isClosed_isBounded isClosed_closure ht.isBounded.closure
        (ProperlyDiscontinuousSMul.finite_disjoint_inter_image hcpt hcpt).subset
          fun g hg ↦
            let ⟨y, hy_gt, hy_t⟩ := hg
            let ⟨z, hz, hyz⟩ := Set.mem_smul_set.mp hy_gt
            ⟨g • z, Set.smul_mem_smul_set (subset_closure hz), hyz ▸ subset_closure hy_t⟩) x⟩

/-- When a group acts on a nonempty metric space with compact quotient, the action is cocompact
in the coarse sense. -/
@[to_additive]
instance [Nonempty X] : CocompactSMul G X where
  univ_eq_smul :=
    let x₀ : X := Classical.ofNonempty
    ⟨closedBall x₀ (smul_closedBall_eq_univ x₀).choose,
    ⟨Metric.isBounded_closedBall.isCoarselyBounded, (smul_closedBall_eq_univ x₀).choose_spec.symm⟩⟩

end CoarseSpace

namespace QuasiIsometry

variable (G : Type*) [Group G] {X : Type*}

-- Metric hypotheses
variable [PseudoMetricSpace G] [PseudoMetricSpace X]
variable [ProperSpace G] [ProperSpace X]
variable [HasCoarseMidpoints G] [HasCoarseMidpoints X]

-- G is a discrete group with left-invariant metric
variable [DiscreteTopology G] [IsIsometricSMul G G]

-- G acts on X properly discontinuously, cocompactly, by isometries
variable [MulAction G X] [IsIsometricSMul G X]
variable [ProperlyDiscontinuousSMul G X]
variable [CompactSpace (MulAction.orbitRel.Quotient G X)]

/-- **Švarc-Milnor Lemma**: If a discrete group with a proper left-invariant metric acts
properly discontinuously, cocompactly, and by isometries on a proper metric space, then the
orbit map is a quasi-isometry equivalence. Note that both the group and the space must have
coarse midpoints. -/
@[to_additive]
noncomputable def mulOrbitQuasiIsometryEquiv (x₀ : X) : G ≃qi X :=
  letI : Nonempty X := ⟨x₀⟩
  (@CoarseEquiv.trans G G X
    (instCoarseSpaceOfPseudoEMetricSpace G)
    (CoarseSpace.instCoarseSpaceLeftMulRel G)
    (instCoarseSpaceOfPseudoEMetricSpace X)
    (CoarseSpace.coarseEquiv_metric_leftMul G)
    (CoarseSpace.mulOrbitCoarseEquiv G x₀)).toQuasiIsometryEquiv

/-- The orbit map `g ↦ g • x₀` is a quasi-isometry. -/
@[to_additive /--The orbit map `g ↦ g +ᵥ x₀` is a quasi-isometry.-/]
theorem mulOrbit_quasiIsometry (x₀ : X) : QuasiIsometry (fun g : G => g • x₀) :=
  letI : Nonempty X := ⟨x₀⟩
  (mulOrbitQuasiIsometryEquiv G x₀).quasiIsometry

end QuasiIsometry
