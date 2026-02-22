/-
Copyright (c) 2026 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.IsometricSMul

open Set Metric MulAction
open scoped Pointwise

variable (G : Type*) [Group G] {X : Type*}
variable [PseudoMetricSpace X] [MulAction G X] [IsIsometricSMul G X]
variable [CompactSpace (orbitRel.Quotient G X)]

/-- If a group `G` acts on a pseudo metric space `X` such that the quotient space
`orbitRel.Quotient G X` is compact, then the distance from a point to
`orbit G x₀` is bounded above, where `x₀` is a given basepoint. -/
@[to_additive]
theorem bddAbove_range_infDist_mulAction_orbit (x₀ : X) :
    BddAbove <| range <| fun x ↦ infDist x (orbit G x₀) :=
  -- infDist to the orbit is constant on orbits, so descends to quotient
  have orbit_eq : ∀ a b : X, orbitRel G X a b →
      infDist a (orbit G x₀) = infDist b (orbit G x₀) :=
    fun a b ⟨g, hg⟩ ↦
      calc infDist a (orbit G x₀)
          = infDist (g • b) (orbit G x₀) := hg.symm ▸ rfl
        _ = infDist (g • b) (g • orbit G x₀) := (smul_orbit g x₀).symm ▸ rfl
        _ = infDist b (orbit G x₀) :=
              image_smul (α := G) (β := X) (a := g) ▸ infDist_image (isometry_smul X g)
  -- Define the descended function on the quotient
  let dist' : orbitRel.Quotient G X → ℝ :=
    Quotient.lift (fun x ↦ infDist x (orbit G x₀)) orbit_eq
  -- dist' is continuous
  have hdist'_cont : Continuous dist' :=
    Continuous.quotient_lift (continuous_infDist_pt _) orbit_eq
  -- By compactness, dist' attains a maximum
  let ⟨q, ⟨_, (hq : IsMaxOn dist' univ q)⟩⟩ := CompactSpace.isCompact_univ.exists_isMaxOn
    (nonempty_iff_univ_nonempty.mp <|
      (nonempty_quotient_iff (orbitRel G X)).mpr ⟨x₀⟩)
    hdist'_cont.continuousOn
  -- The maximum value bounds the range
  ⟨dist' q, fun _ ⟨y, hy⟩ ↦ hy ▸ hq (mem_univ (Quotient.mk _ y))⟩

/-- For any point `x` in a pseudo metric space with a cocompact group action, there exists a
group element `g` such that the distance from `x` to `g • x₀` is strictly less than one plus
the supremum of distances to the orbit. -/
@[to_additive
/-- For any point `x` in a pseudo metric space with a cocompact additive group action, there
exists a group element `g` such that the distance from `x` to `g +ᵥ x₀` is strictly less than
one plus the supremum of distances to the orbit. -/]
lemma dist_smul_lt_one_add_sSup_range_infDist_orbit (x x₀ : X) :
    ∃ g : G, dist x (g • x₀) <
      1 + sSup (range fun x ↦ infDist x (orbit G x₀)) :=
  let R := sSup (range fun x ↦ infDist x (orbit G x₀))
  -- infDist x (orbit) ≤ R since x is in the range
  have hR : infDist x (orbit G x₀) ≤ R :=
    le_csSup (bddAbove_range_infDist_mulAction_orbit G x₀) ⟨x, rfl⟩
  -- So infDist x (orbit) < 1 + R
  have hlt : infDist x (orbit G x₀) < 1 + R :=
    lt_add_of_pos_of_le one_pos hR
  -- By definition of infDist, there exists y in orbit with dist x y < 1 + R
  let ⟨_, hy_mem, hy_dist⟩ :=
    (infDist_lt_iff ⟨x₀, mem_orbit_self x₀⟩).mp hlt
  -- Since y ∈ orbit, we have y = g • x₀ for some g
  let ⟨g, hg⟩ := mem_orbit_iff.mp hy_mem
  ⟨g, hg ▸ hy_dist⟩

/-- Under a cocompact group action, there exists a radius `ε` such that the orbit of the closed
ball `closedBall x₀ ε` under the full group covers the entire space. -/
@[to_additive
/-- Under a cocompact additive group action, there exists a radius `ε` such that the orbit of the
closed ball `closedBall x₀ ε` under the full group covers the entire space. -/]
theorem exists_smul_closedBall_eq_univ (x₀ : X) :
    ∃ ε : ℝ, (univ : Set G) • closedBall x₀ ε = univ :=
  ⟨1 + sSup (range fun x ↦ infDist x (orbit G x₀)),
    eq_univ_iff_forall.mpr fun x ↦
      let ⟨g, hg⟩ := dist_smul_lt_one_add_sSup_range_infDist_orbit (G := G) x x₀
      mem_smul.mpr ⟨g, mem_univ g, g⁻¹ • x,
        mem_closedBall.mpr (((isometry_smul X g).dist_eq ..).symm ▸
        (smul_inv_smul g x).symm ▸ le_of_lt hg), smul_inv_smul g x⟩⟩
