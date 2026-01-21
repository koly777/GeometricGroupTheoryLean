/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/

import Mathlib.Data.Nat.Lattice
import Mathlib.Topology.MetricSpace.Bounded

import CoarseSpace.ApproximateMidpoints
import CoarseSpace.Connected
import CoarseSpace.Finiteness

/-!
# The Metric Coarse Structure

This file defines the canonical coarse structure on (extended) pseudo-metric spaces and
establishes the connection between metric and coarse geometry.

## Main Definitions

* `instCoarseSpacePseudoEMetricSpace`: The canonical coarse structure on a pseudo-emetric space,
  where an entourage is controlled iff all pairs have uniformly bounded finite distance.
* `CoarseSpace.metricEntourage X r`: The entourage of pairs within distance `r`.

## Main Results

* `IsCoarselyBounded.isBounded`, `Bornology.IsBounded.isCoarselyBounded`: In a pseudo-metric
  space, coarsely bounded sets coincide with bornologically bounded sets.
* `instCoarselyConnectedSpacePseudoMetricSpace`: Pseudo-metric spaces are coarsely connected.
* `Controlled.exists_dist_upper`: A controlled map from a space with coarse midpoints satisfies
  a coarse Lipschitz bound: `nndist (f x) (f y) ≤ A * nndist x y + B`.
* `CoarseEquiv.exists_dist_lower`: A coarse equivalence into a space with coarse midpoints
  satisfies a reverse bound: `nndist x y ≤ A * nndist (e x) (e y) + B`.
* `instFGOfHasCoarseMidpoints`: A pseudo-metric space with coarse midpoints is finitely
  generated as a coarse space.

## Tags

coarse geometry, metric space, coarse structure
-/


open scoped NNReal ENNReal
open Set Entourage Prod

/-- Every extended pseudo-metric space carries a canonical coarse structure where an entourage is
controlled iff all pairs in it have finite bounded distance. -/
instance (X : Type*) [PseudoEMetricSpace X] : CoarseSpace X where
  IsControlled E := ∃ r : ℝ≥0, ∀ x y, (x, y) ∈ E → edist x y ≤ r
  isControlled_subset := fun ⟨r, hs⟩ ht ↦ ⟨r, fun x y a ↦ hs x y (ht a)⟩
  isControlled_union := fun ⟨r₁, hs⟩ ⟨r₂, ht⟩ ↦
    ⟨max r₁ r₂, fun x y hxy ↦ hxy.elim
      (fun h ↦ (hs x y h).trans (by exact_mod_cast le_max_left r₁ r₂))
      (fun h ↦ (ht x y h).trans (by exact_mod_cast le_max_right r₁ r₂))⟩
  isControlled_id := ⟨0, fun x _ h ↦ h ▸ (edist_self x).le⟩
  isControlled_inv := fun ⟨r, hs⟩ ↦ ⟨r, fun x y h ↦ edist_comm y x ▸ hs y x h⟩
  isControlled_comp := fun ⟨r₁, hs⟩ ⟨r₂, ht⟩ ↦
    ⟨r₁ + r₂, fun x z ⟨y, hxy, hyz⟩ ↦ (edist_triangle x y z).trans
      (add_le_add (hs x y hxy) (ht y z hyz))⟩

namespace CoarseSpace

section Basic

/-- In an extended pseudo-metric space, an entourage is controlled iff all its pairs have uniformly
bounded finite distance. -/
@[simp] theorem isControlled_emetric_iff {X} [PseudoEMetricSpace X] {E : Entourage X} :
    IsControlled E ↔ ∃ r : ℝ≥0, ∀ (x y : X), (x, y) ∈ E → edist x y ≤ r :=
  Iff.rfl

variable (X : Type*) [PseudoEMetricSpace X]

/-- The entourage of pairs within distance `r`. -/
def metricEntourage (r : ℝ≥0) : Entourage X :=
  { p | edist p.1 p.2 ≤ r }

@[simp]
theorem mem_metricEntourage {r : ℝ≥0} {x y : X} :
    (x, y) ∈ metricEntourage X r ↔ edist x y ≤ r :=
  Iff.rfl

/-- The identity entourage is contained in the metric entourage of radius 0. -/
theorem id_subset_metricEntourage_zero :
    Entourage.id ⊆ metricEntourage X 0 :=
  fun ⟨x, _⟩ h ↦ h ▸ (edist_self x).le

/-- Metric entourages are monotone with respect to the radius. -/
@[gcongr]
theorem metricEntourage_mono {r s : ℝ≥0} (h : r ≤ s) :
    metricEntourage X r ⊆ metricEntourage X s :=
  fun _ hp ↦ hp.trans (ENNReal.coe_le_coe.mpr h)

/-- The composition of metric entourages satisfies the triangle inequality. -/
theorem metricEntourage_comp (r s : ℝ≥0) :
    metricEntourage X r ○ metricEntourage X s ⊆ metricEntourage X (r + s) :=
  fun ⟨x, z⟩ ⟨y, hxy, hyz⟩ ↦ (edist_triangle x y z).trans (ENNReal.coe_add .. ▸ add_le_add hxy hyz)

/-- Metric entourages are symmetric. -/
theorem metricEntourage_inv (r : ℝ≥0) :
    (metricEntourage X r)⁻¹ = metricEntourage X r := by
  ext ⟨x, y⟩; simp [SetRel.mem_inv, edist_comm]

@[simp]
theorem isControlled_metricEntourage (r : ℝ≥0) :
    IsControlled (metricEntourage X r) :=
  ⟨r, fun _ _ h ↦ h⟩

theorem isControlled_iff_subset_metricEntourage {E : Entourage X} :
    IsControlled E ↔ ∃ r : ℝ≥0, E ⊆ metricEntourage X r :=
  ⟨fun ⟨r, h⟩ ↦ ⟨r, fun ⟨x, y⟩ hp ↦ h x y hp⟩,
   fun ⟨r, h⟩ ↦ ⟨r, fun _ _ hp ↦ h hp⟩⟩

/-- The coarse ball of a metric entourage equals the metric closed ball. -/
theorem ball_metricEntourage (r : ℝ≥0) (x : X) :
    (metricEntourage X r).ball x = EMetric.closedBall x r := by
  ext y; simp [Entourage.mem_ball_iff, EMetric.mem_closedBall, edist_comm]

/-- Powers of entourages contained in a metric entourage are contained in metric entourages
with linearly scaled radii. -/
theorem pow_subset_metricEntourage {E : Entourage X} {r : ℝ≥0} (hr : E ⊆ metricEntourage X r) :
    ∀ n : ℕ, E ^ n ⊆ metricEntourage X (n * r)
  | 0 => (Nat.cast_zero (R := ℝ≥0)).symm ▸ (zero_mul r).symm ▸
          pow_zero E ▸ id_subset_metricEntourage_zero X
  | n + 1 => (Nat.cast_succ (R := ℝ≥0) n).symm ▸
    calc E ^ (n + 1)
        _ = E ○ E ^ n := Entourage.pow_succ E n
        _ ⊆ metricEntourage X r ○ metricEntourage X (n * r) :=
              SetRel.comp_subset_comp hr (pow_subset_metricEntourage hr n)
        _ ⊆ metricEntourage X (r + n * r) := metricEntourage_comp X r (n * r)
        _ = metricEntourage X ((n + 1) * r) := by ring_nf

end Basic

section PseudoMetricSpace

variable (X : Type*) [PseudoMetricSpace X]

/-- Membership in `metricEntourage r` using `nndist`. -/
theorem mem_metricEntourage_nndist {r : ℝ≥0} {x y : X} :
    (x, y) ∈ metricEntourage X r ↔ nndist x y ≤ r := by
    simp only [mem_metricEntourage, edist_le_coe]


/-- The ball of `metricEntourage r` equals the closed metric ball. -/
theorem ball_metricEntourage_eq_closedBall (r : ℝ≥0) (x : X) :
    (metricEntourage X r).ball x = Metric.closedBall x r := by
  ext y
  simp only [Entourage.mem_ball_iff, mem_metricEntourage_nndist, Metric.mem_closedBall,
             ← NNReal.coe_le_coe, coe_nndist, nndist_comm, dist_comm]

end PseudoMetricSpace

end CoarseSpace

/-- A coarsely bounded set in a pseudo-metric space is bounded in the bornology sense. -/
theorem IsCoarselyBounded.isBounded {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs : IsCoarselyBounded s) : Bornology.IsBounded s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact Bornology.isBounded_empty
  · obtain ⟨r, hr⟩ := hs.isControlled
    refine (Metric.isBounded_iff_subset_closedBall x₀).mpr ⟨r, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_comm, dist_nndist]
    exact NNReal.GCongr.toReal_le_toReal <| edist_le_coe.mp (hr x₀ x (mk_mem_prod hx₀ hx))

/-- A bornologically bounded set in a pseudo-metric space is coarsely bounded. -/
theorem Bornology.IsBounded.isCoarselyBounded {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs : Bornology.IsBounded s) : IsCoarselyBounded s :=
  let ⟨C, hC⟩ := Metric.isBounded_iff.mp hs
  ⟨C.toNNReal, fun _ _ ⟨hx, hy⟩ ↦ by
    rw [edist_dist]; exact_mod_cast (hC hx hy).trans (le_max_left C 0)⟩

namespace CoarseSpace

section EMetric

variable {X : Type*} [EMetricSpace X]

/-- In an extended metric space, the metric entourage of radius 0 is contained in the
identity entourage. -/
theorem metricEntourage_zero_subset_id :
    metricEntourage X 0 ⊆ Entourage.id :=
  fun _ h ↦ edist_eq_zero.mp (le_antisymm ((mem_metricEntourage X).mp h) (zero_le _))

@[simp]
theorem metricEntourage_zero :
    metricEntourage X 0 = Entourage.id :=
  Set.Subset.antisymm metricEntourage_zero_subset_id (id_subset_metricEntourage_zero X)

end EMetric

section PseudoMetric

/-- A pseudo-metric space is coarsely connected: every pair of points has finite distance,
hence lies in some controlled entourage. -/
instance instCoarselyConnectedSpacePseudoMetricSpace (X : Type*) [PseudoMetricSpace X] :
    CoarselyConnectedSpace X where
  isCoarselyConnected_univ := isCoarselyConnected_iff.mpr fun x _ y _ ↦
    ⟨CoarseSpace.metricEntourage X (nndist x y),
     CoarseSpace.isControlled_metricEntourage X _, edist_le_coe.mpr le_rfl⟩

/-- If two functions are close in the coarse sense, then their values are uniformly bounded in
distance. -/
theorem IsClose.nndist_le {X : Type*} [PseudoMetricSpace X] {Z : Type*} {f g : Z → X} (h : f =ᶜ g) :
    ∃ R : ℝ≥0, ∀ z, nndist (f z) (g z) ≤ R :=
  let ⟨R, hR⟩ := h
  ⟨R, fun z => edist_le_coe.mp (hR (f z) (g z) ⟨z, rfl⟩)⟩

/-- A coarse equivalence between pseudo-metric spaces is coarsely surjective: every point in the
target is within bounded distance of some image point. -/
theorem CoarseEquiv.exists_coarsely_surj {X : Type*} {Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] (e : X ≃ᶜ Y) :
    ∃ C : ℝ≥0, ∀ y, ∃ x, nndist y (e x) ≤ C := by
  obtain ⟨R, hR⟩ := IsClose.nndist_le e.isClose_id_right
  exact ⟨R, fun y => ⟨e.symm y, nndist_comm (α := Y) _ _ ▸ hR y⟩⟩

variable (X : Type*) [PseudoMetricSpace X] [HasCoarseMidpoints X]

private noncomputable def constCMP : ℝ≥0 :=
  has_coarse_midpoints (X := X).choose

private theorem constCMP_spec
    (x y : X) : ∃ m, IsApproximateMidpoint x m y (constCMP X) :=
  has_coarse_midpoints.choose_spec x y

private theorem metricEntourage_subset_sq_of_midpoint (R : ℝ≥0) :
    metricEntourage X R ⊆ (metricEntourage X (R / 2 + constCMP X)) ^ 2 := fun ⟨x, y⟩ hxy =>
  let E := metricEntourage X (R / 2 + constCMP X)
  let ⟨m, hm⟩ := constCMP_spec X x y
  have hdist_xy : dist x y ≤ R := by
    rw [dist_edist]
    exact ENNReal.toReal_le_coe_of_le_coe hxy
  have hdx : (x, m) ∈ E := by
    rw [mem_metricEntourage, edist_dist]
    refine ENNReal.ofReal_le_coe.mpr ?_
    calc dist x m ≤ dist x y / 2 + constCMP X := hm.dist_left
      _ ≤ R / 2 + constCMP X := by linarith
  have hdy : (m, y) ∈ E := by
    rw [mem_metricEntourage, edist_dist]
    refine ENNReal.ofReal_le_coe.mpr ?_
    calc dist m y ≤ dist x y / 2 + constCMP X := hm.dist_right
      _ ≤ R / 2 + constCMP X := by linarith
  ⟨m, hdx, ⟨y, hdy, rfl⟩⟩

private noncomputable def iteratedRadius
    (R : ℝ≥0) : ℕ → ℝ≥0
  | 0 => R
  | k + 1 => iteratedRadius R k / 2 + constCMP X

@[simp] private theorem iteratedRadius_zero (R : ℝ≥0) : iteratedRadius X R 0 = R := rfl

@[simp] private theorem iteratedRadius_succ (R : ℝ≥0) (k : ℕ) :
    iteratedRadius X R (k + 1) = iteratedRadius X R k / 2 + constCMP X := rfl

private theorem iteratedRadius_le
    (R : ℝ≥0) (k : ℕ) :
    iteratedRadius X R k ≤ R / 2 ^ k + 2 * constCMP X := by
  induction k with
  | zero => simp [le_add_iff_nonneg_right]
  | succ k ih => calc iteratedRadius X R (k + 1)
      = iteratedRadius X R k / 2 + constCMP X := rfl
    _ ≤ (R / 2 ^ k + 2 * constCMP X) / 2 + constCMP X := by gcongr
    _ = R / 2 ^ (k + 1) + 2 * constCMP X := by ring

private theorem metricEntourage_subset_pow_two_pow (R : ℝ≥0) (k : ℕ) :
    metricEntourage X R ⊆ (metricEntourage X (iteratedRadius X R k)) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc metricEntourage X R
        ⊆ (metricEntourage X (iteratedRadius X R k)) ^ (2 ^ k) := ih
      _ ⊆ ((metricEntourage X (iteratedRadius X R k / 2 + constCMP X)) ^ 2) ^ (2 ^ k) :=
          Entourage.pow_mono (metricEntourage_subset_sq_of_midpoint X (iteratedRadius X R k)) _
      _ = (metricEntourage X (iteratedRadius X R (k + 1))) ^ (2 ^ (k + 1)) := by
          rw [← Entourage.pow_mul, _root_.pow_succ, mul_comm, iteratedRadius_succ]

private theorem metricEntourage_subset_pow_of_cmp {S : ℝ≥0} (hS : 2 * constCMP X < S) (R : ℝ≥0) :
    ∃ n : ℕ, (n : ℝ≥0) ≤ 2 * R / (S - 2 * constCMP X) + 1 ∧
             metricEntourage X R ⊆ (metricEntourage X S) ^ n := by
  let gap := S - 2 * constCMP X
  have hgap : 0 < gap := tsub_pos_of_lt hS
  have hex : ∃ k : ℕ, R / gap < 2 ^ k := by
    obtain ⟨n, hn⟩ := exists_nat_gt (R / gap)
    exact ⟨n, hn.trans_le (by exact_mod_cast Nat.lt_two_pow_self.le)⟩
  let k := Nat.find hex
  have hk_lt : R / gap < 2 ^ k := Nat.find_spec hex
  have hk_min : ∀ i < k, 2 ^ i ≤ R / gap := fun i hi ↦ le_of_not_gt (Nat.find_min hex hi)
  have hiter : iteratedRadius X R k ≤ S := by
    have h1 : R / 2 ^ k ≤ gap := by
      rw [div_le_iff₀ (pow_pos two_pos k)]
      exact mul_comm gap (2 ^ k) ▸ (div_lt_iff₀ hgap).mp hk_lt |>.le
    calc iteratedRadius X R k
        ≤ R / 2 ^ k + 2 * constCMP X := iteratedRadius_le X R k
      _ ≤ gap + 2 * constCMP X := by gcongr
      _ = S := tsub_add_cancel_of_le hS.le
  have hbound : (2 ^ k : ℝ≥0) ≤ 2 * R / gap + 1 := by
    by_cases hk0 : k = 0
    · rw [hk0, _root_.pow_zero]
      exact le_add_of_nonneg_left (zero_le _)
    · have hk_pred : 2 ^ (k - 1) ≤ R / gap :=
        hk_min (k - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos)
      calc (2 : ℝ≥0) ^ k
          = 2 ^ (k - 1 + 1) := by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
        _ = 2 * 2 ^ (k - 1) := pow_succ' 2 (k - 1)
        _ ≤ 2 * (R / gap) := by gcongr
        _ = 2 * R / gap := by rw [mul_div_assoc]
        _ ≤ 2 * R / gap + 1 := le_add_of_nonneg_right zero_le_one
  refine ⟨2 ^ k, ?_, ?_⟩
  · exact_mod_cast hbound
  · calc metricEntourage X R
        ⊆ (metricEntourage X _) ^ (2 ^ k) := metricEntourage_subset_pow_two_pow X R k
      _ ⊆ (metricEntourage X S) ^ (2 ^ k) := Entourage.pow_mono (metricEntourage_mono X hiter) _

variable {X : Type*} {Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [HasCoarseMidpoints X]

/-- A controlled map between pseudo-metric spaces with coarse midpoints satisfies a coarse Lipschitz
bound: distances in the image are bounded by a linear function of distances in the domain. -/
theorem Controlled.exists_dist_upper {f : X → Y} (hf : Controlled f) :
    ∃ A B : ℝ≥0, 1 ≤ A ∧ ∀ x y, nndist (f x) (f y) ≤ A * nndist x y + B := by
  -- Pick generator scale S > 2 * constCMP X
  let S := 2 * constCMP X + 1
  have hS : 2 * constCMP X < S := lt_add_of_pos_right _ one_pos
  -- hf gives S' with (metricEntourage X S).map f ⊆ metricEntourage Y S'
  obtain ⟨S', hS'⟩ := hf (isControlled_metricEntourage X S)
  refine ⟨max 1 (2 * S'), S', le_max_left _ _, fun x y => ?_⟩
  -- For any x y, get n with linear bound
  let R := nndist x y
  obtain ⟨n, hn_bound, hn_mem⟩ := metricEntourage_subset_pow_of_cmp X hS R
  -- (x, y) ∈ metricEntourage X R ⊆ (metricEntourage X S) ^ n
  have hxy_mem : (x, y) ∈ (metricEntourage X S) ^ n :=
    hn_mem ((mem_metricEntourage_nndist X).mpr le_rfl)
  -- (metricEntourage X S).map f ⊆ metricEntourage Y S'
  have hS'_sub : (metricEntourage X S).map f ⊆ metricEntourage Y S' := fun ⟨a, b⟩ h => hS' a b h
  -- (f x, f y) ∈ (metricEntourage Y S') ^ n
  have hfxy_mem : (f x, f y) ∈ (metricEntourage Y S') ^ n :=
    Entourage.pow_mono hS'_sub n (map_pow f _ n (mem_map_iff.mpr ⟨x, y, hxy_mem, rfl, rfl⟩))
  -- nndist (f x) (f y) ≤ n * S'
  have hfxy_dist : nndist (f x) (f y) ≤ n * S' :=
    (mem_metricEntourage_nndist Y).mp (pow_subset_metricEntourage (X := Y) le_rfl n hfxy_mem)
  -- S - 2 * constCMP X = 1 by construction
  have hgap : S - 2 * constCMP X = 1 := add_tsub_cancel_left (2 * constCMP X) 1
  calc nndist (f x) (f y)
      ≤ n * S' := hfxy_dist
    _ ≤ (2 * R / (S - 2 * constCMP X) + 1) * S' := by gcongr
    _ = (2 * R + 1) * S' := by rw [hgap, div_one]
    _ = 2 * S' * R + S' := by ring
    _ ≤ max 1 (2 * S') * R + S' := by gcongr; exact le_max_right _ _
    _ = max 1 (2 * S') * nndist x y + S' := rfl

variable [HasCoarseMidpoints Y]

omit [HasCoarseMidpoints X] in
/-- A coarse equivalence between pseudo-metric spaces with coarse midpoints satisfies a reverse
coarse Lipschitz bound: distances in the domain are bounded by a linear function of distances
in the image. -/
theorem CoarseEquiv.exists_dist_lower (e : X ≃ᶜ Y) :
    ∃ A B : ℝ≥0, 1 ≤ A ∧ ∀ x y, nndist x y ≤ A * nndist (e x) (e y) + B := by
  -- Get upper bound for e.symm
  obtain ⟨A, B, hA, hAB⟩ := Controlled.exists_dist_upper e.coarse_invFun.controlled
  -- Get closeness constant for e.symm ∘ e =ᶜ id
  obtain ⟨R, hR⟩ := IsClose.nndist_le e.isClose_id_left
  refine ⟨A, 2 * R + B, hA, fun x y => ?_⟩
  calc nndist x y
      ≤ nndist x (e.symm (e x)) + nndist (e.symm (e x)) y := nndist_triangle _ _ _
    _ ≤ nndist x _ + (nndist (e.symm (e x)) (e.symm (e y)) + nndist (e.symm (e y)) y) := by
        gcongr; exact nndist_triangle _ _ _
    _ ≤ R + (nndist (e.symm (e x)) (e.symm (e y)) + R) := by
        gcongr
        · rw [nndist_comm]; exact hR x
        · exact hR y
    _ ≤ R + ((A * nndist (e x) (e y) + B) + R) := by gcongr; exact hAB (e x) (e y)
    _ = A * nndist (e x) (e y) + (2 * R + B) := by ring

/-- A pseudo-metric space with coarse midpoints is finitely generated as a coarse space. -/
instance instFGOfHasCoarseMidpoints : FG X :=
  let S := 2 * constCMP X + 1
  have hS : 2 * constCMP X < S := lt_add_of_pos_right _ one_pos
  FG.of_single (metricEntourage X S) fun _ =>
    ⟨fun hF => hF.rec
      (fun _ hE => hE ▸ isControlled_metricEntourage X S)
      (fun _ hsub hE => hE.subset hsub)
      (fun _ _ hE hF => hE.union hF)
      isControlled_id
      (fun _ hE => hE.inv)
      (fun _ _ hE hF => hE.comp hF),
    fun ⟨R, hR⟩ =>
      let ⟨n, _, hn⟩ := metricEntourage_subset_pow_of_cmp X hS R
      (GenerateControlled.pow_single _ n).subset (fun p hp => hn (hR p.1 p.2 hp))⟩

end PseudoMetric

end CoarseSpace
