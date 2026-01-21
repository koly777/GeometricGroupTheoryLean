/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Quasi-isometries

This file defines quasi-isometries between pseudo-metric spaces.

A **quasi-isometry** is a map `f : α → β` between metric spaces that distorts distances by at most
a multiplicative constant plus an additive constant, both in the expanding and contracting
directions, and is "coarsely surjective" (every point in the target is within bounded distance
from the image).

## Main definitions

* `QuasiIsometryWith A B C f`: The predicate stating that `f` is an `(A, B, C)`-quasi-isometry,
  meaning:
  - `A ≥ 1` (multiplicative constant)
  - `∀ x y, dist (f x) (f y) ≤ A * dist x y + B` (upper bound on distances)
  - `∀ x y, dist x y ≤ A * dist (f x) (f y) + B` (lower bound on distances)
  - `∀ y, ∃ x, dist y (f x) ≤ C` (coarse surjectivity)

* `QuasiIsometry f`: The predicate stating that `f` is a quasi-isometry for some constants.

* `QuasiIsometryClass F α β`: A typeclass for types of quasi-isometries.

* `QuasiIsometryEquiv α β` (notation: `α ≃qi β`): A bundled quasi-isometry equivalence,
  consisting of a quasi-isometry and a quasi-inverse that compose to maps close to identity.

## Main results

### Structure theorems
* `QuasiIsometryWith.id`: The identity is a `(1, 0, 0)`-quasi-isometry.
* `QuasiIsometryWith.comp`: Composition of quasi-isometries is a quasi-isometry.
* `QuasiIsometryWith.fromIsometry`: An isometry is a `(1, 0, 0)`-quasi-isometry.

### Monotonicity
* `QuasiIsometryWith.mono_left/middle/right`: Quasi-isometry bounds can be relaxed.

### Products
* `QuasiIsometryWith.prodMap`: Product of quasi-isometries is a quasi-isometry.
* `QuasiIsometryWith.piMap`: Finite product of quasi-isometries is a quasi-isometry.

### Metric properties
* `QuasiIsometryWith.mapsTo_ball`: Quasi-isometries map balls into balls.
* `QuasiIsometryWith.diam_image_le`: Quasi-isometries control diameter.

### Lipschitz connections
* `QuasiIsometryWith.lipschitzWith`: An `(A, 0, C)`-quasi-isometry is `A`-Lipschitz.
* `QuasiIsometryWith.antilipschitzWith`: An `(A, 0, C)`-quasi-isometry is `A`-antilipschitz.

## Notation

* `α ≃qi β`: Notation for `QuasiIsometryEquiv α β`.

## Implementation notes

We formulate the distance bounds using `NNReal` (non-negative reals) for the constants to ensure
non-negativity, while the distance inequalities use `dist`. The structure `QuasiIsometryWith`
provides explicit constants, while `QuasiIsometry` is the existential predicate. The bundled
`QuasiIsometryEquiv` packages both directions with their closeness guarantees.

## Tags

quasi-isometry, coarse geometry, geometric group theory

## References

* C. Druțu, M. Kapovich, *Geometric Group Theory*, Colloquium Publications 63, AMS, 2018
-/

open Function Set
open scoped Topology NNReal

universe u v w u₁

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u₁}
variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ] [PseudoMetricSpace δ]

/-! ## Explicit Constants: `QuasiIsometryWith` -/

/-- `QuasiIsometryWith A B C f` means `f` is an `(A, B, C)`-quasi-isometry:
- `A ≥ 1` is the multiplicative distortion constant
- `B` is the additive distortion constant
- `C` is the coarse surjectivity constant

The distance bounds are:
- Upper: `dist (f x) (f y) ≤ A * dist x y + B`
- Lower: `dist x y ≤ A * dist (f x) (f y) + B`
- Coarse surjectivity: every point in the target is within distance `C` of the image. -/
structure QuasiIsometryWith (A B C : ℝ≥0) (f : α → β) : Prop where
  one_le_A : 1 ≤ A
  dist_upper : ∀ x y, dist (f x) (f y) ≤ A * dist x y + B
  dist_lower : ∀ x y, dist x y ≤ A * dist (f x) (f y) + B
  coarsely_surj : ∀ y, ∃ x, dist y (f x) ≤ C

namespace QuasiIsometryWith

variable {A B C : ℝ≥0} {f : α → β}

/-- Upper bound on distances in terms of `nndist`. -/
theorem nndist_upper (hf : QuasiIsometryWith A B C f) (x y : α) :
    nndist (f x) (f y) ≤ A * nndist x y + B := by
  have := hf.dist_upper x y
  simp only [← coe_nndist] at this
  exact this

/-- Lower bound on distances in terms of `nndist`. -/
theorem nndist_lower (hf : QuasiIsometryWith A B C f) (x y : α) :
    nndist x y ≤ A * nndist (f x) (f y) + B := by
  have := hf.dist_lower x y
  simp only [← coe_nndist] at this
  exact this

variable {A A' B B' C C' : ℝ≥0} {f : α → β}

/-- Constructor for `QuasiIsometryWith` using `nndist` bounds. -/
theorem of_nndist
    (hA : 1 ≤ A)
    (hu : ∀ x y, nndist (f x) (f y) ≤ A * nndist x y + B)
    (hl : ∀ x y, nndist x y ≤ A * nndist (f x) (f y) + B)
    (hs : ∀ y, ∃ x, nndist y (f x) ≤ C) : QuasiIsometryWith A B C f where
  one_le_A := hA
  dist_upper x y := by simpa only [← coe_nndist, NNReal.coe_le_coe] using hu x y
  dist_lower x y := by simpa only [← coe_nndist, NNReal.coe_le_coe] using hl x y
  coarsely_surj y := by
    obtain ⟨x, hx⟩ := hs y
    exact ⟨x, by simpa only [← coe_nndist, NNReal.coe_le_coe] using hx⟩

/-- Relaxing the multiplicative constant `A` preserves quasi-isometry. -/
theorem mono_left (hA : A ≤ A') (hf : QuasiIsometryWith A B C f) :
    QuasiIsometryWith A' B C f where
  one_le_A := hf.one_le_A.trans hA
  dist_upper x y := (hf.dist_upper x y).trans (by gcongr)
  dist_lower x y := (hf.dist_lower x y).trans (by gcongr)
  coarsely_surj := hf.coarsely_surj

/-- Relaxing the additive constant `B` preserves quasi-isometry. -/
theorem mono_middle (hB : B ≤ B') (hf : QuasiIsometryWith A B C f) :
    QuasiIsometryWith A B' C f where
  one_le_A := hf.one_le_A
  dist_upper x y := (hf.dist_upper x y).trans (by gcongr)
  dist_lower x y := (hf.dist_lower x y).trans (by gcongr)
  coarsely_surj := hf.coarsely_surj

/-- Relaxing the coarse surjectivity constant `C` preserves quasi-isometry. -/
theorem mono_right (hC : C ≤ C') (hf : QuasiIsometryWith A B C f) :
    QuasiIsometryWith A B C' f where
  one_le_A := hf.one_le_A
  dist_upper := hf.dist_upper
  dist_lower := hf.dist_lower
  coarsely_surj y := let ⟨x, hx⟩ := hf.coarsely_surj y; ⟨x, hx.trans (by exact_mod_cast hC)⟩

/-- Relaxing all constants preserves quasi-isometry. -/
theorem mono (hA : A ≤ A') (hB : B ≤ B') (hC : C ≤ C') (hf : QuasiIsometryWith A B C f) :
    QuasiIsometryWith A' B' C' f := mono_right hC (mono_middle hB (mono_left hA hf))

/-- The identity map is a `(1, 0, 0)`-quasi-isometry. -/
@[simp] theorem id : QuasiIsometryWith 1 0 0 (id : α → α) where
  one_le_A := le_refl 1
  dist_upper x y := by simp
  dist_lower x y := by simp
  coarsely_surj y := ⟨y, by simp⟩

/-- Composition of quasi-isometries is a quasi-isometry.

If `f : α → β` is an `(A, B, C)`-quasi-isometry and `g : β → γ` is an `(A', B', C')`-quasi-isometry,
then `g ∘ f` is an `(A * A', A * B' + A' * B, C' + A' * C + B')`-quasi-isometry. -/
theorem comp {f : α → β} {g : β → γ}
    (hg : QuasiIsometryWith A' B' C' g) (hf : QuasiIsometryWith A B C f) :
    QuasiIsometryWith (A * A') (A * B' + A' * B) (C' + A' * C + B') (g ∘ f) where
  one_le_A := one_le_mul hf.one_le_A hg.one_le_A
  dist_upper x y := calc
    dist (g (f x)) (g (f y))
      ≤ A' * dist (f x) (f y) + B' := hg.dist_upper _ _
    _ ≤ A' * (A * dist x y + B) + B' := by gcongr; exact hf.dist_upper _ _
    _ = A * A' * dist x y + A' * B + B' := by ring
    _ ≤ A * A' * dist x y + A' * B + A * B' := by
        gcongr; exact le_mul_of_one_le_left (by positivity) hf.one_le_A
    _ = A * A' * dist x y + (A * B' + A' * B) := by ring
  dist_lower x y := calc
    dist x y
      ≤ A * dist (f x) (f y) + B := hf.dist_lower _ _
    _ ≤ A * (A' * dist (g (f x)) (g (f y)) + B') + B := by gcongr; exact hg.dist_lower _ _
    _ = A * A' * dist (g (f x)) (g (f y)) + A * B' + B := by ring
    _ ≤ A * A' * dist (g (f x)) (g (f y)) + A * B' + A' * B := by
        gcongr; exact le_mul_of_one_le_left (by positivity) hg.one_le_A
    _ = A * A' * dist (g (f x)) (g (f y)) + (A * B' + A' * B) := by ring
  coarsely_surj z := by
    obtain ⟨y, hy⟩ := hg.coarsely_surj z
    obtain ⟨x, hx⟩ := hf.coarsely_surj y
    exact ⟨x, calc dist z (g (f x))
                 ≤ dist z (g y) + dist (g y) (g (f x)) := dist_triangle _ _ _
               _ ≤ C' + (A' * dist y (f x) + B') := by gcongr; exact hg.dist_upper _ _
               _ ≤ C' + (A' * C + B') := by gcongr
               _ = C' + A' * C + B' := by ring⟩

/-! ### Connection to isometries -/
section Isometry

/-- A surjective isometry is a `(1, 0, 0)`-quasi-isometry. -/
theorem fromIsometry (h : Isometry f) (hsurj : Function.Surjective f) :
    QuasiIsometryWith 1 0 0 f where
  one_le_A := le_refl 1
  dist_upper x y := by simp [h.dist_eq]
  dist_lower x y := by simp [h.dist_eq]
  coarsely_surj y := let ⟨x, hx⟩ := hsurj y; ⟨x, by simp [hx]⟩

/-- Alias for `fromIsometry`. -/
theorem of_isometry (h : Isometry f) (hsurj : Function.Surjective f) :
    QuasiIsometryWith 1 0 0 f := fromIsometry h hsurj

end Isometry

/-! ### Connection to Lipschitz maps -/

/-- A quasi-isometry with zero additive constant is Lipschitz. -/
theorem lipschitzWith (hf : QuasiIsometryWith A 0 C f) : LipschitzWith A f := fun x y => by
  simp only [edist_nndist]
  have := hf.nndist_upper x y
  simp only [add_zero] at this
  exact_mod_cast this

/-- A quasi-isometry with zero additive constant is antilipschitz. -/
theorem antilipschitzWith (hf : QuasiIsometryWith A 0 C f) : AntilipschitzWith A f := fun x y => by
  simp only [edist_nndist]
  have := hf.nndist_lower x y
  simp only [add_zero] at this
  exact_mod_cast this

/-! ### Products and Pi types -/
section ProdPi

/-- The product of two quasi-isometries is a quasi-isometry on the product space.

The constants become the maximum of the individual constants. -/
theorem prodMap {f : α → β} {g : γ → δ}
    (hf : QuasiIsometryWith A B C f) (hg : QuasiIsometryWith A' B' C' g) :
    QuasiIsometryWith (max A A') (max B B') (max C C') (Prod.map f g) where
  one_le_A := le_max_iff.mpr (Or.inl hf.one_le_A)
  dist_upper x y := by
    simp only [Prod.dist_eq]
    apply max_le
    · calc dist (f x.1) (f y.1)
          ≤ A * dist x.1 y.1 + B := hf.dist_upper _ _
        _ ≤ max A A' * dist x.1 y.1 + max B B' := by
            gcongr <;> exact le_max_left ..
        _ ≤ max A A' * max (dist x.1 y.1) (dist x.2 y.2) + max B B' := by
            gcongr; exact le_max_left ..
    · calc dist (g x.2) (g y.2)
          ≤ A' * dist x.2 y.2 + B' := hg.dist_upper ..
        _ ≤ max A A' * dist x.2 y.2 + max B B' := by
            gcongr <;> exact le_max_right ..
        _ ≤ max A A' * max (dist x.1 y.1) (dist x.2 y.2) + max B B' := by
            gcongr; exact le_max_right ..
  dist_lower x y := by
    simp only [Prod.dist_eq]
    apply max_le
    · calc dist x.1 y.1
          ≤ A * dist (f x.1) (f y.1) + B := hf.dist_lower ..
        _ ≤ max A A' * dist (f x.1) (f y.1) + max B B' := by
            gcongr <;> exact le_max_left ..
        _ ≤ max A A' * max (dist (f x.1) (f y.1)) (dist (g x.2) (g y.2)) + max B B' := by
            gcongr; exact le_max_left ..
    · calc dist x.2 y.2
          ≤ A' * dist (g x.2) (g y.2) + B' := hg.dist_lower ..
        _ ≤ max A A' * dist (g x.2) (g y.2) + max B B' := by
            gcongr <;> exact le_max_right ..
        _ ≤ max A A' * max (dist (f x.1) (f y.1)) (dist (g x.2) (g y.2)) + max B B' := by
            gcongr; exact le_max_right ..
  coarsely_surj := fun ⟨y₁, y₂⟩ => by
    obtain ⟨x₁, hx₁⟩ := hf.coarsely_surj y₁
    obtain ⟨x₂, hx₂⟩ := hg.coarsely_surj y₂
    refine ⟨(x₁, x₂), ?_⟩
    simp only [Prod.dist_eq, Prod.map_apply]
    exact max_le (hx₁.trans (by exact_mod_cast le_max_left ..))
                 (hx₂.trans (by exact_mod_cast le_max_right ..))

/-- The pointwise map of quasi-isometries on a finite Pi type is a quasi-isometry.

The constants become the supremum over the indices. -/
theorem piMap {ι : Type*} [Fintype ι] [Nonempty ι] {X Y : ι → Type*}
    [∀ i, PseudoMetricSpace (X i)] [∀ i, PseudoMetricSpace (Y i)]
    {A B C : ι → ℝ≥0} {f : ∀ i, X i → Y i}
    (hf : ∀ i, QuasiIsometryWith (A i) (B i) (C i) (f i)) :
    QuasiIsometryWith (Finset.univ.sup A) (Finset.univ.sup B) (Finset.univ.sup C) (Pi.map f) where
  one_le_A := by
    obtain ⟨i⟩ : Nonempty ι := inferInstance
    exact le_trans (hf i).one_le_A (Finset.le_sup (Finset.mem_univ i))
  dist_upper x y := by
    have h : nndist (Pi.map f x) (Pi.map f y) ≤
      Finset.univ.sup A * nndist x y + Finset.univ.sup B := by
      rw [nndist_pi_le_iff]
      intro i
      calc nndist (f i (x i)) (f i (y i))
          ≤ A i * nndist (x i) (y i) + B i := (hf i).nndist_upper _ _
        _ ≤ Finset.univ.sup A * nndist (x i) (y i) + Finset.univ.sup B := by
            gcongr <;> exact Finset.le_sup (Finset.mem_univ i)
        _ ≤ Finset.univ.sup A * nndist x y + Finset.univ.sup B := by
            gcongr; exact nndist_le_pi_nndist x y i
    exact_mod_cast h
  dist_lower x y := by
    have h : nndist x y ≤
      Finset.univ.sup A * nndist (Pi.map f x) (Pi.map f y) + Finset.univ.sup B := by
      rw [nndist_pi_le_iff]
      intro i
      calc nndist (x i) (y i)
          ≤ A i * nndist (f i (x i)) (f i (y i)) + B i := (hf i).nndist_lower _ _
        _ ≤ Finset.univ.sup A * nndist (f i (x i)) (f i (y i)) + Finset.univ.sup B := by
            gcongr <;> exact Finset.le_sup (Finset.mem_univ i)
        _ ≤ Finset.univ.sup A * nndist (Pi.map f x) (Pi.map f y) + Finset.univ.sup B := by
            gcongr; exact nndist_le_pi_nndist (fun i ↦ f i (x i)) (fun i ↦ f i (y i)) i
    exact_mod_cast h
  coarsely_surj y := by
    choose x hx using fun i => (hf i).coarsely_surj (y i)
    refine ⟨x, ?_⟩
    have h : nndist y (Pi.map f x) ≤ Finset.univ.sup C := by
      rw [nndist_pi_le_iff]
      intro i
      calc nndist (y i) (f i (x i))
          ≤ C i := by simpa only [← coe_nndist, NNReal.coe_le_coe] using hx i
        _ ≤ Finset.univ.sup C := Finset.le_sup (Finset.mem_univ i)
    exact_mod_cast h

end ProdPi

/-! ### Metric ball and diameter bounds -/

/-- Quasi-isometries map open balls into open balls of controlled radius. -/
theorem mapsTo_ball (hf : QuasiIsometryWith A B C f) (x : α) (r : ℝ≥0) :
    Set.MapsTo f (Metric.ball x r) (Metric.ball (f x) (A * r + B)) := fun y hy ↦ by
  simp only [Metric.mem_ball] at hy ⊢
  calc dist (f y) (f x)
      ≤ A * dist y x + B := hf.dist_upper y x
    _ < A * r + B := by gcongr; exact one_pos.trans_le hf.one_le_A

/-- Quasi-isometries map closed balls into closed balls of controlled radius. -/
theorem mapsTo_closedBall (hf : QuasiIsometryWith A B C f) (x : α) (r : ℝ≥0) :
    Set.MapsTo f (Metric.closedBall x r) (Metric.closedBall (f x) (A * r + B)) := fun y hy ↦ by
  simp only [Metric.mem_closedBall] at hy ⊢
  calc dist (f y) (f x)
      ≤ A * dist y x + B := hf.dist_upper y x
    _ ≤ A * r + B := by gcongr

/-- The diameter of an image under a quasi-isometry is bounded by the diameter of the
original set times `A` plus `B`. -/
theorem diam_image_le (hf : QuasiIsometryWith A B C f) (s : Set α) :
    Metric.diam (f '' s) ≤ A * Metric.diam s + B := by
  by_cases hb : Bornology.IsBounded s
  · refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    calc dist (f x) (f y)
        ≤ A * dist x y + B := hf.dist_upper x y
      _ ≤ A * Metric.diam s + B := by
        gcongr
        exact Metric.dist_le_diam_of_mem hb hx hy
  · have hs : s.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro he
      exact hb (he ▸ Bornology.isBounded_empty)
    obtain ⟨z, hz⟩ := hs
    have hbf : ¬Bornology.IsBounded (f '' s) := by
      intro hbf
      apply hb
      obtain ⟨R, hR⟩ := hbf.subset_ball (f z)
      refine Metric.isBounded_iff.mpr ⟨A * (R + R) + B, fun x hx y hy ↦ ?_⟩
      have hfx : f x ∈ Metric.closedBall (f z) R := Metric.ball_subset_closedBall (hR ⟨x, hx, rfl⟩)
      have hfy : f y ∈ Metric.closedBall (f z) R := Metric.ball_subset_closedBall (hR ⟨y, hy, rfl⟩)
      calc dist x y
          ≤ A * dist (f x) (f y) + B := hf.dist_lower x y
        _ ≤ A * (dist (f x) (f z) + dist (f z) (f y)) + B := by gcongr; exact dist_triangle _ _ _
        _ ≤ A * (R + R) + B := by
          gcongr
          · exact Metric.mem_closedBall.mp hfx
          · exact Metric.mem_closedBall'.mp hfy
    simp [Metric.diam_eq_zero_of_unbounded hb, Metric.diam_eq_zero_of_unbounded hbf]

/-- The diameter of the range is bounded by the diameter of the domain times `A` plus `B`. -/
theorem diam_range_le (hf : QuasiIsometryWith A B C f) :
    Metric.diam (Set.range f) ≤ A * Metric.diam (Set.univ : Set α) + B :=
  Set.image_univ ▸ hf.diam_image_le Set.univ

/-- A ball of radius `(r - B) / A` is contained in the preimage of a ball of radius `r`. -/
theorem preimage_ball_subset (hf : QuasiIsometryWith A B C f) (x : α) (r : ℝ≥0) :
    Metric.ball x ((r - B) / A) ⊆ f ⁻¹' Metric.ball (f x) r := fun y hy ↦ by
  simp only [Set.mem_preimage, Metric.mem_ball] at hy ⊢
  have hA : (0 : ℝ) < A := one_pos.trans_le hf.one_le_A
  have hrB : B ≤ r := by
    by_contra h'
    push_neg at h'
    have h3 : (↑r - ↑B) / ↑A ≤ (0 : ℝ) := by
      apply div_nonpos_of_nonpos_of_nonneg
      · have : (↑r : ℝ) < ↑B := NNReal.coe_lt_coe.mpr h'
        linarith
      · linarith
    have : dist y x < 0 := lt_of_lt_of_le hy h3
    exact not_lt.mpr dist_nonneg this
  calc dist (f y) (f x)
      ≤ A * dist y x + B := hf.dist_upper y x
    _ < A * ((r - B) / A) + B := by gcongr
    _ = (r - B) + B := by field_simp
    _ = r := tsub_add_cancel_of_le hrB

/-- The preimage of a ball of radius `r` is contained in a ball of radius `A * r + B`. -/
theorem ball_subset_preimage (hf : QuasiIsometryWith A B C f) (x : α) (r : ℝ≥0) :
    f ⁻¹' Metric.ball (f x) r ⊆ Metric.ball x (A * r + B) := fun y hy ↦ by
  simp only [Set.mem_preimage, Metric.mem_ball] at hy ⊢
  calc dist y x
      ≤ A * dist (f y) (f x) + B := hf.dist_lower y x
    _ < A * r + B := by gcongr; exact one_pos.trans_le hf.one_le_A

/-! ### Quasi-inverses -/

/-- If `f` is a quasi-isometry and `g` is a right inverse of `f`, then `g` is also a
quasi-isometry with the same `A` and `B` constants. -/
theorem right_inv {g : β → α} (hf : QuasiIsometryWith A B C f) (hg : Function.RightInverse g f)
    (hclose : ∀ x, dist x (g (f x)) ≤ C') :
    QuasiIsometryWith A B C' g where
  one_le_A := hf.one_le_A
  dist_upper y₁ y₂ := by
    have := hf.dist_lower (g y₁) (g y₂)
    simp only [hg y₁, hg y₂] at this
    exact this
  dist_lower y₁ y₂ := by
    have := hf.dist_upper (g y₁) (g y₂)
    simp only [hg y₁, hg y₂] at this
    exact this
  coarsely_surj x := ⟨f x, hclose x⟩

end QuasiIsometryWith

/-! ## Existential Predicate: `QuasiIsometry` -/

/-- A map `f : α → β` is a quasi-isometry if there exist constants `A ≥ 1`, `B ≥ 0`, `C ≥ 0`
such that `f` is an `(A, B, C)`-quasi-isometry.

This is the existential version of `QuasiIsometryWith`, useful when the specific constants
are not important. -/
def QuasiIsometry [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) : Prop :=
  ∃ A B C : ℝ≥0, QuasiIsometryWith A B C f

namespace QuasiIsometry

/-- Construct `QuasiIsometry` from `QuasiIsometryWith`. -/
theorem of_quasiIsometryWith {A B C : ℝ≥0} {f : α → β} (h : QuasiIsometryWith A B C f) :
    QuasiIsometry f := ⟨A, B, C, h⟩

/-- Extract the constants witnessing that `f` is a quasi-isometry. -/
theorem exists_constants {f : α → β} (h : QuasiIsometry f) :
    ∃ A B C : ℝ≥0, QuasiIsometryWith A B C f := h

/-- The identity is a quasi-isometry. -/
@[simp] theorem id : QuasiIsometry (id : α → α) :=
  of_quasiIsometryWith QuasiIsometryWith.id

/-- Composition of quasi-isometries is a quasi-isometry. -/
theorem comp {f : α → β} {g : β → γ} (hg : QuasiIsometry g) (hf : QuasiIsometry f) :
    QuasiIsometry (g ∘ f) := by
  obtain ⟨A, B, C, hf⟩ := hf
  obtain ⟨A', B', C', hg⟩ := hg
  exact of_quasiIsometryWith (hg.comp hf)

/-- A surjective isometry is a quasi-isometry. -/
theorem of_isometry {f : α → β} (h : Isometry f) (hsurj : Function.Surjective f) :
    QuasiIsometry f := of_quasiIsometryWith (QuasiIsometryWith.of_isometry h hsurj)

/-- Product of quasi-isometries is a quasi-isometry. -/
theorem prodMap {f : α → β} {g : γ → δ} (hf : QuasiIsometry f) (hg : QuasiIsometry g) :
    QuasiIsometry (Prod.map f g) := by
  obtain ⟨A, B, C, hf⟩ := hf
  obtain ⟨A', B', C', hg⟩ := hg
  exact of_quasiIsometryWith (hf.prodMap hg)

/-- Pointwise map of quasi-isometries on a finite Pi type is a quasi-isometry. -/
theorem piMap {ι : Type*} [Fintype ι] [Nonempty ι] {X Y : ι → Type*}
    [∀ i, PseudoMetricSpace (X i)] [∀ i, PseudoMetricSpace (Y i)]
    {f : ∀ i, X i → Y i} (hf : ∀ i, QuasiIsometry (f i)) :
    QuasiIsometry (Pi.map f) := by
  choose A B C hf using hf
  exact of_quasiIsometryWith (QuasiIsometryWith.piMap hf)

/-- A quasi-isometry has an upper bound on distances. -/
theorem dist_upper_exists {f : α → β} (h : QuasiIsometry f) :
    ∃ A B : ℝ≥0, ∀ x y, dist (f x) (f y) ≤ A * dist x y + B := by
  obtain ⟨A, B, _, hf⟩ := h
  exact ⟨A, B, hf.dist_upper⟩

/-- A quasi-isometry has a lower bound on distances. -/
theorem dist_lower_exists {f : α → β} (h : QuasiIsometry f) :
    ∃ A B : ℝ≥0, ∀ x y, dist x y ≤ A * dist (f x) (f y) + B := by
  obtain ⟨A, B, _, hf⟩ := h
  exact ⟨A, B, hf.dist_lower⟩

/-- A quasi-isometry is coarsely surjective. -/
theorem coarsely_surj_exists {f : α → β} (h : QuasiIsometry f) :
    ∃ C : ℝ≥0, ∀ y, ∃ x, dist y (f x) ≤ C := by
  obtain ⟨_, _, C, hf⟩ := h
  exact ⟨C, hf.coarsely_surj⟩

/-- A quasi-isometry has an upper bound on distances (using `nndist`). -/
theorem nndist_upper_exists {f : α → β} (h : QuasiIsometry f) :
    ∃ A B : ℝ≥0, ∀ x y, nndist (f x) (f y) ≤ A * nndist x y + B := by
  obtain ⟨A, B, _, hf⟩ := h
  exact ⟨A, B, hf.nndist_upper⟩

/-- A quasi-isometry has a lower bound on distances (using `nndist`). -/
theorem nndist_lower_exists {f : α → β} (h : QuasiIsometry f) :
    ∃ A B : ℝ≥0, ∀ x y, nndist x y ≤ A * nndist (f x) (f y) + B := by
  obtain ⟨A, B, _, hf⟩ := h
  exact ⟨A, B, hf.nndist_lower⟩

/-- The image of a set under a quasi-isometry has controlled diameter. -/
theorem diam_image_le_exists {f : α → β} (h : QuasiIsometry f) (s : Set α) :
    ∃ A B : ℝ≥0, Metric.diam (f '' s) ≤ A * Metric.diam s + B := by
  obtain ⟨A, B, _, hf⟩ := h
  exact ⟨A, B, hf.diam_image_le s⟩

/-- The range of a quasi-isometry has controlled diameter. -/
theorem diam_range_le_exists {f : α → β} (h : QuasiIsometry f) :
    ∃ A B : ℝ≥0, Metric.diam (Set.range f) ≤ A * Metric.diam (Set.univ : Set α) + B := by
  obtain ⟨A, B, _, hf⟩ := h
  exact ⟨A, B, hf.diam_range_le⟩

end QuasiIsometry

/-! ## Typeclass: `QuasiIsometryClass` -/

/-- `QuasiIsometryClass F α β` states that `F` is a type of quasi-isometries from `α` to `β`.

This is a typeclass for bundled quasi-isometry types, analogous to `IsometryClass`. -/
class QuasiIsometryClass (F : Type*) (α β : outParam Type*) [PseudoMetricSpace α]
    [PseudoMetricSpace β] [FunLike F α β] : Prop where
  /-- Every element of `F` is a quasi-isometry. -/
  quasiIsometry : ∀ f : F, QuasiIsometry f

namespace QuasiIsometryClass

variable {F : Type*} [FunLike F α β]
variable [QuasiIsometryClass F α β]

/-- An element of a `QuasiIsometryClass` is a quasi-isometry. -/
theorem isQuasiIsometry (f : F) : QuasiIsometry f := QuasiIsometryClass.quasiIsometry f

end QuasiIsometryClass

/-! ## Bundled Equivalence: `QuasiIsometryEquiv` -/

/-- A quasi-isometry equivalence between two metric spaces.

This is a bundled quasi-isometry with an explicit quasi-inverse, such that:
- Both `toFun` and `invFun` are quasi-isometries
- `invFun ∘ toFun` is close to the identity on `α` (i.e., `dist x (invFun (toFun x))` is bounded)
- `toFun ∘ invFun` is close to the identity on `β` (i.e., `dist y (toFun (invFun y))` is bounded)

Two spaces are **quasi-isometric** if there exists a `QuasiIsometryEquiv` between them.
This is the fundamental equivalence relation in geometric group theory and coarse geometry. -/
structure QuasiIsometryEquiv (α β : Type*) [PseudoMetricSpace α] [PseudoMetricSpace β] where
  /-- The forward map of the quasi-isometry equivalence. -/
  toFun : α → β
  /-- The inverse map of the quasi-isometry equivalence. -/
  invFun : β → α
  /-- The forward map is a quasi-isometry. -/
  quasiIsometry_toFun : QuasiIsometry toFun
  /-- The inverse map is a quasi-isometry. -/
  quasiIsometry_invFun : QuasiIsometry invFun
  /-- The composition `invFun ∘ toFun` is close to the identity. -/
  left_inv_close : ∃ C : ℝ≥0, ∀ x, dist x (invFun (toFun x)) ≤ C
  /-- The composition `toFun ∘ invFun` is close to the identity. -/
  right_inv_close : ∃ C : ℝ≥0, ∀ y, dist y (toFun (invFun y)) ≤ C

/-- Notation for quasi-isometry equivalences. -/
infixl:25 " ≃qi " => QuasiIsometryEquiv

namespace QuasiIsometryEquiv

/-! ### Coercion and extensionality -/
section CoeFun

instance instCoeFun : CoeFun (α ≃qi β) (fun _ => α → β) where
  coe := QuasiIsometryEquiv.toFun

@[simp]
theorem coe_toFun (e : α ≃qi β) : e.toFun = e := rfl

@[simp]
theorem coe_mk (f g hf hg hleft hright) :
    (⟨f, g, hf, hg, hleft, hright⟩ : α ≃qi β) = f := rfl

/-- Two `QuasiIsometryEquiv`s are equal if their forward and inverse functions are equal. -/
@[ext]
theorem ext {e₁ e₂ : α ≃qi β} (hfwd : ∀ x, e₁ x = e₂ x)
    (hinv : ∀ y, e₁.invFun y = e₂.invFun y) : e₁ = e₂ := by
  cases e₁; cases e₂
  congr 1
  · exact funext hfwd
  · exact funext hinv

end CoeFun

/-! ### Basic properties -/
section Basic

/-- The forward map of a `QuasiIsometryEquiv` is a quasi-isometry. -/
theorem quasiIsometry (e : α ≃qi β) : QuasiIsometry e := e.quasiIsometry_toFun

/-- The inverse map of a `QuasiIsometryEquiv` is a quasi-isometry. -/
theorem quasiIsometry_symm (e : α ≃qi β) : QuasiIsometry e.invFun := e.quasiIsometry_invFun

end Basic

/-! ### Refl, symm, and trans -/
section ReflSymmTrans

/-- The identity quasi-isometry equivalence.

This shows that quasi-isometry equivalence is reflexive. -/
@[refl, simps]
def refl (α : Type*) [PseudoMetricSpace α] : α ≃qi α where
  toFun := id
  invFun := id
  quasiIsometry_toFun := QuasiIsometry.id
  quasiIsometry_invFun := QuasiIsometry.id
  left_inv_close := ⟨0, fun _ => by simp⟩
  right_inv_close := ⟨0, fun _ => by simp⟩

/-- The inverse of a quasi-isometry equivalence.

This shows that quasi-isometry equivalence is symmetric. -/
@[symm, simps]
def symm (e : α ≃qi β) : β ≃qi α where
  toFun := e.invFun
  invFun := e.toFun
  quasiIsometry_toFun := e.quasiIsometry_invFun
  quasiIsometry_invFun := e.quasiIsometry_toFun
  left_inv_close := e.right_inv_close
  right_inv_close := e.left_inv_close

/-- Taking the inverse twice returns the original equivalence. -/
@[simp]
theorem symm_symm (e : α ≃qi β) : e.symm.symm = e := rfl

/-- `symm` is a bijection on `QuasiIsometryEquiv`. -/
theorem symm_bijective : Function.Bijective (symm : (α ≃qi β) → (β ≃qi α)) :=
  ⟨fun e₁ e₂ h => by simpa only [symm_symm] using congrArg symm h,
   fun e => ⟨e.symm, symm_symm e⟩⟩

/-- The coercion of `e.symm` is `e.invFun`. -/
theorem coe_symm (e : α ≃qi β) : (e.symm : β → α) = e.invFun := rfl

/-- Composition of quasi-isometry equivalences.

This shows that quasi-isometry equivalence is transitive. -/
@[trans, simps]
def trans (e₁ : α ≃qi β) (e₂ : β ≃qi γ) : α ≃qi γ where
  toFun := e₂ ∘ e₁
  invFun := e₁.invFun ∘ e₂.invFun
  quasiIsometry_toFun := e₂.quasiIsometry.comp e₁.quasiIsometry
  quasiIsometry_invFun := e₁.quasiIsometry_invFun.comp e₂.quasiIsometry_invFun
  left_inv_close := by
    obtain ⟨C₁, hC₁⟩ := e₁.left_inv_close
    obtain ⟨C₂, hC₂⟩ := e₂.left_inv_close
    obtain ⟨A, B, _, hAB⟩ := e₁.quasiIsometry_invFun
    refine ⟨C₁ + A * C₂ + B, fun x => ?_⟩
    calc dist x (e₁.invFun (e₂.invFun (e₂ (e₁ x))))
        ≤ dist x (e₁.invFun (e₁ x)) +
          dist (e₁.invFun (e₁ x)) (e₁.invFun (e₂.invFun (e₂ (e₁ x)))) :=
          dist_triangle _ _ _
      _ ≤ C₁ + (A * dist (e₁ x) (e₂.invFun (e₂ (e₁ x))) + B) := by
          gcongr
          · exact hC₁ x
          · exact hAB.dist_upper _ _
      _ ≤ C₁ + (A * C₂ + B) := by gcongr; exact hC₂ (e₁ x)
      _ = C₁ + A * C₂ + B := by ring
  right_inv_close := by
    obtain ⟨C₁, hC₁⟩ := e₁.right_inv_close
    obtain ⟨C₂, hC₂⟩ := e₂.right_inv_close
    obtain ⟨A, B, _, hAB⟩ := e₂.quasiIsometry_toFun
    refine ⟨C₂ + A * C₁ + B, fun z => ?_⟩
    calc dist z (e₂ (e₁ (e₁.invFun (e₂.invFun z))))
        ≤ dist z (e₂ (e₂.invFun z)) +
          dist (e₂ (e₂.invFun z)) (e₂ (e₁ (e₁.invFun (e₂.invFun z)))) :=
          dist_triangle _ _ _
      _ ≤ C₂ + (A * dist (e₂.invFun z) (e₁ (e₁.invFun (e₂.invFun z))) + B) := by
          gcongr
          · exact hC₂ z
          · exact hAB.dist_upper _ _
      _ ≤ C₂ + (A * C₁ + B) := by gcongr; exact hC₁ (e₂.invFun z)
      _ = C₂ + A * C₁ + B := by ring

/-- Applying a composition is the same as applying each map in sequence. -/
@[simp]
theorem trans_apply (e₁ : α ≃qi β) (e₂ : β ≃qi γ) (x : α) :
    (e₁.trans e₂) x = e₂ (e₁ x) := rfl

/-- The inverse of a composition is the composition of inverses in reverse order. -/
theorem symm_trans (e₁ : α ≃qi β) (e₂ : β ≃qi γ) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm := rfl

/-- Applying the inverse of a composition. -/
theorem symm_trans_apply (e₁ : α ≃qi β) (e₂ : β ≃qi γ) (z : γ) :
    (e₁.trans e₂).symm z = e₁.symm (e₂.symm z) := rfl

end ReflSymmTrans

/-! ### Closeness bounds -/
section Closeness

/-- `e ∘ e.symm` is close to the identity: the distance from `y` to `e (e.symm y)` is bounded. -/
theorem apply_symm_apply_dist_le (e : α ≃qi β) :
    ∃ C : ℝ≥0, ∀ y, dist y (e (e.symm y)) ≤ C :=
  e.right_inv_close

/-- `e.symm ∘ e` is close to the identity: the distance from `x` to `e.symm (e x)` is bounded. -/
theorem symm_apply_apply_dist_le (e : α ≃qi β) :
    ∃ C : ℝ≥0, ∀ x, dist x (e.symm (e x)) ≤ C :=
  e.left_inv_close

/-- `e ∘ e.symm` is close to the identity (using `nndist`). -/
theorem apply_symm_apply_nndist_le (e : α ≃qi β) :
    ∃ C : ℝ≥0, ∀ y, nndist y (e (e.symm y)) ≤ C := by
  obtain ⟨C, hC⟩ := e.apply_symm_apply_dist_le
  exact ⟨C, fun y => by simpa only [← coe_nndist, NNReal.coe_le_coe] using hC y⟩

/-- `e.symm ∘ e` is close to the identity (using `nndist`). -/
theorem symm_apply_apply_nndist_le (e : α ≃qi β) :
    ∃ C : ℝ≥0, ∀ x, nndist x (e.symm (e x)) ≤ C := by
  obtain ⟨C, hC⟩ := e.symm_apply_apply_dist_le
  exact ⟨C, fun x => by simpa only [← coe_nndist, NNReal.coe_le_coe] using hC x⟩

end Closeness

/-! ### Diameter bounds -/
section Diameter

/-- The image of a set under a `QuasiIsometryEquiv` has controlled diameter. -/
theorem diam_image_le (e : α ≃qi β) (s : Set α) :
    ∃ A B : ℝ≥0, Metric.diam (e '' s) ≤ A * Metric.diam s + B :=
  e.quasiIsometry.diam_image_le_exists s

/-- The range of a `QuasiIsometryEquiv` has controlled diameter. -/
theorem diam_range_le (e : α ≃qi β) :
    ∃ A B : ℝ≥0, Metric.diam (Set.range e) ≤ A * Metric.diam (Set.univ : Set α) + B :=
  e.quasiIsometry.diam_range_le_exists

end Diameter

/-! ### Ball mappings -/
section Ball

/-- A `QuasiIsometryEquiv` maps open balls into open balls of controlled radius. -/
theorem mapsTo_ball (e : α ≃qi β) (x : α) (r : ℝ≥0) :
    ∃ A B : ℝ≥0, Set.MapsTo e (Metric.ball x r) (Metric.ball (e x) (A * r + B)) := by
  obtain ⟨A, B, _, hAB⟩ := e.quasiIsometry
  exact ⟨A, B, hAB.mapsTo_ball x r⟩

/-- A `QuasiIsometryEquiv` maps closed balls into closed balls of controlled radius. -/
theorem mapsTo_closedBall (e : α ≃qi β) (x : α) (r : ℝ≥0) :
    ∃ A B : ℝ≥0, Set.MapsTo e (Metric.closedBall x r) (Metric.closedBall (e x) (A * r + B)) := by
  obtain ⟨A, B, _, hAB⟩ := e.quasiIsometry
  exact ⟨A, B, hAB.mapsTo_closedBall x r⟩

end Ball

/-! ### Constructing from isometries -/
section FromIsometry

/-- An isometry equivalence is a quasi-isometry equivalence.

Isometries are the "trivial" case of quasi-isometries with `A = 1` and `B = C = 0`. -/
def ofIsometryEquiv (e : α ≃ᵢ β) : α ≃qi β where
  toFun := e
  invFun := e.symm
  quasiIsometry_toFun := QuasiIsometry.of_isometry e.isometry e.surjective
  quasiIsometry_invFun := QuasiIsometry.of_isometry e.symm.isometry e.symm.surjective
  left_inv_close := ⟨0, fun x => by simp [e.symm_apply_apply]⟩
  right_inv_close := ⟨0, fun y => by simp [e.apply_symm_apply]⟩

/-- The coercion of `ofIsometryEquiv e` is just `e`. -/
@[simp]
theorem coe_ofIsometryEquiv (e : α ≃ᵢ β) : (ofIsometryEquiv e : α → β) = e := rfl

/-- The inverse of `ofIsometryEquiv e` is `ofIsometryEquiv e.symm`. -/
@[simp]
theorem ofIsometryEquiv_symm (e : α ≃ᵢ β) : (ofIsometryEquiv e).symm = ofIsometryEquiv e.symm :=
  rfl

end FromIsometry

/-! ### Standard constructions -/
section Constructions

/-- Product commutativity as a quasi-isometry equivalence.

Swapping the factors of a product is a quasi-isometry (in fact, an isometry). -/
def prodComm : α × β ≃qi β × α where
  toFun := Prod.swap
  invFun := Prod.swap
  quasiIsometry_toFun := by
    apply QuasiIsometry.of_isometry
    · exact Isometry.of_dist_eq fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ => by
        simp only [Prod.swap, Prod.dist_eq, max_comm]
    · exact Prod.swap_surjective
  quasiIsometry_invFun := by
    apply QuasiIsometry.of_isometry
    · exact Isometry.of_dist_eq fun ⟨y₁, x₁⟩ ⟨y₂, x₂⟩ => by
        simp only [Prod.swap, Prod.dist_eq, max_comm]
    · exact Prod.swap_surjective
  left_inv_close := ⟨0, fun _ => by simp [Prod.swap_swap]⟩
  right_inv_close := ⟨0, fun _ => by simp [Prod.swap_swap]⟩

/-- Product associativity as a quasi-isometry equivalence.

Reassociating nested products is a quasi-isometry (in fact, an isometry). -/
def prodAssoc : (α × β) × γ ≃qi α × (β × γ) where
  toFun := fun ((x, y), z) => (x, (y, z))
  invFun := fun (x, (y, z)) => ((x, y), z)
  quasiIsometry_toFun := by
    apply QuasiIsometry.of_isometry
    · exact Isometry.of_dist_eq fun ⟨⟨x₁, y₁⟩, z₁⟩ ⟨⟨x₂, y₂⟩, z₂⟩ => by
        simp only [Prod.dist_eq, max_assoc]
    · exact fun ⟨x, y, z⟩ => ⟨⟨⟨x, y⟩, z⟩, rfl⟩
  quasiIsometry_invFun := by
    apply QuasiIsometry.of_isometry
    · exact Isometry.of_dist_eq fun ⟨x₁, y₁, z₁⟩ ⟨x₂, y₂, z₂⟩ => by
        simp only [Prod.dist_eq, max_assoc]
    · exact fun ⟨⟨x, y⟩, z⟩ => ⟨⟨x, y, z⟩, rfl⟩
  left_inv_close := ⟨0, fun _ => by simp⟩
  right_inv_close := ⟨0, fun _ => by simp⟩

end Constructions

/-! ### Simp projections -/
section Simps

/-- See Note [custom simps projection] -/
def Simps.apply (e : α ≃qi β) : α → β := e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : α ≃qi β) : β → α := e.symm

end Simps

end QuasiIsometryEquiv
