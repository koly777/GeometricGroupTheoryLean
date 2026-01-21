/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/

import Mathlib.Topology.MetricSpace.Basic

/-!
# Approximate Midpoints

This file defines approximate midpoints and the `HasCoarseMidpoints` typeclass.

* `IsApproximateMidpoint x m y ε`: `m` lies within `ε` of the midpoint between `x` and `y`.
* `HasCoarseMidpoints X`: every pair of points admits an `ε`-approximate midpoint for some
  uniform `ε`.
-/

open scoped Topology NNReal

variable {X : Type*} [PseudoMetricSpace X]

/-- An approximate midpoint between `x` and `y` with error `ε`. -/
def IsApproximateMidpoint (x m y : X) (ε : ℝ) : Prop :=
  max (dist x m) (dist m y) ≤ dist x y / 2 + ε

/-- A pseudo-metric space has coarse midpoints if there exists a uniform constant `ε` such that
every pair of points admits an `ε`-approximate midpoint. -/
class HasCoarseMidpoints (X : Type*) [PseudoMetricSpace X] where
  has_coarse_midpoints : ∃ ε : ℝ≥0, ∀ x y : X, ∃ m : X, IsApproximateMidpoint x m y ε

export HasCoarseMidpoints (has_coarse_midpoints)

namespace IsApproximateMidpoint

variable {x m y : X} {ε δ : ℝ}

theorem dist_left (h : IsApproximateMidpoint x m y ε) : dist x m ≤ dist x y / 2 + ε :=
  le_trans (le_max_left _ _) h

theorem dist_right (h : IsApproximateMidpoint x m y ε) : dist m y ≤ dist x y / 2 + ε :=
  le_trans (le_max_right _ _) h

@[symm]
theorem symm (h : IsApproximateMidpoint x m y ε) : IsApproximateMidpoint y m x ε:= by
  simp only [IsApproximateMidpoint, dist_comm] at h ⊢
  rwa [max_comm]

@[mono]
theorem mono (h : IsApproximateMidpoint x m y ε) (hle : ε ≤ δ) :
  IsApproximateMidpoint x m y δ :=
  h.trans (add_le_add_right hle _)

theorem of_dist_le_half (hε : 0 ≤ ε) (hx : dist x m ≤ dist x y / 2) (hy : dist m y ≤ dist x y / 2) :
    IsApproximateMidpoint x m y ε :=
  max_le (hx.trans (le_add_of_nonneg_right hε))
         (hy.trans (le_add_of_nonneg_right hε))

end IsApproximateMidpoint
