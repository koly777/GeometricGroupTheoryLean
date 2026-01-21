/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import CoarseSpace.CoarseEquiv.Lemmas
import CoarseSpace.Metric.Basic
import CoarseSpace.QuasiIsometry

/-!
# Quasi-Isometries and Coarse Equivalences

This file establishes the bridge between metric and coarse geometry: quasi-isometries
induce coarse equivalences, and conversely, coarse equivalences between spaces with
coarse midpoints induce quasi-isometries.

## Main Results

* `QuasiIsometryWith.coarseMap`: A quasi-isometry is a coarse map.
* `QuasiIsometryEquiv.toCoarseEquiv`: A quasi-isometry equivalence induces a coarse equivalence.
* `CoarseEquiv.quasiIsometry`: A coarse equivalence between spaces with coarse midpoints
  is a quasi-isometry.
* `CoarseEquiv.toQuasiIsometryEquiv`: A coarse equivalence between spaces with coarse midpoints
  upgrades to a quasi-isometry equivalence.

## Implementation Notes

The two directions have different hypotheses:

* **QI → Coarse**: No additional assumptions. The linear distance bounds of a quasi-isometry
  immediately give controlledness and coarse properness.

* **Coarse → QI**: Requires `HasCoarseMidpoints` on both spaces. The upper bound (controlledness)
  is automatic, but the lower bound needs coarse midpoints to prevent distances from collapsing.
  Without this, a coarse equivalence could send distant points arbitrarily close together.

This is necessary: coarse equivalence is a weaker notion than quasi-isometry in general, but they
coincide for "nice" spaces (geodesic, length, or more generally, spaces with coarse midpoints).
-/

open Set Function CoarseSpace Entourage

open scoped NNReal

variable {X Y Z : Type*}
variable [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

namespace QuasiIsometryWith

variable {A B C : ℝ≥0} {f : X → Y}

/-- A quasi-isometry maps controlled entourages to controlled entourages.

If `E` is controlled with bound `r`, then `map f E` is controlled with bound `A * r + B`. -/
protected theorem controlled (hf : QuasiIsometryWith A B C f) : Controlled f := by
  intro E hE
  obtain ⟨r, hr⟩ := hE
  refine ⟨A * r + B, fun x y hxy => ?_⟩
  obtain ⟨⟨a, b⟩, hab, rfl, rfl⟩ := hxy
  rw [edist_nndist]
  refine ENNReal.coe_le_coe.mpr ?_
  calc nndist (f a) (f b)
      ≤ A * nndist a b + B := hf.nndist_upper a b
    _ ≤ A * r + B := by gcongr; exact edist_le_coe.mp (hr a b hab)

/-- A quasi-isometry is coarsely proper: preimages of coarsely bounded sets are bounded.

If `s` is bounded with pairs at distance at most `r`, then `f⁻¹(s)` has pairs at
distance at most `A * r + B`. -/
protected theorem coarselyProper (hf : QuasiIsometryWith A B C f) : CoarselyProper f := by
  intro s ⟨hs⟩
  obtain ⟨r, hr⟩ := hs
  refine ⟨⟨A * r + B, fun x y ⟨hx, hy⟩ => ?_⟩⟩
  rw [edist_nndist]
  refine ENNReal.coe_le_coe.mpr ?_
  calc nndist x y
      ≤ A * nndist (f x) (f y) + B := hf.nndist_lower x y
    _ ≤ A * r + B := by gcongr; exact edist_le_coe.mp <| hr (f x) (f y) ⟨hx, hy⟩

/-- A quasi-isometry is a coarse map. -/
protected theorem coarseMap (hf : QuasiIsometryWith A B C f) : Coarse f :=
  ⟨hf.controlled, hf.coarselyProper⟩

end QuasiIsometryWith

namespace QuasiIsometry

variable {f : X → Y}

/-- A quasi-isometry (existential form) is a controlled map. -/
protected theorem controlled (hf : QuasiIsometry f) : Controlled f := by
  obtain ⟨A, B, C, h⟩ := hf
  exact h.controlled

/-- A quasi-isometry (existential form) is coarsely proper. -/
protected theorem coarselyProper (hf : QuasiIsometry f) : CoarselyProper f := by
  obtain ⟨A, B, C, h⟩ := hf
  exact h.coarselyProper

/-- A quasi-isometry (existential form) is a coarse map. -/
protected theorem coarseMap (hf : QuasiIsometry f) : Coarse f :=
  ⟨hf.controlled, hf.coarselyProper⟩

end QuasiIsometry

namespace QuasiIsometryEquiv

variable (e : X ≃qi Y)

/-- The forward map of a quasi-isometry equivalence is a coarse map. -/
protected theorem coarse_toFun : Coarse e :=
  e.quasiIsometry.coarseMap

/-- The inverse map of a quasi-isometry equivalence is a coarse map. -/
protected theorem coarse_invFun : Coarse e.invFun :=
  e.quasiIsometry_invFun.coarseMap

/-- The composition `e.symm ∘ e` is close to the identity. -/
protected theorem isClose_symm_comp_self : e.symm ∘ e =ᶜ id := by
  obtain ⟨C, hC⟩ := e.left_inv_close
  refine ⟨C, fun x y hxy => ?_⟩
  obtain ⟨a, rfl, rfl⟩ := hxy
  rw [edist_nndist]
  refine ENNReal.coe_le_coe.mpr ?_
  exact nndist_comm _ (id a) ▸ hC a

/-- The composition `e ∘ e.symm` is close to the identity. -/
protected theorem isClose_self_comp_symm : e ∘ e.symm =ᶜ id := by
  obtain ⟨C, hC⟩ := e.right_inv_close
  refine ⟨C, fun x y hxy => ?_⟩
  obtain ⟨a, rfl, rfl⟩ := hxy
  rw [edist_nndist]
  refine ENNReal.coe_le_coe.mpr ?_
  exact nndist_comm _ (id a) ▸ hC a

/-- A quasi-isometry equivalence induces a coarse equivalence.

This is the bridge from metric to coarse geometry:
quasi-isometric metric spaces are coarsely equivalent. -/
protected def toCoarseEquiv : X ≃ᶜ Y where
  toFun := e
  invFun := e.symm
  coarse_toFun := e.coarse_toFun
  coarse_invFun := e.coarse_invFun
  isClose_id_right := e.isClose_self_comp_symm
  isClose_id_left := e.isClose_symm_comp_self

@[simp]
theorem toCoarseEquiv_apply (x : X) : e.toCoarseEquiv x = e x := rfl

@[simp]
theorem toCoarseEquiv_symm_apply (y : Y) : e.toCoarseEquiv.symm y = e.symm y := rfl

/-- The coarse equivalence of a composition of quasi-isometries is the composition
of coarse equivalences of quasi-isometries. -/
theorem toCoarseEquiv_trans (e₁ : X ≃qi Y) (e₂ : Y ≃qi Z) :
    (e₁.trans e₂).toCoarseEquiv = e₁.toCoarseEquiv.trans e₂.toCoarseEquiv := rfl

/-- The coarse equivalence of the identity quasi-isometry is the identity coarse equivalence. -/
theorem toCoarseEquiv_refl :
    (QuasiIsometryEquiv.refl X).toCoarseEquiv = CoarseEquiv.refl X := rfl

/-- The coarse equivalence of the inverse of a quasi-isometry is the inverse
of the coarse equivalence. -/
theorem toCoarseEquiv_symm : e.symm.toCoarseEquiv = e.toCoarseEquiv.symm := rfl

end QuasiIsometryEquiv

namespace CoarseEquiv

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable [HasCoarseMidpoints X] [HasCoarseMidpoints Y]

/-- A coarse equivalence between pseudo-metric spaces with coarse midpoints is a quasi-isometry. -/
protected theorem quasiIsometry (e : X ≃ᶜ Y) : QuasiIsometry e := by
  obtain ⟨A₁, B₁, hA₁, hUpper⟩ := Controlled.exists_dist_upper e.coarse_toFun.controlled
  obtain ⟨A₂, B₂, hA₂, hLower⟩ := e.exists_dist_lower
  obtain ⟨C, hSurj⟩ := e.exists_coarsely_surj
  let A := max A₁ A₂
  let B := max B₁ B₂
  refine ⟨A, B, C, ?_, ?_, ?_, ?_⟩
  · exact le_max_of_le_left hA₁
  · intro x y
    calc dist (e x) (e y)
        = (nndist (e x) (e y) : ℝ) := dist_nndist _ _
      _ ≤ A₁ * nndist x y + B₁ := mod_cast hUpper x y
      _ ≤ A * nndist x y + B := by gcongr; exacts [le_max_left .., le_max_left ..]
      _ = A * dist x y + B := by rw [dist_nndist]
  · intro x y
    calc dist x y
        = (nndist x y : ℝ) := dist_nndist _ _
      _ ≤ A₂ * nndist (e x) (e y) + B₂ := mod_cast hLower x y
      _ ≤ A * nndist (e x) (e y) + B := by gcongr; exacts [le_max_right .., le_max_right ..]
      _ = A * dist (e x) (e y) + B := by rw [dist_nndist]
  · intro y
    obtain ⟨x, hx⟩ := hSurj y
    exact ⟨x, mod_cast hx⟩

/-- Convert a coarse equivalence to a quasi-isometry equivalence.

This is the bridge from coarse to metric geometry: a coarse equivalence between
pseudo-metric spaces with coarse midpoints upgrades to a quasi-isometry equivalence.
The inverse is also a quasi-isometry (by symmetry of coarse equivalence), and the
closeness conditions provide the quasi-inverse bounds. -/
protected noncomputable def toQuasiIsometryEquiv (e : X ≃ᶜ Y) : X ≃qi Y where
  toFun := e
  invFun := e.symm
  quasiIsometry_toFun := e.quasiIsometry
  quasiIsometry_invFun := e.symm.quasiIsometry
  left_inv_close :=
    let ⟨R, hR⟩ := IsClose.nndist_le e.isClose_id_left
    ⟨R, fun x => mod_cast nndist_comm (α := X) .. ▸ hR x⟩
  right_inv_close :=
    let ⟨R, hR⟩ := IsClose.nndist_le e.isClose_id_right
    ⟨R, fun y => mod_cast nndist_comm (α := Y) .. ▸ hR y⟩

end CoarseEquiv

namespace CoarseEquiv

end CoarseEquiv
