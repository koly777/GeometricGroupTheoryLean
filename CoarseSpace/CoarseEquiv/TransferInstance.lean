/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import Mathlib.Logic.Equiv.Set

import CoarseSpace.CoarseEquiv.Defs
import CoarseSpace.Constructions

/-!
# Transfer coarse structure across `Equiv`s

We show how to transport a coarse space structure across an `Equiv` and prove that this
makes the equivalence a coarse equivalence between the original space and the
transported coarse space.
-/

variable {X Y : Type*}

namespace Equiv

/-- Transfer a `CoarseSpace` across an `Equiv`. -/
protected abbrev coarseSpace [CoarseSpace Y] (e : X ≃ Y) : CoarseSpace X :=
  .induced e ‹_›

/-- An equivalence `e : X ≃ Y` gives a coarse equivalence `X ≃ᶜ Y` where the coarse space structure
on `X` is the one obtained by transporting the coarse space structure on `Y` back along `e`. -/
def coarseEquiv [CoarseSpace Y] (e : X ≃ Y) : letI := e.coarseSpace; X ≃ᶜ Y:=
  letI := e.coarseSpace
  { e with
  coarse_toFun :=
  ⟨fun hE ↦ hE,
   fun {s} hs ↦ (isCoarselyBounded_induced_iff e _).mpr
     (hs.subset (Set.image_preimage_subset e s))⟩,
    coarse_invFun := ⟨
      fun {E} hE ↦ (isControlled_induced_iff _ _).mpr
      ((Entourage.map_comp _ _ E).symm ▸
      invFun_as_coe e ▸ self_comp_symm e ▸ Entourage.map_id _ ▸ hE),
      fun {s} hs ↦ Equiv.image_eq_preimage_symm e s ▸
        (isCoarselyBounded_induced_iff e s).mp hs,⟩,
    isClose_id_right := toFun_as_coe e ▸ invFun_as_coe e ▸
      self_comp_symm e ▸ CoarseSpace.IsClose.refl _,
    isClose_id_left :=  invFun_as_coe e ▸ toFun_as_coe e ▸
      self_comp_symm _ ▸ CoarseSpace.IsClose.refl _ }

end Equiv
