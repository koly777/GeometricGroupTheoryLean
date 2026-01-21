/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import CoarseSpace.Basic
/-!
# Coarse equivalences

This file defines **coarse equivalences** between coarse spaces, in the sense of Roe.

A `CoarseEquiv X Y` is given by maps `f : X → Y` and `g : Y → X` such that

* both `f` and `g` are coarse maps (`IsCoarse`), and
* `f ∘ g` and `g ∘ f` are *close* to the respective identity maps.

We write `X ≃ᶜ Y` for the type of coarse equivalences.

This is the coarse analogue of an isometry, hence we do **not** require
`f` and `g` to be strict inverses or even bijections; they are only inverses up to
coarse closeness.

## References

* J. Roe, *Lectures on Coarse Geometry*, University Lecture Series 31, AMS, 2003
-/

open Set Function CoarseSpace Prod Entourage

open scoped Entourage

variable {X Y Z W : Type*}

/-- Coarse equivalence between `X` and `Y`.

A `CoarseEquiv X Y` consists of a coarse map `toFun : X → Y` and a coarse map
`invFun : Y → X` such that both compositions are close to the identity. -/
structure CoarseEquiv (X : Type*) (Y : Type*) [CoarseSpace X] [CoarseSpace Y] where
  /-- Forward map of a coarse equivalence. -/
  toFun : X → Y
  /-- Backward (quasi-inverse) map of a coarse equivalence. -/
  invFun : Y → X
  /-- The forward map is a coarse map. -/
  coarse_toFun : Coarse toFun := by fun_prop
  /-- The backward map is a coarse map. -/
  coarse_invFun : Coarse invFun := by fun_prop
  /-- `toFun ∘ invFun` is close to the identity on `Y`. -/
  isClose_id_right : toFun ∘ invFun =ᶜ id
  /-- `invFun ∘ toFun` is close to the identity on `X`. -/
  isClose_id_left : invFun ∘ toFun =ᶜ id

@[inherit_doc]
infixl:25 " ≃ᶜ " => CoarseEquiv

namespace CoarseEquiv

variable [CoarseSpace X] [CoarseSpace Y] [CoarseSpace Z] [CoarseSpace W]

/-- The forward map of a coarse equivalence is a coarse map. -/
@[fun_prop]
protected theorem coarse (h : X ≃ᶜ Y) : Coarse h.toFun :=
  h.coarse_toFun

/-! ### Coercion to function -/

/-- Coerce a coarse equivalence to its forward map. -/
instance : CoeFun (X ≃ᶜ Y) (fun _ ↦ X → Y) :=
  ⟨fun e ↦ e.toFun⟩

/-- The coercion of a `CoarseEquiv` constructed with `mk` is the forward function. -/
@[simp]
theorem mk_coe (f : X → Y) (g h₁ h₂ hL hR) :
    (CoarseEquiv.mk f g h₁ h₂ hL hR : X → Y) = f :=
  rfl

/-- The coercion of `e.toFun` equals the coercion of `e`. -/
@[simp]
theorem coe_toFun (e : X ≃ᶜ Y) : (e.toFun : X → Y) = e :=
  rfl

/-- Two coarse equivalences are equal if their forward and inverse maps agree pointwise. -/
@[ext]
theorem ext {e₁ e₂ : X ≃ᶜ Y} (h : ∀ x, e₁ x = e₂ x) (h' : ∀ y, e₁.invFun y = e₂.invFun y) :
    e₁ = e₂ := by
  cases e₁; cases e₂; simp only [mk.injEq]; exact ⟨funext h, funext h'⟩

/-! ### Identity, symmetry, and composition -/

/-- Identity coarse equivalence. -/
@[simps! -fullyApplied toFun invFun]
protected def refl (X : Type*) [CoarseSpace X] : X ≃ᶜ X where
  toFun := id
  invFun := id
  isClose_id_left := isClose_id_comp _
  isClose_id_right := isClose_comp_id _

/-- Inverse coarse equivalence. -/
@[symm]
protected def symm (h : X ≃ᶜ Y) : Y ≃ᶜ X where
  toFun := h.invFun
  invFun := h.toFun
  coarse_toFun := h.coarse_invFun
  coarse_invFun := h.coarse_toFun
  isClose_id_left := h.isClose_id_right
  isClose_id_right := h.isClose_id_left

/-- The backward map of a coarse equivalence is a coarse map. -/
@[fun_prop]
protected theorem coarse_symm (h : X ≃ᶜ Y) : Coarse h.symm.toFun :=
  h.coarse_invFun

/-- The coercion of `e.invFun` equals the coercion of `e.symm`. -/
@[simp]
theorem coe_invFun (e : X ≃ᶜ Y) : (e.invFun : Y → X) = e.symm :=
  rfl

/-- The forward map of `h.symm` is `h.invFun`. -/
@[simp]
theorem symm_toFun (h : X ≃ᶜ Y) : h.symm.toFun = h.invFun :=
  rfl

/-- The inverse map of `h.symm` is `h.toFun`. -/
@[simp]
theorem symm_invFun (h : X ≃ᶜ Y) : h.symm.invFun = h.toFun :=
  rfl

/-- The double inverse of a coarse equivalence is itself. -/
@[simp]
theorem symm_symm (h : X ≃ᶜ Y) : h.symm.symm = h := by
  cases h; rfl

/-- Composition of coarse equivalences. -/
@[trans]
protected def trans (h₁ : X ≃ᶜ Y) (h₂ : Y ≃ᶜ Z) : X ≃ᶜ Z where
  toFun := h₂.toFun ∘ h₁.toFun
  invFun := h₁.invFun ∘ h₂.invFun
  isClose_id_right :=
    ((h₁.isClose_id_right.comp_left h₂.coarse.controlled).trans
    <| isClose_comp_id _).comp h₂.invFun |>.trans h₂.isClose_id_right
  isClose_id_left :=
    ((h₂.isClose_id_left.comp_left h₁.coarse_invFun.controlled).trans
    <| isClose_comp_id _).comp h₁ |>.trans h₁.isClose_id_left

/-- The composition of coarse equivalences applied to `x`. -/
@[simp]
theorem trans_apply (h₁ : X ≃ᶜ Y) (h₂ : Y ≃ᶜ Z) (x : X) :
    (h₁.trans h₂) x = h₂ (h₁ x) :=
  rfl

/-- The inverse of a composition applied to `z`. -/
@[simp]
theorem symm_trans_apply (h₁ : X ≃ᶜ Y) (h₂ : Y ≃ᶜ Z) (z : Z) :
    (h₁.trans h₂).symm z = h₁.symm (h₂.symm z) :=
  rfl

/-- The inverse of the identity equivalence is itself. -/
@[simp]
theorem refl_symm : (CoarseEquiv.refl X).symm = CoarseEquiv.refl X :=
  rfl

/-- Composing an equivalence with its inverse is close to the identity. -/
@[simp]
theorem self_trans_symm_toFun (h : X ≃ᶜ Y) :
  (h.trans h.symm).toFun =ᶜ (CoarseEquiv.refl X).toFun := by
  simp only [CoarseEquiv.trans, CoarseEquiv.symm, CoarseEquiv.refl]
  exact h.isClose_id_left

/-- Composing the inverse with the equivalence is close to the identity. -/
@[simp]
theorem symm_trans_self_toFun (h : X ≃ᶜ Y) :
  (h.symm.trans h).toFun =ᶜ (CoarseEquiv.refl Y).toFun := by
  simp only [CoarseEquiv.trans, CoarseEquiv.symm, CoarseEquiv.refl]
  exact h.isClose_id_right

/-- The inverse of a composition is the composition of inverses in reverse order. -/
@[simp]
theorem symm_trans (e₁ : X ≃ᶜ Y) (e₂ : Y ≃ᶜ Z) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm := rfl

/-- Composition of coarse equivalences is associative. -/
theorem trans_assoc (e₁ : X ≃ᶜ Y) (e₂ : Y ≃ᶜ Z) (e₃ : Z ≃ᶜ W) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) := rfl

/-- Composing the identity on the left is the identity. -/
@[simp]
theorem refl_trans (e : X ≃ᶜ Y) : (CoarseEquiv.refl X).trans e = e := by
  cases e; rfl

/-- Composing the identity on the right is the identity. -/
@[simp]
theorem trans_refl (e : X ≃ᶜ Y) : e.trans (CoarseEquiv.refl Y) = e := by
  cases e; rfl

/-- A coarse equivalence pulls back controlled sets to controlled sets. -/
theorem isControlled_comap (e : X ≃ᶜ Y)
    {E : Entourage Y} (hE : IsControlled E) : IsControlled (E.comap e) := by
  -- The closeness relation as an entourage: {(x, g(f(x))) | x}
  let R : Entourage X := range fun x ↦ (x, e.invFun (e x))
  have hR : IsControlled R := e.isClose_id_left.symm
  -- E.comap e ⊆ R ○ (E.map e.invFun) ○ R.inv
  have hsub : E.comap e ⊆ R.comp ((E.map e.invFun).comp R.inv) := by
    intro ⟨a, b⟩ hab
    refine ⟨e.invFun (e a), ⟨a, rfl⟩, e.invFun (e b), ?_, ⟨b, rfl⟩⟩
    exact ⟨⟨e a, e b⟩, hab, rfl⟩
  exact (hR.comp ((e.coarse_invFun.controlled hE).comp hR.inv)).subset hsub

/-! ### Coarse maps and closeness -/

/-- Conjugation by a coarse equivalence preserves closeness of self-maps. -/
theorem isClose_conj {f g : X → X} (h : X ≃ᶜ Y) (hfg : f =ᶜ g) :
    (h.toFun ∘ f ∘ h.invFun) =ᶜ (h.toFun ∘ g ∘ h.invFun) :=
   (IsClose.comp _ hfg).comp_left h.coarse_toFun.controlled

/-- Construct a coarse equivalence from a coarse map with a left inverse, given that
the comap of controlled sets is controlled. -/
@[simps toFun invFun]
noncomputable
def mkOfLeftInverse (f : X → Y) (g : Y → X) (hfg : Function.LeftInverse f g) (hf : Coarse f)
  (hf_comap : ∀ E, IsControlled E → IsControlled (E.comap f)) : CoarseEquiv X Y where
  toFun := f
  invFun := g
  coarse_invFun :=
    ⟨controlled_of_leftInverse hfg hf_comap,
    coarselyProper_of_leftInverse hfg hf.controlled⟩
  isClose_id_right := CoarseSpace.isClose_of_eq (RightInverse.id hfg)
  isClose_id_left := isClose_id_of_leftInverse hfg hf_comap

/-- Construct a coarse equivalence from a surjective coarse map, given that
the comap of controlled sets is controlled. Uses choice to pick a right inverse. -/
@[simps! toFun invFun]
noncomputable
def mkOfSurjective (f : X → Y) (hf_surj : Function.Surjective f) (hf : Coarse f)
    (hf_comap : ∀ E, IsControlled E → IsControlled (E.comap f)) : CoarseEquiv X Y :=
  mkOfLeftInverse f (Classical.choose hf_surj.hasRightInverse)
    (Classical.choose_spec hf_surj.hasRightInverse) hf hf_comap

/-- Construct a coarse equivalence from an equivalence of types where both directions
are coarse maps. -/
@[simps toFun invFun]
def ofEquiv (e : X ≃ Y) (hf : Coarse e := by fun_prop)
    (hg : Coarse e.symm := by fun_prop) : X ≃ᶜ Y where
  toFun := e
  invFun := e.symm
  isClose_id_right := isClose_of_eq (funext e.right_inv)
  isClose_id_left := isClose_of_eq (funext e.left_inv)

end CoarseEquiv

variable [CoarseSpace X] [CoarseSpace Y] [CoarseSpace Z] {f : X → Y}

structure IsCoarseEquiv (f : X → Y) : Prop where
  coarse : Coarse f
  exists_inv : ∃ (g : Y → X), Coarse g ∧ f ∘ g =ᶜ id ∧ g ∘ f =ᶜ id

protected theorem CoarseEquiv.IsCoarseEquiv (e : X ≃ᶜ Y) : IsCoarseEquiv e :=
  ⟨e.coarse_toFun, ⟨e.symm,
  ⟨CoarseEquiv.coarse_symm e, e.isClose_id_right, e.isClose_id_left⟩⟩⟩

namespace IsCoarseEquiv

protected lemma id : IsCoarseEquiv (@id X) := (CoarseEquiv.IsCoarseEquiv (CoarseEquiv.refl X))

protected noncomputable def toCoarseEquiv (hf : IsCoarseEquiv f) : X ≃ᶜ Y where
  toFun := f
  invFun := hf.exists_inv.choose
  coarse_toFun := hf.coarse
  coarse_invFun := (hf.exists_inv.choose_spec).1
  isClose_id_right := (hf.exists_inv.choose_spec).2.1
  isClose_id_left := (hf.exists_inv.choose_spec).2.2

lemma comp {g : Y → Z} (hg : IsCoarseEquiv g) (hf : IsCoarseEquiv f) : IsCoarseEquiv (g ∘ f) :=
  let f' := hf.exists_inv.choose
  let g' := hg.exists_inv.choose
  let hf' := hf.exists_inv.choose_spec
  let hg' := hg.exists_inv.choose_spec
  ⟨hg.coarse.comp hf.coarse,
   ⟨f' ∘ g', hf'.1.comp hg'.1,
    ((hf'.2.1.comp_left hg.coarse.controlled ).trans
    <| isClose_comp_id _).comp g' |>.trans hg'.2.1,
    ((hg'.2.2.comp_left hf'.1.controlled).trans
    <| isClose_comp_id _).comp f |>.trans hf'.2.2⟩⟩

/-- A coarse equivalence pulls back controlled sets to controlled sets. -/
protected theorem isControlled_comap (hf : IsCoarseEquiv f)
    {E : Entourage Y} (hE : IsControlled E) : IsControlled (E.comap f) :=
  hf.toCoarseEquiv.isControlled_comap hE

omit [CoarseSpace Y]

/-- If `f : X → Y` is surjective and is a coarse equivalence with respect to
two coarse structures on `Y`, then those structures coincide. -/
theorem coarseSpace_eq_of_surjective_isCoarseEquiv
    {f : X → Y} (hf_surj : Function.Surjective f)
    (c₁ c₂ : CoarseSpace Y)
    (hf₁ : @IsCoarseEquiv X Y _ c₁ f)
    (hf₂ : @IsCoarseEquiv X Y _ c₂ f) :
    c₁ = c₂ :=
  CoarseSpace.ext <| Set.ext fun E ↦
    ⟨fun hE ↦ Entourage.map_comap_of_surjective hf_surj E ▸
        hf₂.coarse.controlled (@IsCoarseEquiv.isControlled_comap X Y _ c₁ f hf₁ E hE),
     fun hE ↦ Entourage.map_comap_of_surjective hf_surj E ▸
        letI : CoarseSpace Y := c₁
        hf₁.coarse.controlled (@IsCoarseEquiv.isControlled_comap X Y _ c₂ f hf₂ E hE)⟩

end IsCoarseEquiv
