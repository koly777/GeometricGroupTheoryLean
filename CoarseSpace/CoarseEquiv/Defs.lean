/-
Copyright (c) 2026 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import CoarseSpace.Basic

/-!
# Coarse Equivalences

A `CoarseEquiv X Y` consists of controlled maps `f : X → Y` and `g : Y → X` such that
`f ∘ g` and `g ∘ f` are close to the identity. We write `X ≃ᶜ Y`.
-/

open Function Filter
open scoped SetRel Coarse

variable {α β γ : Type*}

/-- Coarse equivalence between `α` and `β`. -/
structure CoarseEquiv (α β : Type*) [CoarseSpace α] [CoarseSpace β] where
  toFun : α → β
  invFun : β → α
  controlled_toFun : IsControlledMap toFun := by fun_prop
  controlled_invFun : IsControlledMap invFun := by fun_prop
  isClose_id_right : toFun ∘ invFun =ᶜ id
  isClose_id_left : invFun ∘ toFun =ᶜ id

@[inherit_doc]
infixl:25 " ≃ᶜ " => CoarseEquiv

namespace CoarseEquiv

variable [CoarseSpace α] [CoarseSpace β] [CoarseSpace γ]

/-- The forward map of a coarse equivalence is a coarse map. -/
@[fun_prop]
protected theorem coarse (e : α ≃ᶜ β) : Coarse e.toFun :=
  ⟨e.controlled_toFun,
   e.controlled_invFun.isCoarselyProperMap_of_isClose_comp_id e.isClose_id_left⟩

instance : CoeFun (α ≃ᶜ β) (fun _ ↦ α → β) := ⟨fun e ↦ e.toFun⟩

@[simp] theorem coe_toFun (e : α ≃ᶜ β) : (e.toFun : α → β) = e := rfl

@[ext]
theorem ext {e₁ e₂ : α ≃ᶜ β} (h : ∀ x, e₁ x = e₂ x) (h' : ∀ y, e₁.invFun y = e₂.invFun y) :
    e₁ = e₂ := by
  cases e₁; cases e₂; simp only [mk.injEq]; exact ⟨funext h, funext h'⟩

/-- Identity coarse equivalence. -/
@[simps! -fullyApplied toFun invFun]
protected def refl (α : Type*) [CoarseSpace α] : α ≃ᶜ α where
  toFun := id
  invFun := id
  isClose_id_left := IsClose.refl _
  isClose_id_right := IsClose.refl _

/-- Inverse coarse equivalence. -/
@[symm]
protected def symm (e : α ≃ᶜ β) : β ≃ᶜ α where
  toFun := e.invFun
  invFun := e.toFun
  controlled_toFun := e.controlled_invFun
  controlled_invFun := e.controlled_toFun
  isClose_id_left := e.isClose_id_right
  isClose_id_right := e.isClose_id_left

@[fun_prop]
protected theorem coarse_symm (e : α ≃ᶜ β) : Coarse e.symm.toFun :=
  ⟨e.controlled_invFun,
   e.controlled_toFun.isCoarselyProperMap_of_isClose_comp_id e.isClose_id_right⟩

@[simp] theorem coe_invFun (e : α ≃ᶜ β) : (e.invFun : β → α) = e.symm := rfl
@[simp] theorem symm_symm (e : α ≃ᶜ β) : e.symm.symm = e := by cases e; rfl

@[fun_prop]
theorem controlled_toFun' (e : α ≃ᶜ β) : IsControlledMap e.toFun := e.controlled_toFun

@[fun_prop]
theorem controlled_invFun' (e : α ≃ᶜ β) : IsControlledMap e.invFun := e.controlled_invFun

/-- Composition of coarse equivalences. -/
@[trans]
protected def trans (e₁ : α ≃ᶜ β) (e₂ : β ≃ᶜ γ) : α ≃ᶜ γ where
  toFun := e₂.toFun ∘ e₁.toFun
  invFun := e₁.invFun ∘ e₂.invFun
  isClose_id_right :=
    ((e₁.isClose_id_right.comp e₂.invFun).lcomp e₂.controlled_toFun).trans e₂.isClose_id_right
  isClose_id_left :=
    ((e₂.isClose_id_left.comp e₁.toFun).lcomp e₁.controlled_invFun).trans e₁.isClose_id_left

@[simp] theorem trans_apply (e₁ : α ≃ᶜ β) (e₂ : β ≃ᶜ γ) (x : α) : (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] theorem symm_trans (e₁ : α ≃ᶜ β) (e₂ : β ≃ᶜ γ) :
  (e₁.trans e₂).symm = e₂.symm.trans e₁.symm := rfl

/-- Construct a coarse equivalence from an equivalence where both directions are coarse. -/
def ofEquiv (e : α ≃ β)
  (hf : IsControlledMap e := by fun_prop)
  (hg : IsControlledMap e.symm := by fun_prop) :
    α ≃ᶜ β where
  toFun := e
  invFun := e.symm
  isClose_id_right := (Equiv.self_comp_symm e) ▸ (IsClose.refl _)
  isClose_id_left :=  (Equiv.symm_comp_self e) ▸ (IsClose.refl _)

end CoarseEquiv
