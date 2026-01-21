/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import CoarseSpace.Entourage.Basic
import Mathlib.Tactic.FunProp

/-!
# Coarse Spaces

This file defines **coarse spaces** using controlled entourages.

## Main definitions

* `CoarseSpace X` : a coarse structure on `X`
* `IsCoarselyBounded` : a set whose product with itself is controlled
* `IsClose` : closeness of functions
* `CoarselyProper` : preimages of bounded sets are bounded
* `Controlled` : pushforwards of controlled sets are controlled
* `Coarse` : both proper and controlled

## References

* J. Roe, *Lectures on Coarse Geometry*, University Lecture Series 31, AMS, 2003
-/

open Set Entourage Prod

universe u v w

/-- A coarse structure on a type `X`.

A `CoarseSpace X` is given by a predicate `IsControlled` on entourages
such that `IsControlled` contains the diagonal, is symmetric and is
closed under taking subsets, finite unions and composition. -/
class CoarseSpace (X : Type u) where
  IsControlled : Entourage X → Prop
  protected isControlled_subset :
    ∀ {E F : Entourage X}, IsControlled E → F ⊆ E → IsControlled F
  protected isControlled_union :
   ∀ {E F : Entourage X}, IsControlled E → IsControlled F → IsControlled (E ∪ F)
  isControlled_id :
    IsControlled Entourage.id
  protected isControlled_inv :
    ∀ {E : Entourage X}, IsControlled E → IsControlled E⁻¹
  protected isControlled_comp :
    ∀ {E F : Entourage X}, IsControlled E → IsControlled F → IsControlled (E ○ F)

export CoarseSpace (IsControlled isControlled_id)

scoped[CoarseSpace] notation (name := IsControlled_of) "IsControlled[" c "]" =>
  @IsControlled _ c

open CoarseSpace

/-- Copy of a `CoarseSpace` with a new `CoarseSpace` equal to the old one. Useful to fix
definitional equalities. -/
protected def CoarseSpace.copy {X : Type u} (c : CoarseSpace X)
  (p : Entourage X → Prop) (h : ∀ E, p E ↔ IsControlled[c] E) :
    CoarseSpace X where
    IsControlled := p
    isControlled_subset := by simp_rw [h]; exact c.isControlled_subset
    isControlled_union  := by simp_rw [h]; exact c.isControlled_union
    isControlled_id     := by simp_rw [h]; exact c.isControlled_id
    isControlled_inv    := by simp_rw [h]; exact c.isControlled_inv
    isControlled_comp   := by simp_rw [h]; exact c.isControlled_comp

variable {X : Type u} {Y : Type v} [CoarseSpace X]

/-- A set `s : Set X` is coarsely bounded if the product `s ×ˢ s` is a
controlled relation. -/
structure IsCoarselyBounded (s : Set X) : Prop where
  isControlled : IsControlled (s ×ˢ s)

/-- Notation `IsCoarselyBounded[s]` for `IsCoarselyBounded (X := _) s`, scoped to
`CoarseSpace`. -/
scoped[CoarseSpace] notation (name := IsCoarselyBounded_of) "IsCoarselyBounded[" c "]" =>
  @IsCoarselyBounded _ c

/-- A coarsely bounded space is one in which `Set.univ : Set X` is coarsely bounded. -/
class CoarselyBoundedSpace (X : Type u) [CoarseSpace X] : Prop where
  coarselyBounded_univ : IsCoarselyBounded (Set.univ : Set X)

/-- Two functions are close to each other if `range <| map f g` is a controlled set. -/
def IsClose {α : Type w} (f g : α → X) : Prop := IsControlled (range <| (fun x ↦ (f x, g x)))

@[inherit_doc]
notation:50 f " =ᶜ " g:50 => IsClose f g

variable [CoarseSpace Y]

/-- A function `f` between coarse spaces is a controlled map iff pushforward of controlled
entourages under `f` is controlled. -/
@[fun_prop]
def Controlled (f : X → Y) : Prop :=
  ∀ {E}, IsControlled E → IsControlled (map f E)

/-- A function `f` between coarse spaces is a proper map iff the preimage of coarsely bounded sets
is coarsely bounded. -/
@[fun_prop]
def CoarselyProper (f : X → Y) : Prop :=
  ∀ {s}, IsCoarselyBounded s → IsCoarselyBounded (f⁻¹' s)

/-- A function between coarse spaces is a coarse map if it is a proper map and a controlled map. -/
@[fun_prop]
structure Coarse (f : X → Y) : Prop where
  controlled' : Controlled f := by fun_prop
  coarselyProper : CoarselyProper f := by fun_prop

@[fun_prop]
theorem Coarse.controlled {f : X → Y} (hf : Coarse f) : Controlled f :=
  hf.controlled'

@[fun_prop]
theorem Coarse.proper {f : X → Y} (hf : Coarse f) : CoarselyProper f :=
  hf.coarselyProper
