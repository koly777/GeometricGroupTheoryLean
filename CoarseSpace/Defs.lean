/-
Copyright (c) 2026 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import Mathlib.Order.Filter.Lift
import Mathlib.Tactic.FunProp

import ForMathlib.Data.Rel

/-!
# Coarse Spaces

This file defines coarse spaces using a filter-theoretic approach dual to the standard
entourage-based definition.

## Main Definitions

* `CoarseSpace α`: A coarse structure on `α`, given by a filter of *cocontrolled* sets on `α × α`.
* `IsCocontrolled s`: The predicate that `s : SetRel α α` is cocontrolled (a member of the filter).
* `IsControlled s`: The predicate that `s : SetRel α α` is controlled.
* `IsCoarselyBounded s`: The predicate that `s : Set α` is bounded (i.e `s ×ˢ s` is controlled).
* `IsClose f g`: The predicate that two maps `f g : α → β` are close.
* `IsControlledMap f`: The predicate that `f : α → β` sends controlled sets to controlled sets.
* `IsCoarselyProperMap f`: The predicate that `f : α → β` has bounded preimages of bounded sets.
* `Coarse f`: The structure combining `IsControlledMap` and `IsCoarselyProperMap`.

## Design Notes

Rather than axiomatizing controlled sets directly (which form an ideal-like structure), we work
with their complements, the *cocontrolled* sets, which form a filter. This approach:

* Gives subset and finite union closure for controlled sets automatically from the filter axioms.
* Expresses the composition axiom (making use of the residual) via:
  `cocontrolled ≤ cocontrolled.lift' (fun s ↦ sᶜ ⧵ s)`.
  One can recover composition in the presence of the filter axioms.

## Tags

coarse space, coarse geometry, controlled set, bornologous, proper map
-/

universe u v

open Filter
open scoped SetRel

/-- A coarse space is a generalization of the "large-scale" or "coarse" aspects of a metric space,
capturing the notion of bounded distance without requiring a specific metric. It consists of a
filter on `α × α` called the "cocontrolled" sets, whose complements—the *controlled* sets—satisfy
properties analogous to the reflexivity, symmetry, and triangle inequality of a metric.

The controlled sets form a structure similar to a bornology: they are closed under subsets and
finite unions. -/
class CoarseSpace (α : Type u) where
  /-- The filter of cocontrolled sets in a coarse space. -/
  protected cocontrolled : Filter (α × α)
  /-- The complement of the diagonal is cocontrolled. -/
  protected refl : cocontrolled ≤ 𝓟 (SetRel.id)ᶜ
  /-- If `s ∈ cocontrolled`, then `Prod.swap ⁻¹' s ∈ cocontrolled`. -/
  protected symm : Tendsto Prod.swap cocontrolled cocontrolled
  /-- Composition: if `sᶜ` and `tᶜ` are cocontrolled, so is `(sᶜ ○ tᶜ)ᶜ`.
      Stated dually using the residual. -/
  protected comp : cocontrolled ≤ cocontrolled.lift' (fun s ↦ sᶜ ⧵ s)

/-- Notation for the cocontrolled filter. -/
scoped[Coarse] notation "𝓒" => CoarseSpace.cocontrolled
scoped[Coarse] notation "𝓒[" c "]" => @CoarseSpace.cocontrolled _ c

variable {α : Type u} {β : Type v}

section Defs

/-- Defining a `CoarseSpace` from a filter basis satisfying coarse-space-like axioms. -/
@[simps! cocontrolled]
def CoarseSpace.mkOfBasis {α : Type u} (B : FilterBasis (α × α))
    (refl : ∀ r ∈ B, r ⊆ (SetRel.id)ᶜ)
    (symm : ∀ r ∈ B, ∃ t ∈ B, t ⊆ Prod.swap ⁻¹' r)
    (comp : ∀ r ∈ B, ∃ t ∈ B, t ⊆ rᶜ ⧵ r) : CoarseSpace α where
  cocontrolled := B.filter
  refl := le_principal_iff.mpr <| B.mem_filter_iff.mpr
          ⟨_, B.nonempty.some_mem, refl _ B.nonempty.some_mem⟩
  symm := (B.hasBasis.tendsto_iff B.hasBasis).mpr symm
  comp := (B.hasBasis.le_basis_iff <|
           B.hasBasis.lift' <|
           compl_anti.res monotone_id).2 comp

/-- Defining a `CoarseSpace` from a set of controlled relations. -/
@[simps! cocontrolled]
def CoarseSpace.ofControlled {α : Type*} (C : Set (SetRel α α))
    (subset_mem : ∀ s₁ ∈ C, ∀ s₂ ⊆ s₁, s₂ ∈ C)
    (union_mem : ∀ s₁ ∈ C, ∀ s₂ ∈ C, s₁ ∪ s₂ ∈ C)
    (refl_mem : SetRel.id ∈ C)
    (symm_mem : ∀ s ∈ C, Prod.swap ⁻¹' s ∈ C)
    (comp_mem : ∀ s ∈ C, s ○ s ∈ C) : CoarseSpace α where
  cocontrolled := comk (· ∈ C)
    (subset_mem _ refl_mem _ <| Set.empty_subset SetRel.id) subset_mem union_mem
  refl := le_principal_iff.mpr <| compl_mem_comk.mpr <| subset_mem _ refl_mem _ fun _ h ↦ h
  symm := fun s ↦ by
    simp only [mem_comk, mem_map];
    exact fun h ↦ Set.preimage_compl ▸ symm_mem _ h
  comp := le_lift'.mpr fun s hs ↦ mem_comk.mpr <| by
    rw [← compl_compl s, ← SetRel.compl_comp, compl_compl, compl_compl]
    exact comp_mem sᶜ hs

variable [CoarseSpace α] [CoarseSpace β]

/-- `IsCocontrolled` is the predicate that `s` is in the filter of cocontrolled sets in the ambient
CoarseSpace on `α`. -/
def IsCocontrolled (s : SetRel α α) : Prop := s ∈ CoarseSpace.cocontrolled

/-- `IsControlled` is the predicate that `s` is controlled if its complement is cocontrolled. -/
def IsControlled (s : SetRel α α) : Prop := IsCocontrolled sᶜ

/-- `IsCoarselyBounded` is the predicate that `s : Set α` is bounded if `s ×ˢ s` is controlled. -/
def IsCoarselyBounded (s : Set α) : Prop := IsControlled (s ×ˢ s)

omit [CoarseSpace α] in
/-- Two functions are close to each other on `s` if `map f g '' SetRel.id` is a controlled set. -/
def IsClose (f g : α → β) : Prop := IsControlled <| .map f g '' SetRel.id

@[inherit_doc]
notation:50 f " =ᶜ " g:50 => IsClose f g

open Coarse in
/-- A map `f : α → β` is a *controlled map* if the pullback of the CoarseSpace.cocontrolled
filter under the function `Prod.map f f` is contained in the cocontrolled filter.

Equivalently, the function maps controlled sets to controlled sets. -/
@[fun_prop]
def IsControlledMap (f : α → β) : Prop :=
  (𝓒 : Filter (β × β)).comap (.map f f) ≤ 𝓒

/-- A map `f : α → β` is a *coarsely proper map* if the pullback of the coarsely bounded sets
is coarsely bounded. -/
@[fun_prop]
def IsCoarselyProperMap (f : α → β) : Prop :=
  ∀ s : Set β, IsCoarselyBounded s → IsCoarselyBounded (f⁻¹' s)

/-- A map between `f : α → β` between coarse spaces is *coarse* if it is
a controlled and coarsely proper map. -/
@[fun_prop]
structure Coarse (f : α → β) : Prop where
  controlled : IsControlledMap f
  proper : IsCoarselyProperMap f

end Defs

/-! ### Notation for non-standard coarse spaces -/

/-- Notation for `IsCocontrolled` with respect to a non-standard coarse space. -/
scoped[Coarse] notation (name := IsCocontrolled_of) "IsCocontrolled[" c "]" =>
  @IsCocontrolled _ c

/-- Notation for `IsControlled` with respect to a non-standard coarse space. -/
scoped[Coarse] notation (name := IsControlled_of) "IsControlled[" c "]" =>
  @IsControlled _ c

/-- Notation for `IsCoarselyBounded` with respect to a non-standard coarse space. -/
scoped[Coarse] notation (name := IsCoarselyBounded_of) "IsCoarselyBounded[" c "]" =>
  @IsCoarselyBounded _ c
