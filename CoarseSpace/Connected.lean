/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/

import Mathlib.Topology.Bornology.Basic

import CoarseSpace.Basic
import CoarseSpace.Finiteness

/-!
# Coarse Connectivity

A set is coarsely connected if every pair of points lies in some controlled entourage.
A coarse space is coarsely connected if the entire space is.

## Main Definitions

* `IsCoarselyConnected s`: every pair in `s` belongs to some controlled entourage.
* `CoarselyConnectedSpace X`: typeclass for coarsely connected spaces.
* `CoarselyConnectedSpace.toBornology`: the bornology whose bounded sets are the coarsely
  bounded sets.

## Main Results

* `IsCoarselyConnected.image`: images under controlled maps preserve coarse connectivity.
* `IsCoarselyBounded.union`: in a coarsely connected space, unions of coarsely bounded sets
  are coarsely bounded.
* `CoarselyConnectedSpace.pow_nonempty_of_generateFrom`: in a finitely generated coarsely
  connected space, any two points are connected by a finite power of the generating set.

## References

* J. Roe, *Lectures on Coarse Geometry*, University Lecture Series 31, AMS, 2003
-/

open Set Entourage CoarseSpace Bornology

variable {X : Type*} {Y : Type*}
variable [CoarseSpace X] [CoarseSpace Y]

/-- A set is coarsely connected if each pair of elements in `s` is
a member of some controlled set. -/
def IsCoarselyConnected (s : Set X) :=
  s ×ˢ s ⊆ ⋃₀ {E | IsControlled E}

/--
Equivalent characterization of coarse connectivity: a set is coarsely connected if and only if
for every pair of points in the set, there exists a controlled set containing that pair.
-/
theorem isCoarselyConnected_iff {s : Set X} :
    IsCoarselyConnected s ↔ ∀ x ∈ s, ∀ y ∈ s, ∃ E, IsControlled E ∧ (x, y) ∈ E := by
    rw [IsCoarselyConnected]
    constructor
    · intro h _ hx _ hy
      simpa only [mem_sUnion, mem_setOf_eq] using h (mk_mem_prod hx hy)
    · intro h _ hxy
      simpa only [Set.mem_prod, mem_sUnion, mem_setOf_eq] using h _ hxy.1 _ hxy.2

@[simp]
theorem isCoarselyConnected_empty : IsCoarselyConnected (∅ : Set X):= by
  rw [IsCoarselyConnected, prod_empty]
  exact empty_subset _

/-- Every singleton set is coarsely connected. -/
@[simp]
theorem isCoarselyConnected_singleton (x : X) :
    IsCoarselyConnected ({x} : Set X) := by
  rw [IsCoarselyConnected, singleton_prod_singleton]
  exact singleton_subset_iff.mpr ⟨Entourage.id, isControlled_id, rfl⟩

/-- Subsets of coarsely connected sets are coarsely connected. -/
theorem IsCoarselyConnected.subset {s t : Set X}
    (ht : IsCoarselyConnected t) (hst : s ⊆ t) : IsCoarselyConnected s :=
  (prod_mono hst hst).trans ht

/-- If `s` is coarsely connected and `x, y ∈ s`, then the singleton pair
`{(x, y)}` is controlled. -/
theorem IsCoarselyConnected.pair {x y : X} {s : Set X}
  (hs : IsCoarselyConnected s) (hx : x ∈ s) (hy : y ∈ s) :
  IsControlled {(x, y)} := by
  obtain ⟨t, ht, hxy⟩ := mem_sUnion.mp (hs <| mk_mem_prod hx hy)
  exact ht.subset <| singleton_subset_iff.mpr hxy

/-- Symmetry for coarsely connected sets: if `{(x, y)}` is controlled for all `x, y ∈ s`,
then so is `{(y, x)}`. -/
theorem IsCoarselyConnected.symm {s : Set X} (hs : IsCoarselyConnected s) :
    ∀ x ∈ s, ∀ y ∈ s, IsControlled {(y, x)} :=
  fun _ hx _ hy => hs.pair hy hx

/-- The image of a coarsely connected set under a controlled map is coarsely connected. -/
theorem IsCoarselyConnected.image {s : Set X} {f : X → Y}
    (hs : IsCoarselyConnected s) (hf : Controlled f) : IsCoarselyConnected (f '' s) := by
  rw [isCoarselyConnected_iff]
  intro _ ⟨x, hx, hfx⟩ _ ⟨y, hy, hfy⟩
  subst_vars
  obtain ⟨E, hE, hxy⟩ := isCoarselyConnected_iff.mp hs x hx y hy
  exact ⟨E.map f, hf hE, mem_map_iff.mpr ⟨x, y, hxy, rfl, rfl⟩⟩

/-- A coarse space `X` is coarsely connected if `@Set.univ X` is coarsely connected. -/
class CoarselyConnectedSpace (X : Type*) [CoarseSpace X] : Prop where
  isCoarselyConnected_univ : IsCoarselyConnected (@Set.univ X)

export CoarselyConnectedSpace (isCoarselyConnected_univ)

/-- In a coarsely connected space, every pair of points forms a controlled singleton. -/
theorem CoarselyConnectedSpace.isControlled_pair {X : Type*} [CoarseSpace X]
  [CoarselyConnectedSpace X] (x y : X) : IsControlled {(x, y)} :=
  isCoarselyConnected_univ.pair (mem_univ _) (mem_univ _)

/--
In a coarsely connected space, any two constant functions are close. -/
theorem IsClose.const [CoarselyConnectedSpace X] {Y : Type*} (x y : X) :
    Function.const Y x =ᶜ Function.const _ y := by
  unfold IsClose
  simp only [Function.const_apply]
  by_cases h : Nonempty Y
  · rw [range_const]; exact CoarselyConnectedSpace.isControlled_pair x y
  · rw [not_nonempty_iff] at h
    rw [range_eq_empty]
    exact isControlled_empty

/-- In a coarsely connected space, the union of two coarsely bounded sets is coarsely bounded. -/
theorem IsCoarselyBounded.union [CoarselyConnectedSpace X] {s t : Set X}
  (hs : IsCoarselyBounded s) (ht : IsCoarselyBounded t) :
  IsCoarselyBounded (s ∪ t) := by
  wlog hs_nonempty : IsEmpty (s: Set X) generalizing s t
  · by_cases ht_nonempty : IsEmpty t
    · simpa [union_comm] using this ht hs ht_nonempty
    · rw [not_isEmpty_iff] at *; clear this;
      obtain ⟨x, hx⟩ := (isCoarselyBounded_iff_isClose_const (hs_nonempty)).mp hs
      obtain ⟨y, hy⟩ := (isCoarselyBounded_iff_isClose_const (ht_nonempty)).mp ht
      apply (isCoarselyBounded_iff_isClose_const (s := (s ∪ t)) _).mpr
      · use x; apply isClose_of_union (Y := (s ∪ t : Set X)) (f := Subtype.val)
         (f₁ := Function.const _ x) (s := { z | (z : X) ∈ s }) (t := { z | (z : X) ∈ t })
        · intro z
          rcases z.property with hz | hz
          · left;  exact hz
          · right; exact hz
        · simpa using (.comp (restrictPreimage s Subtype.val) hx)
        · simpa using (.comp (restrictPreimage t Subtype.val)
          (IsClose.trans hy <| IsClose.const y x))
      · refine nonempty_subtype.mpr ?_
        rcases hs_nonempty with ⟨x, _⟩
        use x; left; assumption
  · rw [isEmpty_coe_sort] at *
    subst_vars; rwa [empty_union]

namespace CoarselyConnectedSpace

variable [CoarselyConnectedSpace X]

/--
A coarsely connected space induces a bornology whose bounded sets are exactly the coarsely
bounded sets. -/
def toBornology : Bornology X := Bornology.ofBounded
  ({s | IsCoarselyBounded s})
  (isCoarselyBounded_empty)
  (fun _ h _ h₁ ↦ h.subset h₁)
  (fun _ h _ h₁ ↦ h.union h₁)
  (fun _ ↦ isCoarselyBounded_singleton _)

/-- A set is bounded in the induced bornology if and only if it is coarsely bounded. -/
theorem isBounded_iff_isCoarselyBounded {s : Set X} :
 @IsBounded _ toBornology s ↔ IsCoarselyBounded s := by
  rw [isBounded_ofBounded_iff]; rfl

/-- In finitely generated coarsely connected spaces, any two points can be connected
by a finite chain of elements from the generating set. -/
theorem pow_nonempty_of_generateFrom (S : Finset (Entourage X))
    (hS : generateFrom (S : Set (Entourage X)) = ‹CoarseSpace X›) (x y : X) :
    {n : ℕ | (x, y) ∈ ((S.sup id).symmetrize ∪ Entourage.id) ^ n}.Nonempty := by
  obtain ⟨F, hF, hxy⟩ := isCoarselyConnected_iff.mp isCoarselyConnected_univ x trivial y trivial
  obtain ⟨n, hn⟩ := (isControlled_iff_subset_pow_of_generateFrom S hS F).mp hF
  exact ⟨n, hn hxy⟩

end CoarselyConnectedSpace

namespace FG

theorem pow_nonempty_of_getGenerator [CoarselyConnectedSpace X] [FG X] (x y : X) :
    {n : ℕ | (x, y) ∈ (FG.getGenerator X) ^ n}.Nonempty := by
  obtain ⟨E, hE, hxy⟩ := isCoarselyConnected_iff.mp isCoarselyConnected_univ x trivial y trivial
  obtain ⟨n, hn⟩ := FG.getGenerator_mem_pow E hE
  exact ⟨n, hn hxy⟩

end FG
