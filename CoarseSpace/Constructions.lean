/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import CoarseSpace.Basic

import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Set.Image

/-!
# Constructions of Coarse Spaces

This file defines coarse space structures on various type constructions.

## Main Definitions

* `CoarseSpace.induced`: The induced (pullback) coarse structure along a function.
* `instCoarseSpaceSubtype`: Coarse structure on subtypes via the induced structure.
* Product coarse structure on `X × Y`.
* Dependent product coarse structure on `∀ i, C i`.

## Main Results

* `isControlled_induced_iff`: Characterization of controlled sets in the induced structure.
* `isControlled_subtype_iff`: Controlled sets in subtypes.
* `isControlled_prod_iff`: Controlled sets in products.
* `isControlled_pi_iff`: Controlled sets in dependent products.
* `isCoarselyBounded_prod_iff`: Coarsely bounded sets in products.
* `isCoarselyBounded_pi_iff`: Coarsely bounded sets in dependent products.

## Implementation Notes

The product coarse structure is defined so that a set is controlled iff its projections
to each factor are controlled. Similarly for dependent products.

## References

* J. Roe, *Lectures on Coarse Geometry*, University Lecture Series 31, AMS, 2003
-/

open CoarseSpace Entourage Set Function

variable {X Y ι : Type*} {C : ι → Type*} [∀ i, CoarseSpace (C i)]

/-! ### Induced Coarse Structures -/

/-- The induced (pullback) coarse structure on `X` along a function `f : X → Y`.
A set `E ⊆ X × X` is controlled iff its image under `f × f` is controlled in `Y`. -/
def CoarseSpace.induced {X Y : Type*} (f : X → Y) (cY : CoarseSpace Y) : CoarseSpace X where
  IsControlled        := fun E ↦ @IsControlled Y _ <| (E.map f)
  isControlled_subset := fun hE hF ↦ hE.subset <| image_mono hF
  isControlled_union  := fun hE hF ↦ map_union _ _ _ ▸ (hE.union hF)
  isControlled_id     := isControlled_id.subset (image_subset_iff.mpr fun _ ↦ congrArg _)
  isControlled_inv    := fun hE ↦ map_inv _ f ▸ hE.inv
  isControlled_comp   := fun hE hF ↦ (hE.comp hF).subset (map_comp_subset _ _ _)

/-- Type class version of `CoarseSpace.induced`. -/
abbrev CoarseSpace.inducedTC {X Y} [cY : CoarseSpace Y] (f : X → Y) :
    CoarseSpace X :=
  CoarseSpace.induced f cY

/-- A set is controlled in the induced coarse structure iff its image is controlled. -/
@[simp]
theorem isControlled_induced_iff {f : X → Y} (c : CoarseSpace Y) (E : Entourage X) :
    IsControlled[CoarseSpace.induced f c] E ↔ IsControlled[c] (E.map f) := Iff.rfl

@[simp]
theorem isCoarselyBounded_induced_iff [CoarseSpace Y] (f : X → Y) (s : Set X) :
    IsCoarselyBounded[CoarseSpace.inducedTC f] s ↔ IsCoarselyBounded (f '' s) := by
  constructor <;> rintro ⟨h⟩
  · exact ⟨prodMap_image_prod .. ▸ h⟩
  · exact @IsCoarselyBounded.mk X (CoarseSpace.inducedTC f) s <| by
      change IsControlled (map f (s ×ˢ s))
      rwa [Entourage.map_def, prodMap_image_prod]

/-! ### Subtypes -/

variable [CoarseSpace X]

/-- Subtypes inherit the induced coarse structure from the ambient space. -/
instance instCoarseSpaceSubtype {p : X → Prop} :
    CoarseSpace (Subtype p) :=
  CoarseSpace.inducedTC (Subtype.val : Subtype p → X)

/-- A set is controlled in a subtype iff its image under `Subtype.val` is controlled. -/
theorem isControlled_subtype_iff {p : X → Prop} {E : Entourage (Subtype p)} :
    IsControlled E ↔ IsControlled (E.map Subtype.val) := Iff.rfl

/-- A set in a subtype is coarsely bounded iff its image under `Subtype.val` is. -/
theorem isCoarselyBounded_subtype_iff {p : X → Prop} (s : Set (Subtype p)) :
    IsCoarselyBounded s ↔ IsCoarselyBounded (Subtype.val '' s) :=
  isCoarselyBounded_induced_iff _ _

/-! ### Products -/

/-- Product coarse structure on `X × Y`. A set is controlled iff both projections are controlled. -/
instance [CoarseSpace Y] : CoarseSpace (X × Y) where
  IsControlled        := fun E ↦ (IsControlled <| E.map (Prod.fst)) ∧
                                 (IsControlled <| E.map (Prod.snd))
  isControlled_subset := fun hE hF ↦ ⟨hE.1.subset <| image_mono hF, hE.2.subset <| image_mono hF⟩
  isControlled_union  := fun hE hF ↦ ⟨map_union .. ▸ hE.1.union hF.1,
                                      map_union .. ▸ hE.2.union hF.2⟩
  isControlled_id     := ⟨isControlled_id.subset (image_subset_iff.mpr fun _ ↦ congrArg _),
                          isControlled_id.subset (image_subset_iff.mpr fun _ ↦ congrArg _)⟩
  isControlled_inv    := fun hE ↦ ⟨map_inv .. ▸ hE.1.inv, map_inv .. ▸ hE.2.inv⟩
  isControlled_comp   := fun hE hF ↦ ⟨(hE.1.comp hF.1).subset (map_comp_subset ..),
                                     (hE.2.comp hF.2).subset (map_comp_subset ..)⟩

namespace CoarseSpace

variable [CoarseSpace Y]

/-! #### Controlled Sets in Products -/

/-- A set in `(X × Y) × (X × Y)` is controlled iff both projections are controlled. -/
theorem isControlled_prod_iff {E : Entourage (X × Y)} :
    IsControlled (E.map (Prod.fst)) ∧ IsControlled (E.map (Prod.snd)) ↔ IsControlled E :=
  Iff.rfl

/-- The first projection of a controlled set in a product is controlled. -/
@[aesop safe apply]
lemma IsControlled.image_fst {E : Entourage (X × Y)} (hE : IsControlled E) :
    IsControlled (E.map (Prod.fst)) :=
  (isControlled_prod_iff.2 hE).1

/-- The second projection of a controlled set in a product is controlled. -/
@[aesop safe apply]
lemma IsControlled.image_snd {E : Entourage (X × Y)} (hE : IsControlled E) :
    IsControlled (E.map (Prod.snd)) :=
  (isControlled_prod_iff.2 hE).2

variable {E : Entourage X} {F : Entourage Y} {S : ∀ i, Entourage (C i)}

/-- If a product of entourages is controlled and the second factor is nonempty,
then the first factor is controlled. -/
@[aesop safe apply]
theorem IsControlled.fst_of_prod (h : IsControlled (E ×ˢ F)) (hF : F.Nonempty) :
    IsControlled E :=
  map_fst_sprod E F hF ▸ h.image_fst

/-- If a product of entourages is controlled and the first factor is nonempty,
then the second factor is controlled. -/
@[aesop safe apply]
theorem IsControlled.snd_of_prod (h : IsControlled (E ×ˢ F)) (hE : E.Nonempty) :
    IsControlled F :=
  map_snd_sprod E F hE ▸ h.image_snd

/-- The product of controlled entourages is controlled. -/
@[aesop safe apply]
theorem IsControlled.sprod (hE : IsControlled E) (hF : IsControlled F) :
    IsControlled (E ×ˢ F) :=
  match E.eq_empty_or_nonempty, F.eq_empty_or_nonempty with
  | .inl hE', _ => hE' ▸ sprod_empty_left F ▸ isControlled_empty
  | _, .inl hF' => hF' ▸ sprod_empty_right E ▸ isControlled_empty
  | .inr hE', .inr hF' =>
      ⟨(map_fst_sprod E F hF').symm ▸ hE, (map_snd_sprod E F hE').symm ▸ hF⟩

/-- For nonempty products, controlledness is equivalent to both factors being controlled. -/
@[simp]
theorem isControlled_sprod_iff_of_nonempty (hne : (E ×ˢ F).Nonempty) :
    IsControlled (E ×ˢ F) ↔ IsControlled E ∧ IsControlled F := by
  rw [sprod_nonempty] at hne
  exact ⟨fun h ↦ ⟨h.fst_of_prod hne.2, h.snd_of_prod hne.1⟩,
         fun ⟨hE, hF⟩ ↦ hE.sprod hF⟩

/-- Full characterization of when a product of entourages is controlled. -/
theorem isControlled_sprod :
    IsControlled (E ×ˢ F) ↔ E = ∅ ∨ F = ∅ ∨ IsControlled E ∧ IsControlled F :=
  ⟨fun h ↦ (em (E = ∅)).elim .inl fun hE ↦ (em (F = ∅)).elim (.inr ∘ .inl) fun hF ↦
     .inr (.inr ((isControlled_sprod_iff_of_nonempty (sprod_nonempty.mpr
       ⟨nonempty_iff_ne_empty.mpr hE, nonempty_iff_ne_empty.mpr hF⟩)).mp h)),
   fun | .inl h => h ▸ (sprod_empty_left F ▸ isControlled_empty)
       | .inr (.inl h) => h ▸ (sprod_empty_right E ▸ isControlled_empty)
       | .inr (.inr ⟨hE, hF⟩) => hE.sprod hF⟩

/-- `E ×ˢ id` is controlled iff `E` is controlled. -/
theorem isControlled_sprod_id_iff [Nonempty Y] {E : Entourage X} :
    IsControlled (E ×ˢ Entourage.id (α := Y)) ↔ IsControlled E :=
  ⟨fun ⟨h, _⟩ => map_fst_sprod_id (β := Y) E ▸ h,
   fun hE => ⟨(map_fst_sprod_id (β := Y) E).symm ▸ hE,
              isControlled_id.subset (map_snd_sprod_id_subset E)⟩⟩

/-- `id ×ˢ F` is controlled iff `F` is controlled. -/
theorem isControlled_id_sprod_iff [Nonempty X] {F : Entourage Y} :
    IsControlled (Entourage.id (α := X) ×ˢ F) ↔ IsControlled F :=
  ⟨fun ⟨_, h⟩ => map_snd_id_sprod (α := X) F ▸ h,
   fun hF => ⟨isControlled_id.subset (map_fst_id_sprod_subset F),
              (map_snd_id_sprod (α := X) F).symm ▸ hF⟩⟩

/-- On an empty type, every entourage is controlled. -/
theorem isControlled_of_isEmpty [IsEmpty X] (E : Entourage X) : IsControlled E :=
  isControlled_empty.subset fun ⟨a, _⟩ _ => IsEmpty.false a

/-- On a product with an empty factor, every entourage is controlled. -/
theorem isControlled_prod_of_isEmpty_left [IsEmpty X] (E : Entourage (X × Y)) :
    IsControlled E :=
  ⟨isControlled_of_isEmpty _,
   isControlled_empty.subset fun _ ⟨⟨⟨a, _⟩, _⟩, _, _⟩ => IsEmpty.false a⟩

/-- On a product with an empty factor, every entourage is controlled. -/
theorem isControlled_prod_of_isEmpty_right [IsEmpty Y] (E : Entourage (X × Y)) :
    IsControlled E :=
  ⟨isControlled_empty.subset fun _ ⟨⟨⟨_, b⟩, _⟩, _, _⟩ => IsEmpty.false b,
   isControlled_of_isEmpty _⟩

/-! #### Coarsely Bounded Sets in Products -/

/-- A product of sets is coarsely bounded iff both factors are coarsely bounded. -/
theorem isCoarselyBounded_prod_iff {s : Set X} {t : Set Y} (hs : s.Nonempty) (ht : t.Nonempty) :
    IsCoarselyBounded (s ×ˢ t) ↔ IsCoarselyBounded s ∧ IsCoarselyBounded t :=
  ⟨fun ⟨h⟩ ↦
     have hs_sub : s ×ˢ s ⊆ map Prod.fst ((s ×ˢ t) ×ˢ (s ×ˢ t)) :=
       fun ⟨a₁, a₂⟩ ⟨ha₁, ha₂⟩ ↦
         ⟨((a₁, ht.some), (a₂, ht.some)), ⟨⟨ha₁, ht.some_mem⟩, ⟨ha₂, ht.some_mem⟩⟩, rfl⟩
     have ht_sub : t ×ˢ t ⊆ map Prod.snd ((s ×ˢ t) ×ˢ (s ×ˢ t)) :=
       fun ⟨b₁, b₂⟩ ⟨hb₁, hb₂⟩ ↦
         ⟨((hs.some, b₁), (hs.some, b₂)), ⟨⟨hs.some_mem, hb₁⟩, ⟨hs.some_mem, hb₂⟩⟩, rfl⟩
     ⟨⟨h.image_fst.subset hs_sub⟩, ⟨h.image_snd.subset ht_sub⟩⟩,
   fun ⟨⟨hs'⟩, ⟨ht'⟩⟩ ↦
     have fst_sub : map Prod.fst ((s ×ˢ t) ×ˢ (s ×ˢ t)) ⊆ s ×ˢ s :=
       fun _ ⟨_, ⟨⟨hx₁, _⟩, ⟨hx₂, _⟩⟩, heq⟩ ↦ heq ▸ ⟨hx₁, hx₂⟩
     have snd_sub : map Prod.snd ((s ×ˢ t) ×ˢ (s ×ˢ t)) ⊆ t ×ˢ t :=
       fun _ ⟨_, ⟨⟨_, hy₁⟩, ⟨_, hy₂⟩⟩, heq⟩ ↦ heq ▸ ⟨hy₁, hy₂⟩
     ⟨hs'.subset fst_sub, ht'.subset snd_sub⟩⟩

/-! #### Product s -/

section s

/-- The first projection from a product is a controlled map. -/
@[fun_prop]
theorem controlled_fst : Controlled (Prod.fst : X × Y → X) :=
  fun hE => hE.image_fst

/-- The first projection is coarsely proper when the second factor is coarsely bounded. -/
@[fun_prop]
theorem coarselyProper_fst [Nonempty Y] [CoarselyBoundedSpace Y] :
    CoarselyProper (Prod.fst : X × Y → X) := fun {s} hs =>
  s.eq_empty_or_nonempty.elim
    (fun he => he ▸ Set.preimage_empty (f := Prod.fst) ▸ isCoarselyBounded_empty)
    (fun hne => (Set.prod_univ (s := s)).symm ▸
      (isCoarselyBounded_prod_iff hne (Set.univ_nonempty (α := Y))).mpr
      ⟨hs, isCoarselyBounded_univ⟩)

/-- The first projection is a coarse map when the second factor is coarsely bounded. -/
@[fun_prop]
theorem coarse_fst [Nonempty Y] [CoarselyBoundedSpace Y] :
    Coarse (Prod.fst : X × Y → X) := {}

/-- The second projection from a product is a controlled map. -/
@[fun_prop]
theorem controlled_snd : Controlled (Prod.snd : X × Y → Y) :=
  fun hE => hE.image_snd

/-- The second projection is coarsely proper when the first factor is coarsely bounded. -/
@[fun_prop]
theorem coarselyProper_snd [Nonempty X] [CoarselyBoundedSpace X] :
    CoarselyProper (Prod.snd : X × Y → Y) := fun {s} hs =>
  s.eq_empty_or_nonempty.elim
    (fun he ↦ he ▸ Set.preimage_empty (f := Prod.snd) ▸ isCoarselyBounded_empty)
    (fun hne ↦ (Set.univ_prod (t := s)).symm ▸
      (isCoarselyBounded_prod_iff (Set.univ_nonempty (α := X)) hne).mpr
      ⟨isCoarselyBounded_univ, hs⟩)

/-- The second projection is a coarse map when the first factor is coarsely bounded. -/
@[fun_prop]
theorem coarse_snd [Nonempty X] [CoarselyBoundedSpace X] :
    Coarse (Prod.snd : X × Y → Y) := {}

/-- Embedding into a product at a fixed second coordinate is a controlled map. -/
@[fun_prop]
theorem controlled_prod_mk (b : Y) : Controlled (fun a : X => (a, b)) := by
  intro _ hE; constructor
  · convert hE; ext ⟨⟩; simp
  · exact (isControlled_diag_singleton b).subset <|
    fun _ ⟨_, ⟨_, _, rfl⟩, h⟩ ↦ mem_singleton_of_eq <| id h.symm

/-- Embedding into a product at a fixed second coordinate is coarsely proper. -/
@[fun_prop]
theorem coarselyProper_prod_mk (b : Y) : CoarselyProper (fun a : X => (a, b)) :=
  fun hs => (isCoarselyBounded_image controlled_fst _ hs).subset
    fun a ha => ⟨(a, b), ha, rfl⟩

/-- Embedding into a product at a fixed second coordinate is a coarse map. -/
@[fun_prop]
theorem coarse_prod_mk (b : Y) : Coarse (fun a : X => (a, b)) := {}

/-- Embedding into a product at a fixed first coordinate is a controlled map. -/
@[fun_prop]
theorem controlled_mk_prod (a : X) : Controlled (fun b : Y => (a, b)) := by
  intro E hE; constructor
  · exact (isControlled_diag_singleton a).subset <|
    fun _ ⟨_, ⟨_, _, rfl⟩, h⟩ ↦ mem_singleton_of_eq <| id h.symm
  · convert hE; ext ⟨⟩; simp

/-- Embedding into a product at a fixed first coordinate is coarsely proper. -/
@[fun_prop]
theorem coarselyProper_mk_prod (a : X) : CoarselyProper (fun b : Y => (a, b)) :=
  fun hs => (isCoarselyBounded_image controlled_snd _ hs).subset
    fun b hb => ⟨(a, b), hb, rfl⟩

/-- Embedding into a product at a fixed first coordinate is a coarse map. -/
@[fun_prop]
theorem coarse_mk_prod (a : X) : Coarse (fun b : Y => (a, b)) := {}

/-- Swapping coordinates is a controlled map. -/
@[fun_prop]
theorem controlled_swap : Controlled (Prod.swap : X × Y → Y × X) :=
  fun h => ⟨(Entourage.map_comp ..).symm ▸ h.2, (Entourage.map_comp ..).symm ▸ h.1⟩

/-- Swapping coordinates is a coarsely proper map. -/
@[fun_prop]
theorem coarselyProper_swap : CoarselyProper (Prod.swap : X × Y → Y × X) :=
  fun h => congrFun image_swap_eq_preimage_swap _ ▸
    (isCoarselyBounded_image controlled_swap _ h)

/-- `Prod.swap` is a coarse map. -/
@[fun_prop]
theorem coarse_swap : Coarse (Prod.swap : X × Y → Y × X) := {}

/-! #### Closeness of Product s -/

section Prod

variable {γ δ : Type*}

/-- The product of close maps is close to the product. -/
theorem IsClose.prodMap {f f' : γ → X} {g g' : δ → Y}
    (hf : f =ᶜ f') (hg : g =ᶜ g') : Prod.map f g =ᶜ Prod.map f' g' :=
  ⟨hf.subset fun ⟨_, _⟩ ⟨⟨_, _⟩, ⟨⟨a, _⟩, rfl⟩, h⟩ => ⟨a, h⟩,
   hg.subset fun ⟨_, _⟩ ⟨⟨_, _⟩, ⟨⟨_, c⟩, rfl⟩, h⟩ => ⟨c, h⟩⟩

variable [CoarseSpace γ] [CoarseSpace δ]
variable {f : X → Y} {g : γ → δ}

/-- A controlled map on each factor gives a controlled map on the product. -/
@[fun_prop]
theorem Controlled.prodMap (hf : Controlled f) (hg : Controlled g) :
    Controlled (Prod.map f g) := by
  intro E ⟨hE₁, hE₂⟩
  constructor
  · simpa only [Entourage.map_comp] using hf hE₁
  · simpa only [Entourage.map_comp] using hg hE₂

/-- A coarsely proper map on each factor gives a coarsely proper map on the product. -/
@[fun_prop]
theorem CoarselyProper.prodMap (hf : CoarselyProper f) (hg : CoarselyProper g) :
    CoarselyProper (Prod.map f g) := fun {s} hs ↦
  let T := Prod.map f g ⁻¹' s
  have hfst := isCoarselyBounded_image controlled_fst s hs
  have hsnd := isCoarselyBounded_image controlled_snd s hs
  have fst_sub : Prod.fst '' T ⊆ f ⁻¹' (Prod.fst '' s) :=
    image_subset_iff.mpr (preimage_mono (subset_preimage_image Prod.fst s))
  have snd_sub : Prod.snd '' T ⊆ g ⁻¹' (Prod.snd '' s) :=
    image_subset_iff.mpr (preimage_mono (subset_preimage_image Prod.snd s))
  ⟨(congrArg IsControlled (prodMap_image_prod _ _ _ _)).mpr
      ((hf hfst).isControlled.subset (prod_mono fst_sub fst_sub)),
   (congrArg IsControlled (prodMap_image_prod _ _ _ _)).mpr
      ((hg hsnd).isControlled.subset (prod_mono snd_sub snd_sub))⟩

/-- `Prod.map` of coarse maps is a coarse map. -/
@[fun_prop]
theorem Coarse.prodMap (hf : Coarse f) (hg : Coarse g) :
    Coarse (Prod.map f g) := {}

end Prod

/-! #### Product Associativity -/

section ProdAssoc

variable {γ : Type*} [CoarseSpace γ]

/-- The associativity map is a controlled map. -/
@[fun_prop]
theorem controlled_prodAssoc :
    Controlled (fun ⟨⟨a, b⟩, c⟩ => (a, b, c) : (X × Y) × γ → X × Y × γ) := by
  intro E ⟨hE₁, hE₂⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Entourage.map_comp] using hE₁.image_fst
  · simpa only [Entourage.map_comp] using hE₁.image_snd
  · simpa only [Entourage.map_comp] using hE₂

/-- The inverse associativity map is a controlled map. -/
@[fun_prop]
theorem controlled_prodAssoc_symm :
    Controlled (fun ⟨a, b, c⟩ => ((a, b), c) : X × Y × γ → (X × Y) × γ) := by
  intro E ⟨hE₁, hE₂, hE₃⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [Entourage.map_comp] using hE₁
  · simpa only [Entourage.map_comp] using hE₂
  · simpa only [Entourage.map_comp] using hE₃

/-- The associativity map is coarsely proper. -/
@[fun_prop]
theorem coarselyProper_prodAssoc :
    CoarselyProper (fun ⟨⟨a, b⟩, c⟩ => (a, b, c) : (X × Y) × γ → X × Y × γ) := fun {s} hs =>
  (isCoarselyBounded_image controlled_prodAssoc_symm s hs).subset
    fun ⟨⟨a, b⟩, c⟩ h => ⟨⟨a, b, c⟩, h, rfl⟩

/-- The inverse associativity map is coarsely proper. -/
@[fun_prop]
theorem coarselyProper_prodAssoc_symm :
    CoarselyProper (fun ⟨a, b, c⟩ => ((a, b), c) : X × Y × γ → (X × Y) × γ) := fun {s} hs =>
  (isCoarselyBounded_image controlled_prodAssoc s hs).subset
    fun ⟨a, b, c⟩ h => ⟨⟨⟨a, b⟩, c⟩, h, rfl⟩

/-- The associativity map is a coarse map. -/
@[fun_prop]
theorem coarse_prodAssoc :
    Coarse (fun ⟨⟨a, b⟩, c⟩ => (a, b, c) : (X × Y) × γ → X × Y × γ) := {}

/-- The inverse associativity map is a coarse map. -/
@[fun_prop]
theorem coarse_prodAssoc_symm :
    Coarse (fun ⟨a, b, c⟩ => ((a, b), c) : X × Y × γ → (X × Y) × γ) := {}

end ProdAssoc

end s

/-! ### Dependent Products -/

/-- Dependent product coarse structure on `∀ i, C i`. A set is controlled iff all projections
are controlled. -/
instance : CoarseSpace (∀ i, C i) where
  IsControlled        := fun s ↦ ∀ i, @IsControlled (C i) _ <| s.map (eval i)
  isControlled_subset := fun h ht i ↦ (h i).subset <| image_mono ht
  isControlled_union  := fun hs ht i ↦ map_union .. ▸ (hs i).union (ht i)
  isControlled_id     := fun i ↦ isControlled_id.subset <|
                                 image_subset_iff.mpr fun _ a ↦ congrFun a i
  isControlled_inv    := fun hs i ↦ map_inv .. ▸ (hs i).inv
  isControlled_comp   := fun hs ht i ↦ ((hs i).comp (ht i)).subset <| map_comp_subset ..

/-- A set in a dependent product is controlled iff all projections are controlled. -/
theorem isControlled_pi_iff {E : Entourage (∀ i, C i)} :
    IsControlled E ↔ (∀ i, IsControlled (E.map (eval i))) :=
  Iff.rfl

/-- The projection of a controlled set in a dependent product is controlled. -/
lemma IsControlled.map_eval {E : Entourage (∀ i, C i)} (hE : IsControlled E) (i : ι) :
    IsControlled (E.map (eval i)) :=
  isControlled_pi_iff.mp hE i

/-- A product of controlled entourages (one for each index) is controlled. -/
theorem IsControlled.pi (h : ∀ i, IsControlled (S i)) : IsControlled (pi S) :=
  isControlled_pi_iff.mp fun i ↦ (h i).subset (pi_map_eval_subset S i)

/-- For nonempty products, controlledness is equivalent to all factors being controlled. -/
theorem isControlled_pi_iff_of_nonempty (hne : (pi S).Nonempty) :
    IsControlled (pi S) ↔ ∀ i, IsControlled (S i) :=
  ⟨fun h i ↦ map_eval_pi hne i ▸ h.map_eval i, IsControlled.pi⟩

/-- Full characterization of when a dependent product of entourages is controlled. -/
theorem isControlled_pi :
    IsControlled (pi S) ↔ (∃ i, S i = ∅) ∨ ∀ i, IsControlled (S i) :=
  ⟨fun h ↦ (em (pi S).Nonempty).elim
     (fun hne ↦ .inr ((isControlled_pi_iff_of_nonempty hne).mp h))
     (fun hne ↦ .inl (pi_eq_empty_iff.mp (not_nonempty_iff_eq_empty.mp hne))),
   fun | .inl ⟨i, hi⟩ => (pi_eq_empty_iff.mpr ⟨i, hi⟩) ▸ isControlled_empty
       | .inr h => IsControlled.pi h⟩

/-- A set in a dependent product is coarsely bounded iff all its projections are. -/
theorem isCoarselyBounded_pi_iff {S : Set (∀ i, C i)} :
    IsCoarselyBounded S ↔ ∀ i, IsCoarselyBounded (eval i '' S) :=
  ⟨fun ⟨h⟩ i ↦ ⟨(h.map_eval i).subset fun _ ⟨⟨f, hf, ha⟩, ⟨g, hg, hb⟩⟩ ↦
     ⟨(f, g), ⟨hf, hg⟩, Prod.ext ha hb⟩⟩,
   fun h ↦ ⟨isControlled_pi_iff.mp fun i ↦ (h i).isControlled.subset
     fun _ ⟨⟨f, g⟩, ⟨hf, hg⟩, heq⟩ ↦ heq ▸ ⟨⟨f, hf, rfl⟩, ⟨g, hg, rfl⟩⟩⟩⟩

end CoarseSpace

/-! ### Type Synonyms -/

/-- `Additive X` inherits its coarse structure from `X`. -/
instance : CoarseSpace (Additive X) :=
  ‹CoarseSpace X›

/-- `Multiplicative X` inherits its coarse structure from `X`. -/
instance : CoarseSpace (Multiplicative X) :=
  ‹CoarseSpace X›

/-- The order dual `Xᵒᵈ` inherits its coarse structure from `X`. -/
instance : CoarseSpace Xᵒᵈ :=
  ‹CoarseSpace X›
