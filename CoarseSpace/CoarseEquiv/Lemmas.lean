/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import Mathlib.Logic.Equiv.Fin.Basic

import CoarseSpace.CoarseEquiv.Defs
import CoarseSpace.Constructions
import CoarseSpace.Connected
import CoarseSpace.Finiteness

/-!
# Lemmas about coarse equivalences

This file contains lemmas about coarse equivalences between coarse spaces.

## Main results

### Coarse property preservation
* `CoarseEquiv.univ_subset_controlled_preimage_image`: A coarse equivalence is coarsely surjective.
* `CoarseEquiv.coarselyBoundedSpace`: A coarse equivalence transfers `CoarselyBoundedSpace`
  from domain to codomain.
* `CoarseEquiv.coarselyConnected`: A coarse equivalence transfers `CoarselyConnectedSpace`
  from domain to codomain.
* `CoarseEquiv.fg`: Finite generation is preserved by coarse equivalences.

### Set properties
* `CoarseEquiv.isCoarselyBounded_image`: The image of a set under a coarse equivalence is
  coarsely bounded iff the original set is.
* `CoarseEquiv.IsCoarselyBounded.preimage`: The preimage of a coarsely bounded set under
  a coarse equivalence is coarsely bounded.

### Entourage properties
* `CoarseEquiv.isControlled_image`: The image of an entourage under a coarse equivalence
  is controlled iff the original entourage is.
* `CoarseEquiv.isControlled_comap`: The comap of a controlled entourage under a coarse
  equivalence is controlled.

### Composition
* `CoarseEquiv.CoarselyProper.of_comp`: If `e ∘ f` is proper and `e` is a coarse
  equivalence, then `f` is proper.
* `CoarseEquiv.Controlled.of_comp`: If `e ∘ f` is controlled and `e` is a coarse
  equivalence, then `f` is controlled.
* `CoarseEquiv.Coarse.of_comp`: If `e ∘ f` is coarse and `e` is a coarse equivalence,
  then `f` is coarse.

### Product constructions
* `CoarseEquiv.prodComm`: The commutativity of products as a coarse equivalence.
* `CoarseEquiv.prodCoarselyBounded`: `X × Y ≃ᶜ X` when `Y` is coarsely bounded.
* `CoarseEquiv.prodCongr`: The product of two coarse equivalences.
* `CoarseEquiv.prodAssoc`: The associativity of products as a coarse equivalence.

## Notation

We use `e`, `e₁`, `e₂`, etc. for coarse equivalences, following the convention in
`CoarseEquiv.Defs`.
-/

open Set Function CoarseSpace Prod Entourage

variable {X Y Z W : Type*}

namespace CoarseEquiv

variable [CoarseSpace X] [CoarseSpace Y] [CoarseSpace Z] [CoarseSpace W]

/-! ### Controlled Entourage Properties -/

section EntourageProperties

variable {E : Entourage X} {F : Entourage Y}

/-- The image of an entourage under a coarse equivalence is controlled iff the entourage is. -/
@[simp]
theorem isControlled_image_iff (e : X ≃ᶜ Y) :
    IsControlled (E.map e) ↔ IsControlled E :=
  ⟨fun hEmap =>
    have hEf : IsControlled (E.map (e.invFun ∘ e)) :=
      E.map_comp e e.invFun ▸ e.coarse_symm.controlled hEmap
    IsControlled.of_map_of_isClose_id e.isClose_id_left hEf,
   e.coarse.controlled⟩

/-- Mapping an entourage by a coarse equivalence preserves controlledness. -/
theorem IsControlled.map_coarseEquiv (e : X ≃ᶜ Y) (hE : IsControlled E) :
    IsControlled (E.map e) :=
  e.isControlled_image_iff.mpr hE

end EntourageProperties

/-! ### Coarse Property Preservation -/

/-- A coarse equivalence is coarsely surjective: every point in the codomain is
within controlled distance of the image. -/
theorem univ_subset_controlled_preimage_image (e : X ≃ᶜ Y) :
    ∃ E : Entourage Y, IsControlled E ∧ Set.univ ⊆ E.preimage (e '' Set.univ) :=
  ⟨_, e.isClose_id_right.inv, fun y _ =>
    ⟨e (e.invFun y), ⟨e.invFun y, trivial, rfl⟩, ⟨y, rfl⟩⟩⟩

/-- A coarse equivalence transfers `CoarselyBoundedSpace` from domain to codomain. -/
theorem coarselyBoundedSpace [CoarselyBoundedSpace X] (e : X ≃ᶜ Y) : CoarselyBoundedSpace Y := by
  obtain ⟨E, hE, hsub⟩ := e.univ_subset_controlled_preimage_image
  exact ⟨(isCoarselyBounded_preimage_of_isControlled hE
    (isCoarselyBounded_image
    e.coarse.controlled _ isCoarselyBounded_univ)).subset hsub⟩

/-- A coarse equivalence transfers `CoarselyConnectedSpace` from domain to codomain. -/
theorem coarselyConnectedSpace [CoarselyConnectedSpace X] (e : X ≃ᶜ Y) :
    CoarselyConnectedSpace Y where
  isCoarselyConnected_univ := isCoarselyConnected_iff.mpr fun x _ y _ =>
    let ⟨_, hE, hE_mem⟩ := isCoarselyConnected_iff.mp isCoarselyConnected_univ
      (e.invFun x) trivial (e.invFun y) trivial
    ⟨_, e.isClose_id_right.inv.comp
    ((e.coarse_toFun.controlled hE).comp e.isClose_id_right),
      e (e.invFun x), SetRel.mem_inv.mpr ⟨x, rfl⟩,
      e (e.invFun y), mem_map_iff.mpr ⟨e.invFun x, e.invFun y, hE_mem, rfl, rfl⟩,
      ⟨y, rfl⟩⟩

/-- Finite generation is preserved by coarse equivalences. -/
theorem fg (e : X ≃ᶜ Y) [FG X] : FG Y := by
  -- Step 1: Get a symmetric generator E for the coarse structure on X
  let E := FG.getGenerator X
  -- Step 2: Define the closeness entourage G = {((e ∘ e⁻¹) x, x) | x ∈ Y}
  -- This measures how far e ∘ e⁻¹ is from the identity
  let G : Entourage Y := range fun x ↦ ((e ∘ e.symm) x, id x)
  have hG : IsControlled G := e.isClose_id_right
  -- Step 3: Construct the candidate generator F = G.symmetrize ∪ E.map e
  -- This combines the closeness data with the transported generator from X
  let F := G.symmetrize ∪ E.map e
  have hF : IsControlled F := (hG.union hG.inv).union
        (isControlled_map_of_isControlled e.coarse_toFun.controlled
        (FG.isControlled_getGenerator))
  have hF_symm : F.IsSymm := (symmetrize_isSymm G).union (map_of_isSymm FG.getGenerator_isSymm e)
  -- Step 4: Establish subset relations for later use
  have hG_sub : G ⊆ F := (subset_symmetrize G).trans subset_union_left
  have hG_inv_sub : G⁻¹ ⊆ F := (inv_subset_symmetrize G).trans subset_union_left
  have hEmap_sub : E.map e ⊆ F := subset_union_right
  -- Step 5: Show F generates the coarse structure on Y
  apply FG.of_single F fun H => ⟨fun hH => ?_, fun hH => ?_⟩
  -- Forward direction: F is controlled, so anything generated by {F} is controlled
  · exact generateFrom_le_iff_subset_controlled.mpr
          (fun _ h => Set.mem_singleton_iff.mp h ▸ Set.mem_setOf.mpr hF) H hH
  -- Backward direction: any controlled H on Y lies in some power of F
  · -- Transport H back to X via e⁻¹, then find n such that H.map e⁻¹ ⊆ Eⁿ
    obtain ⟨n, hn⟩ := FG.getGenerator_mem_pow (H.map e.symm)
          (isControlled_map_of_isControlled e.coarse_symm.controlled hH)
    -- The double-mapped image (H.map e⁻¹).map e lands in Fⁿ
    have hmid : (H.map e.symm).map e ⊆ F ^ n := calc
      (H.map e.symm).map e ⊆ (E ^ n).map e := map_mono e hn
      _ ⊆ (E.map e) ^ n := map_pow e E n
      _ ⊆ F ^ n := pow_mono hEmap_sub n
    -- Key decomposition: H ⊆ G⁻¹ ○ (H.map e⁻¹).map e ○ G
    -- For (x₁, x₂) ∈ H, we factor through the "approximate image" points y₁, y₂
    have hdecomp : H ⊆ G⁻¹ ○ (H.map e.invFun).map e ○ G := fun ⟨x₁, x₂⟩ h =>
      let y₁ := (e ∘ e.symm) x₁  -- the point "close to" x₁ in the image of e
      let y₂ := (e ∘ e.symm) x₂  -- the point "close to" x₂ in the image of e
      have hx₁_y₁ : (x₁, y₁) ∈ G⁻¹ := mem_range_self x₁
      have hy₂_x₂ : (y₂, x₂) ∈ G := mem_range_self x₂
      have hy₁_y₂ : (y₁, y₂) ∈ (H.map e.symm).map e :=
        mem_map_iff.mpr ⟨e.symm x₁, e.symm x₂,
          mem_map_iff.mpr ⟨x₁, x₂, h, rfl, rfl⟩, rfl, rfl⟩
      ⟨y₂, ⟨y₁, hx₁_y₁, hy₁_y₂⟩, hy₂_x₂⟩
    -- Combine: H ⊆ G⁻¹ ○ Fⁿ ○ G ⊆ F^(n+2) since G, G⁻¹ ⊆ F and F is symmetric
    have hHF : H ⊆ F ^ (n + 2) := calc
      H ⊆ G⁻¹ ○ (H.map e.symm).map e ○ G := hdecomp
      _ ⊆ G⁻¹ ○ F ^ n ○ G := comp_mono (comp_mono (Subset.refl _) hmid) (Subset.refl _)
      _ ⊆ F ^ (n + 2) := subset_pow_of_comp_pow_comp hF_symm hG_inv_sub hG_sub n
    -- Conclude: H is generated by {F}
    letI : CoarseSpace Y := generateFrom {F}
    exact (isControlled_generateFrom_of_mem <| mem_singleton F).pow (n + 2) |>.subset hHF

/-! ### Set Properties -/

section SetProperties

variable {s : Set X} {t : Set Y}

/-- The image of a set under a coarse equivalence is coarsely bounded iff the set is. -/
@[simp]
theorem isCoarselyBounded_image' (e : X ≃ᶜ Y) :
    IsCoarselyBounded (e '' s) ↔ IsCoarselyBounded s :=
  ⟨fun hs =>
    (isCoarselyBounded_preimage_of_isControlled e.isClose_id_left.inv
      (isCoarselyBounded_image e.coarse_symm.controlled _ hs)).subset
      fun x hx => ⟨e.invFun (e x), ⟨e x, ⟨x, hx, rfl⟩, rfl⟩, ⟨x, rfl⟩⟩,
   isCoarselyBounded_image e.coarse.controlled s⟩

/-- The image of a set under the inverse of a coarse equivalence is coarsely bounded
iff the set is. -/
@[simp]
theorem isCoarselyBounded_symm_image (e : X ≃ᶜ Y) :
    IsCoarselyBounded (e.symm '' t) ↔ IsCoarselyBounded t :=
  e.symm.isCoarselyBounded_image'

/-- The image of a coarsely bounded set under a coarse equivalence is coarsely bounded. -/
theorem IsCoarselyBounded.image (e : X ≃ᶜ Y) (hs : IsCoarselyBounded s) :
    IsCoarselyBounded (e '' s) :=
  e.isCoarselyBounded_image'.mpr hs

/-- The preimage of a coarsely bounded set under a coarse equivalence is coarsely bounded. -/
theorem IsCoarselyBounded.preimage (e : X ≃ᶜ Y) (ht : IsCoarselyBounded t) :
    IsCoarselyBounded (e ⁻¹' t) :=
  (isCoarselyBounded_preimage_of_isControlled e.isClose_id_left.inv
    (isCoarselyBounded_image e.coarse_symm.controlled t ht)).subset
    fun x hx => ⟨e.invFun (e x), ⟨e x, hx, rfl⟩, ⟨x, rfl⟩⟩

end SetProperties

/-! ### Composition with Coarse Equivalences -/

section Composition

variable {f : X → Y}

/-- If `e ∘ f` is a coarsely proper map and `e` is a coarse equivalence, then `f` is
coarsely proper. -/
theorem CoarselyProper.of_comp (e : Y ≃ᶜ Z)
    (hcomp : CoarselyProper (e ∘ f)) : CoarselyProper f :=
  fun {t} ht => (hcomp (e.isCoarselyBounded_image'.mpr ht)).subset
    (Set.preimage_mono (Set.subset_preimage_image e t))

/-- If `e ∘ f` is a controlled map and `e` is a coarse equivalence, then `f` is controlled. -/
theorem Controlled.of_comp (e : Y ≃ᶜ Z) {f : X → Y}
    (hcomp : Controlled (e ∘ f)) : Controlled f :=
  fun {F} hF => e.isControlled_image_iff.mp (F.map_comp f e ▸ hcomp hF)

/-- If `e ∘ f` is a coarse map and `e` is a coarse equivalence, then `f` is coarse. -/
theorem Coarse.of_comp (e : Y ≃ᶜ Z) {f : X → Y}
    (hcomp : Coarse (e ∘ f)) : Coarse f :=
  ⟨Controlled.of_comp e hcomp.controlled,
  CoarselyProper.of_comp e hcomp.coarselyProper⟩

/-- Composing a coarse map with a coarse equivalence on the right gives a coarse map. -/
theorem Coarse.comp_coarseEquiv (e : X ≃ᶜ Y) {g : Y → Z} (hg : Coarse g) :
    Coarse (g ∘ e) :=
  hg.comp e.coarse

end Composition

/-! ### Product Constructions -/

section Product

/-- The commutativity of products as a coarse equivalence: `X × Y ≃ᶜ Y × X`. -/
def prodComm (X Y : Type*) [CoarseSpace X] [CoarseSpace Y] : X × Y ≃ᶜ Y × X where
  toFun := Prod.swap
  invFun := Prod.swap
  coarse_toFun := coarse_swap
  coarse_invFun := coarse_swap
  isClose_id_right := isClose_of_eq (funext Prod.swap_swap)
  isClose_id_left := isClose_of_eq (funext Prod.swap_swap)

/-- The inverse of `prodComm X Y` is `prodComm Y X`: swapping twice is the identity. -/
@[simp]
theorem prodComm_symm (X Y : Type*) [CoarseSpace X] [CoarseSpace Y] :
    (prodComm X Y).symm = prodComm Y X :=
  rfl

/-- `X × Y` is coarsely equivalent to `X` when `Y` is a coarsely bounded space. -/
def prodCoarselyBounded (X : Type*) (Y : Type*) [CoarseSpace X] [CoarseSpace Y]
    [Inhabited Y] [CoarselyBoundedSpace Y] : X × Y ≃ᶜ X where
  toFun := Prod.fst
  invFun x := (x, default)
  coarse_toFun := coarse_fst
  coarse_invFun := coarse_prod_mk default
  isClose_id_right := IsClose.refl _
  isClose_id_left :=
    ⟨isControlled_id.subset fun _ ⟨_, ⟨⟨_, _⟩, rfl⟩, h⟩ =>
       (Prod.mk.inj h).1.symm.trans (Prod.mk.inj h).2,
     isCoarselyBounded_univ.isControlled.subset fun _ ⟨_, ⟨⟨_, _⟩, rfl⟩, _⟩ =>
       Set.mem_prod.mpr ⟨trivial, trivial⟩⟩

/-- `X × {*}` is coarsely equivalent to `X` when the second factor is a unique type. -/
def prodUnique (X : Type*) (Y : Type*) [CoarseSpace X] [CoarseSpace Y] [Unique Y] :
    X × Y ≃ᶜ X :=
  prodCoarselyBounded X Y

/-- The second component of `(prodUnique X Y).symm a` is the unique default element of `Y`. -/
@[simp]
theorem prodUnique_symm_apply_snd (X : Type*) (Y : Type*) [CoarseSpace X] [CoarseSpace Y]
    [Unique Y] (a : X) : ((prodUnique X Y).symm a).2 = default :=
  rfl

/-- The forward map of `prodUnique X Y` is projection onto the first component. -/
@[simp]
theorem coe_prodUnique (X : Type*) (Y : Type*) [CoarseSpace X] [CoarseSpace Y] [Unique Y] :
    ⇑(prodUnique X Y) = Prod.fst :=
  rfl

/-- `{*} × X` is coarsely equivalent to `X` when the first factor is a unique type. -/
def uniqueProd (X : Type*) (Y : Type*) [CoarseSpace X] [CoarseSpace Y] [Unique X] :
    X × Y ≃ᶜ Y :=
  (prodComm X Y).trans (prodUnique Y X)

/-- The forward map of `uniqueProd X Y` is projection onto the second component. -/
@[simp]
theorem coe_uniqueProd (X : Type*) (Y : Type*) [CoarseSpace X] [CoarseSpace Y] [Unique X] :
    ⇑(uniqueProd X Y) = Prod.snd :=
  rfl

/-- The product of two coarse equivalences: if `e₁ : X ≃ᶜ Y` and `e₂ : Z ≃ᶜ W`,
then `X × Z ≃ᶜ Y × W`. -/
def prodCongr (e₁ : X ≃ᶜ Y) (e₂ : Z ≃ᶜ W) : X × Z ≃ᶜ Y × W where
  toFun := Prod.map e₁ e₂
  invFun := Prod.map e₁.invFun e₂.invFun
  coarse_toFun := e₁.coarse.prodMap e₂.coarse
  coarse_invFun := e₁.coarse_symm.prodMap e₂.coarse_symm
  isClose_id_right := e₁.isClose_id_right.prodMap e₂.isClose_id_right
  isClose_id_left := e₁.isClose_id_left.prodMap e₂.isClose_id_left

/-- Evaluating the product of two coarse equivalences applies each equivalence componentwise. -/
@[simp]
theorem prodCongr_apply (e₁ : X ≃ᶜ Y) (e₂ : Z ≃ᶜ W) (x : X × Z) :
    e₁.prodCongr e₂ x = (e₁ x.1, e₂ x.2) :=
  rfl

/-- The inverse of a product of coarse equivalences is the product of their inverses:
`(e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm`. -/
@[simp]
theorem prodCongr_symm (e₁ : X ≃ᶜ Y) (e₂ : Z ≃ᶜ W) :
    (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm :=
  rfl

/-- The associativity of products as a coarse equivalence: `(X × Y) × Z ≃ᶜ X × (Y × Z)`. -/
def prodAssoc (X Y Z : Type*) [CoarseSpace X] [CoarseSpace Y] [CoarseSpace Z] :
    (X × Y) × Z ≃ᶜ X × Y × Z where
  toFun := fun ⟨⟨a, b⟩, c⟩ => (a, b, c)
  invFun := fun ⟨a, b, c⟩ => ((a, b), c)
  coarse_toFun := coarse_prodAssoc
  coarse_invFun := coarse_prodAssoc_symm
  isClose_id_right := IsClose.refl _
  isClose_id_left := IsClose.refl _

end Product

end CoarseEquiv
