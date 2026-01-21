/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Restrict

import CoarseSpace.Defs

/-!
# Basic Properties of Coarse Spaces

This file develops the basic theory of coarse spaces, building on the definitions in
`CoarseSpace.Defs`.

## Main Results

### Closure properties of controlled entourages
* `IsControlled.subset`: Subsets of controlled entourages are controlled.
* `IsControlled.union`: Unions of controlled entourages are controlled.
* `IsControlled.inv`: Inverses of controlled entourages are controlled.
* `IsControlled.comp`: Compositions of controlled entourages are controlled.
* `IsControlled.pow`: Powers of controlled entourages are controlled.

### Closeness of maps
* `IsClose.refl`, `IsClose.symm`, `IsClose.trans`: Closeness is an equivalence relation.
* `IsClose.comp`: Closeness is preserved by precomposition.
* `IsClose.comp_left`: Closeness is preserved by postcomposition with controlled maps.

### Coarsely bounded sets
* `IsCoarselyBounded.subset`: Subsets of coarsely bounded sets are coarsely bounded.
* `isCoarselyBounded_of_exists`: A set is coarsely bounded if `s ×ˢ {x}` is controlled
  for some `x`.
* `isCoarselyBounded_preimage_of_isControlled`: Preimages under controlled entourages
  preserve coarse boundedness.
* `isCoarselyBounded_image`: Images under controlled maps preserve coarse boundedness.

### Coarse maps
* `Coarse.id`: The identity is a coarse map.
* `Coarse.comp`: Coarse maps are closed under composition.
* `coarse_of_isClose_id`: Maps close to the identity are coarse.

## Implementation Notes

The file establishes that `Empty`, `Unit`, and `PUnit` carry trivial coarse structures
where every entourage is controlled.

## References

* J. Roe, *Lectures on Coarse Geometry*, University Lecture Series 31, AMS, 2003
-/

open Set Entourage Function

universe u v w u₁

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type u₁}

namespace CoarseSpace

/-! ### Basic -/

@[ext (iff := false)]
protected theorem ext :
    ∀ {c c' : CoarseSpace X}, IsControlled[c] = IsControlled[c'] → c = c'
  | ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _, _, _⟩, rfl => rfl

variable [CoarseSpace X]

/-! ### Closure Properties of IsControlled -/

/-- A subset of a controlled entourage is controlled. -/
@[aesop safe apply]
theorem IsControlled.subset {E F : Entourage X} (hE : IsControlled E) (hF : F ⊆ E) :
    IsControlled F :=
  CoarseSpace.isControlled_subset hE hF

/-- The union of two controlled entourages is controlled. -/
@[aesop safe apply]
theorem IsControlled.union {E F : Entourage X} (hE : IsControlled E) (hF : IsControlled F) :
    IsControlled (E ∪ F) :=
  CoarseSpace.isControlled_union hE hF

/-- The inverse of a controlled entourage is controlled. -/
@[aesop safe apply]
theorem IsControlled.inv {E : Entourage X} (hE : IsControlled E) : IsControlled E⁻¹ :=
  CoarseSpace.isControlled_inv hE

/-- The composition of two controlled entourages is controlled. -/
@[aesop safe apply]
theorem IsControlled.comp {E F : Entourage X} (hE : IsControlled E) (hF : IsControlled F) :
    IsControlled (E ○ F) :=
  CoarseSpace.isControlled_comp hE hF

/-- Powers of controlled entourages are controlled. -/
theorem IsControlled.pow {E : Entourage X} (hE : IsControlled E) (n : ℕ) :
    IsControlled (E ^ n) := by
  induction n with
  | zero => exact isControlled_id
  | succ n ih => exact hE.comp ih

/-- The empty relation is controlled. -/
@[simp]
theorem isControlled_empty : IsControlled (∅ : Entourage X) :=
  isControlled_id.subset <| empty_subset Entourage.id

/-- The relation containing just the diagonal pair `(x, x)` is controlled. -/
@[simp]
theorem isControlled_diag_singleton (x : X) : IsControlled {(x, x)} :=
  isControlled_id.subset <| singleton_subset_iff.mpr rfl

/-- The supremum of a finite set of controlled entourages is controlled. -/
theorem isControlled_finset_sup (S : Finset (Entourage X))
    (hS : ∀ E ∈ S, IsControlled E) : IsControlled (S.sup id) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact isControlled_empty
  | insert E T hE ih =>
    simp only [Finset.sup_insert, _root_.id_eq]
    exact (hS _ (Finset.mem_insert_self _ _)).union
      (ih fun F hF => hS F (Finset.mem_insert_of_mem hF))

/-- The product `s ×ˢ t` is controlled if and only if `t ×ˢ s` is controlled. -/
theorem isControlled_prod_comm {s t : Set X} :
    IsControlled (s ×ˢ t) ↔ IsControlled (t ×ˢ s) := by
  constructor <;> intro h <;> simpa [SetRel.inv] using h.inv

/-- If `f =ᶜ id` and `E.map f` is controlled, then `E` is controlled. -/
theorem IsControlled.of_map_of_isClose_id {E : Entourage X} {f : X → X} (hf : f =ᶜ id)
    (hEf : IsControlled (E.map f)) : IsControlled E :=
  ((hf.inv.comp hEf).comp hf).subset (E.subset_graph_conj_map f)

/-- If `g ∘ f =ᶜ id` and `F.map g` is controlled, then `F.comap f` is controlled. -/
theorem IsControlled.of_comap_of_isClose_id {F : Entourage Y} {f : X → Y} {g : Y → X}
    (hgf : g ∘ f =ᶜ id) (hFg : IsControlled (F.map g)) :
    IsControlled (comap f F) :=
  ((hgf.inv.comp hFg).comp hgf).subset (F.comap_subset_graph_conj_map f g)

/-- If a set `s` is a ball, then there exists a point `x` such that
`IsControlled (s ×ˢ {x})`. -/
theorem isControlled_prod_singleton_of_exists_ball_eq (s : Set X) :
    (∃ E x, IsControlled E ∧ s = E.ball x) → ∃ x, IsControlled (s ×ˢ {x}) :=
  fun ⟨_, x, hE, hs⟩ ↦ ⟨x, hs ▸ hE.subset fun ⟨_, _⟩ ⟨hy, rfl⟩ ↦ hy⟩

/-- A set `s` has `s ×ˢ {x}` controlled for some `x` if and only if `s` is a ball
of some controlled entourage. -/
theorem isControlled_prod_singleton_iff_exists_ball_eq (s : Set X) :
    (∃ x, IsControlled (s ×ˢ {x})) ↔ ∃ E x, IsControlled E ∧ s = E.ball x :=
  ⟨fun ⟨x, h⟩ ↦ ⟨s ×ˢ {x}, x, h, (Set.ext fun _ ↦ and_iff_left rfl).symm⟩,
   isControlled_prod_singleton_of_exists_ball_eq s⟩

/-! ### Closeness of Maps

Two maps `f g : Y → X` are *close* if the set of pairs `{(f x, g x) | x : Y}` forms a
controlled entourage. This section establishes that closeness is an equivalence relation
and is preserved by pre- and post-composition.
-/

section IsClose

/-- Closeness is reflexive: every map is close to itself. -/
@[refl]
theorem IsClose.refl (f : Y → X) : f =ᶜ f :=
  isControlled_id.subset (fun _ ⟨_, h⟩ ↦ h ▸ rfl)

/-- Equal maps are close. -/
lemma isClose_of_eq {f g : Y → X} (h : f = g) : f =ᶜ g :=
  h ▸ IsClose.refl f

/-- Closeness is symmetric: if `f` is close to `g`, then `g` is close to `f`. -/
@[symm]
theorem IsClose.symm {f f₁ : Y → X} : f =ᶜ f₁ → f₁ =ᶜ f :=
  fun h ↦ h.inv.subset fun _ ⟨x, hx⟩ ↦ ⟨x, congrArg Prod.swap hx⟩

/-- Closeness is transitive: if `f` is close to `g` and `g` is close to `h`,
then `f` is close to `h`. -/
@[trans]
theorem IsClose.trans {f f₁ f₂ : Y → X} : f =ᶜ f₁ → f₁ =ᶜ f₂ → f =ᶜ f₂ :=
  fun hf hf₁ ↦ (hf.comp hf₁).subset fun _ ⟨a, ha⟩ ↦ ha ▸ ⟨f₁ a, ⟨a, rfl⟩, ⟨a, rfl⟩⟩

/-- Closeness is preserved by *precomposition*: if `f` is close to `g`,
then `f ∘ h` is close to `g ∘ h`. -/
@[aesop safe apply]
theorem IsClose.comp {f f₁ : Y → X} (f₂ : Z → Y) :
    f =ᶜ f₁ → f ∘ f₂ =ᶜ f₁ ∘ f₂ :=
  fun h ↦ h.subset <| propext range_subset_iff ▸ fun x ↦ ⟨f₂ x, rfl⟩

/-- Closeness is preserved by *postcomposition* with a controlled map:
if `f` is close to `g` and `h` is a controlled map, then `h ∘ f` is
close to `h ∘ g`. -/
@[aesop safe apply]
theorem IsClose.comp_left [CoarseSpace Z] [CoarseSpace W]
    {f f₁ : Y → Z} {g : Z → W} (h : f =ᶜ f₁) :
    Controlled g → g ∘ f =ᶜ g ∘ f₁ :=
  fun hg ↦ (congrArg IsControlled (range_comp _ _).symm).mp <| hg h

/-- Composing with the identity on the right preserves closeness. -/
@[simp]
theorem isClose_comp_id (f : Y → X) : f ∘ id =ᶜ f :=
  IsClose.refl (f ∘ id)

/-- Composing with the identity on the left preserves closeness. -/
@[simp]
theorem isClose_id_comp (f : Y → X) : id ∘ f =ᶜ f :=
  IsClose.refl (id ∘ f)

/-- If two maps are close when restricted to `s` and to `t`, and `s ∪ t`
covers the whole domain, then they are close on the whole domain. -/
theorem isClose_of_union {f f₁ : Y → X} {s t : Set Y} (h : ∀ x, x ∈ s ∪ t)
    (h₁ : s.restrict f =ᶜ s.restrict f₁)
    (h₂ : t.restrict f =ᶜ t.restrict f₁) : f =ᶜ f₁ :=
  (h₁.union h₂).subset fun _ ⟨x, hx⟩ ↦ hx ▸ (h x).elim
    (fun hs ↦ .inl ⟨⟨x, hs⟩, rfl⟩)
    (fun ht ↦ .inr ⟨⟨x, ht⟩, rfl⟩)

/-- If pullbacks of controlled relations along `f` are controlled, then any left inverse
of `f` is close to the identity when composed with `f`. -/
theorem isClose_id_of_leftInverse [CoarseSpace Y]
    {f : X → Y} {g : Y → X} (hfg : Function.LeftInverse f g)
    (hf : ∀ E : Entourage Y, IsControlled E → IsControlled (E.comap f)) :
    g ∘ f =ᶜ id :=
  (hf _ isControlled_id).subset fun _ a ↦ Exists.casesOn a fun x h ↦ h ▸ hfg (f x)

end IsClose

/-! ### Coarsely Bounded Sets

A set is coarsely bounded if its self-product `s ×ˢ s` is a controlled entourage—
intuitively, all points in the set are at bounded distance from each other.
-/

/-- The empty set is coarsely bounded. -/
@[simp]
theorem isCoarselyBounded_empty : IsCoarselyBounded (∅ : Set X) :=
  ⟨prod_empty ▸ isControlled_empty⟩

/-- Singleton sets are coarsely bounded. -/
@[simp]
theorem isCoarselyBounded_singleton (x : X) : IsCoarselyBounded {x} :=
  ⟨singleton_prod_singleton ▸ isControlled_diag_singleton x⟩

end CoarseSpace

/-- Subsets of coarsely bounded sets are coarsely bounded. -/
theorem IsCoarselyBounded.subset [CoarseSpace X] {s t : Set X}
    (hs : IsCoarselyBounded s) (ht : t ⊆ s) : IsCoarselyBounded t :=
  ⟨hs.isControlled.subset (Set.prod_mono ht ht)⟩

namespace CoarseSpace

variable [CoarseSpace X]

/-- If there exists a point `x` such that `s ×ˢ {x}` is a controlled relation,
then `s` is coarsely bounded. -/
@[aesop safe apply]
theorem isCoarselyBounded_of_exists (s : Set X) :
    (∃ x : X, IsControlled (s ×ˢ {x})) → IsCoarselyBounded s :=
  fun ⟨x, h⟩ ↦
    have : s ×ˢ s = (s ×ˢ {x}) ○ (s ×ˢ {x})⁻¹ :=
      Set.ext fun (_, _) ↦
        ⟨fun ⟨ha, hb⟩ ↦ ⟨x, ⟨ha, rfl⟩, hb, rfl⟩,
         fun ⟨_, ⟨ha, _⟩, hb, _⟩ ↦ ⟨ha, hb⟩⟩
    ⟨this ▸ h.comp h.inv⟩

/-- For a nonempty set `s`, coarse boundedness is equivalent to the existence of
a point `x` such that `s ×ˢ {x}` is controlled. -/
theorem isCoarselyBounded_nonempty_iff_exists {s : Set X} (hs : Nonempty s) :
    IsCoarselyBounded s ↔ ∃ x : X, IsControlled (s ×ˢ {x}) :=
  let ⟨x, hx⟩ := hs
  ⟨fun h ↦ ⟨x, h.isControlled.subset (Set.prod_mono Subset.rfl (singleton_subset_iff.mpr hx))⟩,
   isCoarselyBounded_of_exists s⟩

/-- Characterisation of coarse boundedness via closeness to a constant map:
for a nonempty set `s`, `s` is coarsely bounded iff the inclusion
`s → X` is close to some constant map. -/
theorem isCoarselyBounded_iff_isClose_const {s : Set X} (hs : Nonempty s) :
    IsCoarselyBounded s ↔ ∃ x : X, IsClose (fun (y : s) ↦ (y : X)) (Function.const _ x) :=
  (isCoarselyBounded_nonempty_iff_exists hs).trans <| exists_congr fun a ↦
    iff_of_eq <| congrArg IsControlled <| prod_singleton.trans (image_eq_range (·, a) s)

/-- The preimage of a coarsely bounded set by a controlled relation is
coarsely bounded. -/
@[aesop safe apply]
theorem isCoarselyBounded_preimage_of_isControlled {E : Entourage X} {s : Set X}
    (hE : IsControlled E) (hs : IsCoarselyBounded s) :
    IsCoarselyBounded (E.preimage s) :=
  have sub : E.preimage s ×ˢ E.preimage s ⊆ E ○ (s ×ˢ s) ○ E⁻¹ :=
    fun _ ⟨⟨y₁, hy₁, hx₁y₁⟩, ⟨y₂, hy₂, hx₂y₂⟩⟩ ↦
      ⟨y₂, ⟨y₁, hx₁y₁, hy₁, hy₂⟩, hx₂y₂⟩
  ⟨((hE.comp hs.isControlled).comp hE.inv).subset sub⟩

/-- The union of two coarsely bounded sets with nonempty intersection is
coarsely bounded. -/
theorem isCoarselyBounded.union' {s t : Set X}
    (hs : IsCoarselyBounded s) (ht : IsCoarselyBounded t) :
    (s ∩ t).Nonempty → IsCoarselyBounded (s ∪ t)
  | ⟨x₀, hx₀s, hx₀t⟩ =>
      isCoarselyBounded_of_exists _ ⟨x₀,
        (hs.isControlled.union ht.isControlled).subset fun ⟨_, _⟩ ⟨hab, hb⟩ ↦
          hab.elim (fun ha ↦ .inl ⟨ha, hb ▸ hx₀s⟩) (fun ha ↦ .inr ⟨ha, hb ▸ hx₀t⟩)⟩

/-- The image of a coarsely bounded set under a controlled map is coarsely bounded. -/
theorem isCoarselyBounded_image [CoarseSpace Y] {f : X → Y}
    (hf : Controlled f) (s : Set X) (hs : IsCoarselyBounded s) :
    IsCoarselyBounded (f '' s) :=
  ⟨prodMap_image_prod _ _ _ _ ▸ hf hs.isControlled⟩

/-- The ball of an inverse controlled entourage is coarsely bounded. -/
lemma isCoarselyBounded_ball_inv {F : Entourage X} (hF : IsControlled F) (x₀ : X) :
    IsCoarselyBounded (Entourage.ball F.inv x₀) := by
  simpa [Entourage.ball, SetRel.preimage] using
    isCoarselyBounded_preimage_of_isControlled hF.inv (isCoarselyBounded_singleton x₀)

/-! ### Coarse Maps

This section establishes basic properties of coarse maps: that the identity is a coarse map,
and that coarse maps are closed under composition. A coarse map is one that is both
coarsely proper (preimages of coarsely bounded sets are coarsely bounded) and
controlled (images of controlled entourages are controlled).
-/

end CoarseSpace

/-- The composition of controlled maps is a controlled map. -/
@[fun_prop]
theorem Controlled.comp [CoarseSpace X] [CoarseSpace Y] [CoarseSpace Z]
    {f : X → Y} {g : Y → Z} (hg : Controlled g) (hf : Controlled f) :
    Controlled (g ∘ f) :=
  fun hE ↦ (Entourage.map_comp f g _).symm ▸ hg (hf hE)

/-- The composition of coarsely proper maps is coarsely proper. -/
@[fun_prop]
theorem CoarselyProper.comp [CoarseSpace X] [CoarseSpace Y] [CoarseSpace Z]
    {f : X → Y} {g : Y → Z} (hg : CoarselyProper g) (hf : CoarselyProper f) :
    CoarselyProper (g ∘ f) :=
  fun h ↦ hf (hg h)

/-- The composition of coarse maps is a coarse map. -/
@[fun_prop]
theorem Coarse.comp [CoarseSpace X] [CoarseSpace Y] [CoarseSpace Z]
    {f : X → Y} {g : Y → Z} (hg : Coarse g) (hf : Coarse f) :
    Coarse (g ∘ f) := {}

namespace CoarseSpace

section Maps

variable [CoarseSpace X] [CoarseSpace Y] [CoarseSpace Z]

/-- The identity map is coarsely proper. -/
@[fun_prop]
theorem CoarselyProper.id : CoarselyProper (id : X → X) :=
  fun {_} a ↦ a

/-- The identity map is a controlled map. -/
@[fun_prop]
theorem Controlled.id : Controlled (id : X → X) :=
  fun hE ↦ Entourage.map_id _ ▸ hE

/-- The image of a subset of a controlled entourage under a controlled map is controlled. -/
theorem Controlled.subset {f : X → Y} (hf : Controlled f)
    {E F : Entourage X} (hE : IsControlled E) (hFE : F ⊆ E) :
    IsControlled (F.map f) :=
  (hf hE).subset (map_mono f hFE)

/-- The image of a controlled entourage under a controlled map is controlled. -/
theorem isControlled_map_of_isControlled {f : X → Y} {E : Entourage X}
    (hf : Controlled f) (hE : IsControlled E) :
    IsControlled (E.map f) :=
  hf hE

/-- The identity map is a coarse map. -/
@[fun_prop]
theorem Coarse.id : Coarse (id : X → X) := {}

/-- If a function has a left inverse which is a controlled map, then it is proper. -/
theorem coarselyProper_of_leftInverse {f : X → Y} {g : Y → X}
    (hfg : Function.LeftInverse g f) (hg : Controlled g) :
    CoarselyProper f := fun {s} hs ↦
  (isCoarselyBounded_image hg s hs).subset
    (preimage_subset_image_of_inverse hfg s)

/-- If pullbacks of controlled relations along `f` are controlled, then any left inverse
of `f` is a controlled map. -/
theorem controlled_of_leftInverse
    {f : X → Y} {g : Y → X} (hfg : Function.LeftInverse f g)
    (hf : ∀ E : Entourage Y, IsControlled E → IsControlled (E.comap f)) :
    Controlled g := fun {E} hE ↦
  have sub : E.map g ⊆ E.comap f := fun ⟨x, y⟩ ⟨⟨a, b⟩, hab, heq⟩ ↦
    let ⟨hx, hy⟩ := Prod.mk.inj heq
    show (f x, f y) ∈ E from
      have hfx : a = f x := (hfg a).symm.trans (congrArg f hx)
      have hfy : b = f y := (hfg b).symm.trans (congrArg f hy)
      hfx ▸ hfy ▸ hab
  (hf E hE).subset sub

/-- If `f : X → X` is close to `id`, then `f` is a coarse map. -/
theorem coarse_of_isClose_id {f : X → X} (hf : f =ᶜ id) : Coarse f where
  controlled' {E} hE :=
    let R : Entourage X := Set.range fun x : X ↦ (f x, x)
    let hR : IsControlled R := hf
    let hsub : E.map f ⊆ R ○ E ○ R⁻¹ := fun ⟨_, _⟩ ⟨⟨a, b⟩, hab, heq⟩ ↦
      have ⟨h1, h2⟩ := Prod.mk.inj heq
      h1 ▸ h2 ▸ ⟨b, ⟨a, ⟨a, rfl⟩, hab⟩, ⟨b, rfl⟩⟩
    ((hR.comp hE).comp hR.inv).subset hsub
  coarselyProper {s} hs :=
    let R : Entourage X := Set.range fun x : X ↦ (f x, x)
    let hR : IsControlled R := hf
    let hsub : f ⁻¹' s ⊆ R⁻¹.preimage s := fun x hx ↦
      SetRel.mem_preimage.mpr ⟨f x, hx, SetRel.mem_inv.mpr ⟨x, rfl⟩⟩
    (isCoarselyBounded_preimage_of_isControlled hR.inv hs).subset hsub

end Maps

/-! ### Coarsely Bounded Spaces -/

variable [CoarseSpace X]

section CoarselyBoundedSpace

/-- The universe is coarsely bounded in a coarsely bounded space. -/
theorem isCoarselyBounded_univ [CoarselyBoundedSpace X] :
    IsCoarselyBounded (Set.univ : Set X) :=
  CoarselyBoundedSpace.coarselyBounded_univ

/-- Every set is coarsely bounded in a coarsely bounded space. -/
theorem isCoarselyBounded [CoarselyBoundedSpace X] (s : Set X) : IsCoarselyBounded s :=
  isCoarselyBounded_univ.subset (Set.subset_univ s)

/-- In a coarsely bounded space, the entourage `univ × univ` is controlled. -/
theorem isControlled_univ [CoarselyBoundedSpace X] :
    IsControlled (Set.univ ×ˢ Set.univ : Entourage X) :=
  isCoarselyBounded_univ.isControlled

/-- A space is coarsely bounded iff `univ ×ˢ univ` is controlled. -/
theorem coarselyBoundedSpace_iff_isControlled_univ :
    CoarselyBoundedSpace X ↔ IsControlled (Set.univ ×ˢ Set.univ : Entourage X) :=
  ⟨fun _ => isControlled_univ, fun h => ⟨⟨h⟩⟩⟩

/-- Construct a `CoarselyBoundedSpace` instance from the fact that `univ ×ˢ univ` is controlled. -/
theorem of_isControlled_univ (h : IsControlled (Set.univ ×ˢ Set.univ : Entourage X)) :
    CoarselyBoundedSpace X :=
  ⟨⟨h⟩⟩

/-- If `f : X → Y` is surjective and controlled, and `X` is a coarsely bounded space,
then `Y` is a coarsely bounded space. -/
theorem of_surjective_controlled [CoarseSpace Y] [CoarselyBoundedSpace X] {f : X → Y}
    (hf_surj : Function.Surjective f) (hf : Controlled f) : CoarselyBoundedSpace Y :=
  ⟨hf_surj.range_eq ▸ Set.image_univ (f := f) ▸
    isCoarselyBounded_image hf Set.univ isCoarselyBounded_univ⟩

end CoarselyBoundedSpace

/-! ### Instances -/

/-- The coarse structure on `Empty`, where every entourage is controlled. -/
instance : CoarseSpace Empty where
  IsControlled _ := True
  isControlled_subset _ _ := trivial
  isControlled_union _ _ := trivial
  isControlled_id := trivial
  isControlled_inv _ := trivial
  isControlled_comp _ _ := trivial

/-- The coarse structure on `Unit`, where every entourage is controlled. -/
instance : CoarseSpace Unit where
  IsControlled _ := True
  isControlled_subset _ _ := trivial
  isControlled_union _ _ := trivial
  isControlled_id := trivial
  isControlled_inv _ := trivial
  isControlled_comp _ _ := trivial

/-- The coarse structure on `PUnit`, where every entourage is controlled. -/
instance : CoarseSpace PUnit where
  IsControlled _ := True
  isControlled_subset _ _ := trivial
  isControlled_union _ _ := trivial
  isControlled_id := trivial
  isControlled_inv _ := trivial
  isControlled_comp _ _ := trivial

/-! ### Type-Specific Lemmas -/

/-- Every entourage on `Empty` is controlled. -/
@[simp]
theorem isControlled_empty' (E : Entourage Empty) : IsControlled E := trivial

/-- Every entourage on `Unit` is controlled. -/
@[simp]
theorem isControlled_unit (E : Entourage Unit) : IsControlled E := trivial

/-- Every entourage on `PUnit` is controlled. -/
@[simp]
theorem isControlled_punit (E : Entourage PUnit) : IsControlled E := trivial

/-- Every set in `Empty` is coarsely bounded. -/
@[simp]
theorem isCoarselyBounded_empty' (s : Set Empty) : IsCoarselyBounded s := ⟨trivial⟩

/-- Every set in `Unit` is coarsely bounded. -/
@[simp]
theorem isCoarselyBounded_unit (s : Set Unit) : IsCoarselyBounded s := ⟨trivial⟩

/-- Every set in `PUnit` is coarsely bounded. -/
@[simp]
theorem isCoarselyBounded_punit (s : Set PUnit) : IsCoarselyBounded s := ⟨trivial⟩

/-- `Empty` is a coarsely bounded space. -/
instance instCoarselyBoundedSpaceEmpty : CoarselyBoundedSpace Empty :=
  ⟨isCoarselyBounded_empty' _⟩

/-- `Unit` is a coarsely bounded space. -/
instance instCoarselyBoundedSpaceUnit : CoarselyBoundedSpace Unit :=
  ⟨isCoarselyBounded_unit _⟩

/-- `PUnit` is a coarsely bounded space. -/
instance instCoarselyBoundedSpacePUnit : CoarselyBoundedSpace PUnit :=
  ⟨isCoarselyBounded_punit _⟩

/-- Any subsingleton type is a coarsely bounded space. -/
instance instCoarselyBoundedSpaceSubsingleton [Subsingleton X] : CoarselyBoundedSpace X :=
  of_isControlled_univ <| isControlled_id.subset fun ⟨x, y⟩ _ => Subsingleton.elim x y

end CoarseSpace
