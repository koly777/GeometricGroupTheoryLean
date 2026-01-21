/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rel

/-!
# Entourages for Coarse Spaces

This file defines `Entourage α` as an abbreviation for `SetRel α α`, inheriting the full
`SetRel` API while providing coarse-geometry-specific definitions and notation.

## Main definitions

* `Entourage α` : Abbreviation for `SetRel α α`
* `Entourage.ball` : The coarse ball `{y | (y, x) ∈ E}`
* `Entourage.map` : Push forward an entourage through `f : α → β`
* `Entourage.prod` : Product of entourages (with an `SProd` instance for `×ˢ`)
* `Entourage.pi` : Pi product of entourages
* `Entourage.symmetrize` : Symmetrization `E ∪ E⁻¹`

## Notation

* `E ○ F` : Composition (scoped to `CoarseSpace`)
* `E⁻¹` : Inverse (scoped to `CoarseSpace`)
* `E ×ˢ F` : Product (via `SProd` instance)
* `E ^ n` : n-fold composition (via `HPow` instance)

## Main results

* `map_comap_of_surjective` : For surjective functions, map and comap are inverses

## Implementation notes

We use `abbrev` so that all `SetRel` lemmas apply directly.

## Tags

entourage, coarse space, coarse geometry, relation
-/

open Set Function

variable {α β γ ι : Type*} {X : ι → Type*}

/-- An entourage on `α` is a binary relation on `α`, used to define coarse structures. -/
abbrev Entourage (α : Type*) := SetRel α α

namespace Entourage

/-! ### Notation

We introduce scoped notation for composition (`○`) and inverse (`⁻¹`) of entourages.
These mirror the standard operations on relations but are scoped to avoid conflicts.
-/

scoped[Entourage] infixl:55 " ○ " => SetRel.comp
scoped[Entourage] postfix:max "⁻¹" => SetRel.inv

/-! ### Basic

Core definitions for entourages: the identity entourage and basic membership characterization.
-/

/-- The identity entourage, consisting of all diagonal pairs `(x, x)`. -/
protected abbrev id : Entourage α := SetRel.id

/-- The identity entourage equals `SetRel.id`. -/
@[simp] theorem id_eq : (Entourage.id : Entourage α) = SetRel.id := rfl

/-- Membership in the identity entourage is equivalent to having equal components. -/
theorem mem_id {x : α × α} : x ∈ Entourage.id ↔ x.1 = x.2 := by
 simp only [id_eq]
 obtain ⟨fst, snd⟩ := x
 simp_all only [SetRel.mem_id]

/-! ### Composition

Monotonicity and basic properties of entourage composition.
-/

/-- Composition of entourages is monotone in both arguments. -/
theorem comp_mono {E₁ E₂ F₁ F₂ : Entourage α} (h₁ : E₁ ⊆ E₂) (h₂ : F₁ ⊆ F₂) :
    E₁ ○ F₁ ⊆ E₂ ○ F₂ :=
  fun _ ⟨z, hz₁, hz₂⟩ => ⟨z, h₁ hz₁, h₂ hz₂⟩

/-! ### Ball

The coarse ball `E.ball x` consists of all points `y` such that `(y, x) ∈ E`.
Note that the convention here is that `y` is in the ball centered at `x` if `(y, x) ∈ E`,
which corresponds to `y` being "close to" `x` as measured by the entourage `E`.
-/

/-- The ball of radius `E` centered at `x`: the set `{y | (y, x) ∈ E}` -/
def ball (E : Entourage α) (x : α) : Set α := {y | (y, x) ∈ E}

/-- Membership in a ball is equivalent to the pair being in the entourage. -/
@[simp]
theorem mem_ball_iff {E : Entourage α} {x y : α} : y ∈ E.ball x ↔ (y, x) ∈ E := Iff.rfl

/-- The ball of the empty entourage is empty. -/
@[simp]
theorem ball_empty (x : α) : (∅ : Entourage α).ball x = ∅ := rfl

/-- The ball of the identity entourage is the singleton. -/
@[simp]
theorem ball_id (x : α) : ball Entourage.id x = {x} := by ext y; simp [ball]

/-- Balls are monotone in the entourage. -/
@[gcongr]
theorem ball_mono {E F : Entourage α} (h : E ⊆ F) (x : α) : E.ball x ⊆ F.ball x :=
  fun _ hy => h hy

/-- The ball of a union is the union of balls. -/
theorem ball_union (E F : Entourage α) (x : α) : (E ∪ F).ball x = E.ball x ∪ F.ball x := rfl

/-- The ball of an intersection is contained in the intersection of balls. -/
theorem ball_inter_subset (E F : Entourage α) (x : α) :
    (E ∩ F).ball x ⊆ E.ball x ∩ F.ball x := fun _ ⟨hy, hz⟩ => ⟨hy, hz⟩

/-- The ball of a composition is the preimage of the inner ball under the outer entourage. -/
theorem ball_comp (E F : Entourage α) (x : α) : ball (E ○ F) x = E.preimage (F.ball x) := by
   ext y
   simp only [mem_ball_iff, SetRel.mem_comp, SetRel.mem_preimage]
   simp_rw [and_comm]

/-- Membership in the ball of an inverse swaps the center and the point. -/
theorem mem_ball_inv {E : Entourage α} {x y : α} : y ∈ ball E⁻¹ x ↔ x ∈ E.ball y := by
  simp [ball, SetRel.mem_inv]

/-- Every point belongs to its own ball for a reflexive entourage. -/
theorem mem_ball_self {E : Entourage α} (hE : E.IsRefl) (x : α) : x ∈ ball E x :=
  -- Uses that IsRefl gives (x, x) ∈ E for all x
  SetRel.rfl E

/-- The ball of a reflexive entourage is always nonempty. -/
theorem ball_nonempty {E : Entourage α} (hE : E.IsRefl) (x : α) : (E.ball x).Nonempty :=
  ⟨x, mem_ball_self hE x⟩

/-- For a symmetric entourage, the ball equals the ball of the inverse. -/
theorem ball_inv {E : Entourage α} (hE : E.IsSymm) (x : α) : ball E x = ball E⁻¹ x := by
  ext y; simp [ball]

/-! ### Map

The map operation pushes forward an entourage through a function `f : α → β`.
Given an entourage `E` on `α`, the mapped entourage `E.map f` on `β` contains
all pairs `(f a, f b)` where `(a, b) ∈ E`. This is the image of `E` under `f × f`.
-/

/-- Push forward an entourage through a function on both coordinates. -/
def map (f : α → β) (E : Entourage α) : Entourage β := Prod.map f f '' E

theorem map_def {f : α → β} {E : Entourage α} : E.map f = Prod.map f f '' E := rfl

/-- Characterization of membership in a mapped entourage. -/
@[simp]
theorem mem_map {f : α → β} {E : Entourage α} {p : β × β} :
    p ∈ E.map f ↔ ∃ q ∈ E, (f q.1, f q.2) = p := Iff.rfl

/-- Explicit characterization of membership in a mapped entourage using coordinates. -/
theorem mem_map_iff {f : α → β} {E : Entourage α} {x y : β} :
    (x, y) ∈ E.map f ↔ ∃ a b, (a, b) ∈ E ∧ f a = x ∧ f b = y := by
  simp only [mem_map, Prod.exists, Prod.mk.injEq]

/-- Mapping by the identity function is the identity. -/
@[simp]
theorem map_id (E : Entourage α) : E.map _root_.id = E := Set.image_id' E

/-- Mapping is functorial: `map g ∘ map f = map (g ∘ f)`. -/
theorem map_comp (f : α → β) (g : β → γ) (E : Entourage α) :
    (E.map f).map g = E.map (g ∘ f) := by rw [map, map, ← Set.image_comp]; rfl

/-- Mapping is monotone in the entourage. -/
@[gcongr]
theorem map_mono {E F : Entourage α} (f : α → β) (h : E ⊆ F) : E.map f ⊆ F.map f :=
  Set.image_mono h

/-- Mapping the empty entourage gives the empty entourage. -/
@[simp]
theorem map_empty (f : α → β) : (∅ : Entourage α).map f = ∅ := Set.image_empty _

/-- Mapping distributes over union. -/
@[simp]
theorem map_union (f : α → β) (E F : Entourage α) : (E ∪ F).map f = E.map f ∪ F.map f :=
  Set.image_union _ _ _

/-- Mapping commutes with taking inverses. -/
theorem map_inv (E : Entourage α) (f : α → β) : map f (E⁻¹) = (E.map f)⁻¹ := by
  ext ⟨x, y⟩
  simp only [mem_map, SetRel.mem_inv, Prod.exists]
  constructor <;> rintro ⟨a, b, hab, h⟩ <;> cases h <;> exact ⟨b, a, hab, rfl⟩

/-- The map of a composition is contained in the composition of maps. -/
theorem map_comp_subset (E F : Entourage α) (f : α → β) :
  map f (E ○ F) ⊆ E.map f ○ F.map f := by
  rintro ⟨a, b⟩ ⟨⟨x, y⟩, ⟨z, hxz, hzy⟩, h⟩
  cases h
  exact ⟨f z, ⟨(x, z), hxz, rfl⟩, ⟨(z, y), hzy, rfl⟩⟩

/-- For injective functions, mapping preserves composition exactly. -/
theorem map_comp_of_injective {f : α → β} (hf : Injective f) (E F : Entourage α) :
    map f (E ○ F) = E.map f ○ F.map f :=
  (map_comp_subset E F f).antisymm fun ⟨x, y⟩ ⟨_, ⟨⟨a, c⟩, hac, hx⟩, ⟨⟨d, e⟩, hde, hy⟩⟩ ↦
    have hcd : c = d := hf ((Prod.mk.inj hx).2.trans (Prod.mk.inj hy).1.symm)
    show (x, y) ∈ map f (E ○ F) from
      ⟨⟨a, e⟩, ⟨d, hcd ▸ hac, hde⟩, Prod.ext (Prod.mk.inj hx).1 (Prod.mk.inj hy).2⟩

/-- An entourage is contained in the conjugate of its image by the graph of `f`.
This is useful for showing that `f` is close to the identity in the coarse sense. -/
theorem subset_graph_conj_map (E : Entourage α) (f : α → α) :
    E ⊆ (range fun x => (f x, x))⁻¹ ○ (E.map f) ○ (range fun x => (f x, x)) :=
  fun ⟨a, b⟩ hab => ⟨f b, ⟨f a, ⟨a, rfl⟩, ⟨(a, b), hab, rfl⟩⟩, ⟨b, rfl⟩⟩

/-- Characterization of membership in the ball of an inverse. -/
lemma mem_ball_inv_iff {F : Entourage α} {x₀ y : α} :
    y ∈ Entourage.ball F.inv x₀ ↔ (x₀, y) ∈ F :=
  Entourage.mem_ball_iff.trans SetRel.mem_inv


/-! ### Comap (pullback)

The comap operation pulls back an entourage through a function `f : α → β`.
Given an entourage `E` on `β`, the pulled-back entourage `E.comap f` on `α` contains
all pairs `(a, b)` such that `(f a, f b) ∈ E`. This is the preimage of `E` under `f × f`.

The comap is the right adjoint to map: `E.map f ⊆ F ↔ E ⊆ F.comap f`.
-/

/-- Pull back an entourage through a function on both coordinates. -/
def comap (f : α → β) (E : Entourage β) : Entourage α := Prod.map f f ⁻¹' E

/-- Characterization of membership in a pulled-back entourage. -/
@[simp]
theorem mem_comap {f : α → β} {E : Entourage β} {p : α × α} :
    p ∈ E.comap f ↔ (f p.1, f p.2) ∈ E := Iff.rfl

/-- Pulling back by the identity function is the identity. -/
@[simp]
theorem comap_id (E : Entourage α) : E.comap id = E := rfl

/-- Comap is contravariantly functorial: `comap f ∘ comap g = comap (g ∘ f)`. -/
theorem comap_comp (f : α → β) (g : β → γ) (E : Entourage γ) :
    E.comap (g ∘ f) = (E.comap g).comap f := rfl

/-- Pulling back the empty entourage gives the empty entourage. -/
@[simp]
theorem comap_empty (f : α → β) : (∅ : Entourage β).comap f = ∅ := rfl

/-- Comap is monotone in the entourage. -/
@[gcongr]
theorem comap_mono {E F : Entourage β} (f : α → β) (h : E ⊆ F) : E.comap f ⊆ F.comap f :=
    Set.preimage_mono h

/-- Comap distributes over union. -/
theorem comap_union (f : α → β) (E F : Entourage β) : (E ∪ F).comap f = E.comap f ∪ F.comap f := rfl

/-- Comap commutes with taking inverses. -/
theorem comap_inv (f : α → β) (E : Entourage β) : comap f E⁻¹ = (E.comap f)⁻¹ := rfl

/-- The map-comap composition contracts: `(E.comap f).map f ⊆ E`. -/
theorem map_comap_le (f : α → β) (E : Entourage β) : (E.comap f).map f ⊆ E := by
  rintro ⟨_, _⟩ ⟨⟨a, b⟩, hab, ⟨rfl, rfl⟩⟩
  exact hab

/-- The comap-map composition expands: `E ⊆ (E.map f).comap f`. -/
theorem comap_map_le (f : α → β) (E : Entourage α) : E ⊆ (E.map f).comap f := by
  intro ⟨a, b⟩ hab; exact ⟨⟨a, b⟩, hab, rfl⟩

/-- For surjective functions, map and comap are inverses. -/
theorem map_comap_of_surjective {f : α → β} (hf : Function.Surjective f) (E : Entourage β) :
    (E.comap f).map f = E := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl, rfl⟩; exact hab
  · intro hxy
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    exact ⟨⟨a, b⟩, hxy, rfl⟩

/-- A comap is contained in the conjugate of the corresponding map by the graph of `g ∘ h`.
This is useful for relating pullbacks and pushforwards via a section `g`. -/
theorem comap_subset_graph_conj_map (F : Entourage β) (f : α → β) (g : β → α) :
    F.comap f ⊆ (range fun x => (g (f x), x))⁻¹ ○ (F.map g) ○ (range fun x => (g (f x), x)) :=
  fun ⟨a, b⟩ hab => ⟨g (f b), ⟨g (f a), ⟨a, rfl⟩, ⟨(f a, f b), hab, rfl⟩⟩, ⟨b, rfl⟩⟩

theorem comap_comp_subset (f : α → β) (E F : Entourage β) :
    (E.comap f) ○ (F.comap f) ⊆ comap f (E ○ F) :=
  fun ⟨_, _⟩ ⟨c, hac, hcb⟩ => ⟨f c, hac, hcb⟩

lemma comap_comp_eq_of_surjective (f : α → β) (hf : Function.Surjective f)
    (E F : Entourage β) : comap f (E ○ F) = (E.comap f) ○ (F.comap f) := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨y, hay, hyb⟩
      obtain ⟨c, rfl⟩ := hf y
      exact ⟨c, hay, hyb⟩
    · exact fun h ↦ comap_comp_subset f E F h

/-! ### Product

The product of entourages `E` on `α` and `F` on `β` gives an entourage on `α × β`.
A pair `((a₁, b₁), (a₂, b₂))` is in `E ×ˢ F` iff `(a₁, a₂) ∈ E` and `(b₁, b₂) ∈ F`.

We provide an `SProd` instance so that `E ×ˢ F` notation works.
-/

/-- Product of two entourages. -/
protected def prod (E : Entourage α) (F : Entourage β) : Entourage (α × β) :=
  {p | (p.1.1, p.2.1) ∈ E ∧ (p.1.2, p.2.2) ∈ F}

/-- `SProd` instance for entourage product notation `E ×ˢ F`. -/
instance : SProd (Entourage α) (Entourage β) (Entourage (α × β)) where
  sprod := Entourage.prod

/-- Characterization of membership in a product entourage (using `×ˢ` notation). -/
@[simp]
theorem mem_sprod {E : Entourage α} {F : Entourage β} {p : (α × β) × (α × β)} :
    p ∈ E ×ˢ F ↔ (p.1.1, p.2.1) ∈ E ∧ (p.1.2, p.2.2) ∈ F := Iff.rfl

/-- The product of identity entourages is the identity entourage. -/
@[simp]
theorem sprod_id_id :
    (SetRel.id : Entourage α) ×ˢ (SetRel.id : Entourage β) = SetRel.id := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩; simp only [mem_sprod, SetRel.mem_id, Prod.mk.injEq]

/-- Product with empty on the left is empty. -/
@[simp]
theorem sprod_empty_left (F : Entourage β) : (∅ : Entourage α) ×ˢ F = ∅ := by
  ext ⟨⟨_, _⟩, ⟨_, _⟩⟩; simp

/-- Product with empty on the right is empty. -/
@[simp]
theorem sprod_empty_right (E : Entourage α) : E ×ˢ (∅ : Entourage β) = ∅ := by
  ext ⟨⟨_, _⟩, ⟨_, _⟩⟩; simp

/-- Inverse distributes over product. -/
@[simp]
theorem sprod_inv (E : Entourage α) (F : Entourage β) : (E ×ˢ F)⁻¹ = E⁻¹ ×ˢ F⁻¹ := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩; simp only [SetRel.mem_inv, mem_sprod]

/-- Composition distributes over product. -/
theorem sprod_comp (E₁ E₂ : Entourage α) (F₁ F₂ : Entourage β) :
    (E₁ ×ˢ F₁) ○ (E₂ ×ˢ F₂) = (E₁ ○ E₂) ×ˢ (F₁ ○ F₂) := by
  ext ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩
  simp only [SetRel.mem_comp, mem_sprod, Prod.exists]
  tauto

/-- Product is monotone in both arguments. -/
@[gcongr]
theorem sprod_mono {E E' : Entourage α} {F F' : Entourage β} (hE : E ⊆ E') (hF : F ⊆ F') :
    E ×ˢ F ⊆ E' ×ˢ F' := fun _ ⟨h1, h2⟩ => ⟨hE h1, hF h2⟩

/-- Product distributes over union on the left. -/
theorem sprod_union_left (E E' : Entourage α) (F : Entourage β) :
    (E ∪ E') ×ˢ F = E ×ˢ F ∪ E' ×ˢ F := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩; simp only [mem_sprod, mem_union]; tauto

/-- Product distributes over union on the right. -/
theorem sprod_union_right (E : Entourage α) (F F' : Entourage β) :
    E ×ˢ (F ∪ F') = E ×ˢ F ∪ E ×ˢ F' := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩; simp only [mem_sprod, mem_union]; tauto

/-- A product entourage is nonempty iff both factors are nonempty. -/
theorem sprod_nonempty {E : Entourage α} {F : Entourage β} :
    (E ×ˢ F).Nonempty ↔ E.Nonempty ∧ F.Nonempty := by
  constructor
  · rintro ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, hE, hF⟩; exact ⟨⟨(a, c), hE⟩, ⟨(b, d), hF⟩⟩
  · rintro ⟨⟨⟨a, b⟩, hab⟩, ⟨⟨c, d⟩, hcd⟩⟩; exact ⟨((a, c), (b, d)), hab, hcd⟩

/-- The first projection of a product entourage is the first factor (when second is nonempty). -/
theorem map_fst_sprod (E : Entourage α) (F : Entourage β) (hF : F.Nonempty) :
    (E ×ˢ F).map Prod.fst = E := by
  ext ⟨x, y⟩
  obtain ⟨⟨c, d⟩, hcd⟩ := hF
  simp only [mem_map, mem_sprod]
  constructor
  · rintro ⟨p, ⟨hab, _⟩, h⟩; cases h; exact hab
  · intro hxy; exact ⟨((x, c), (y, d)), ⟨hxy, hcd⟩, rfl⟩

/-- The second projection of a product entourage is the second factor (when first is nonempty). -/
theorem map_snd_sprod (E : Entourage α) (F : Entourage β) (hE : E.Nonempty) :
    (E ×ˢ F).map Prod.snd = F := by
  ext ⟨x, y⟩
  obtain ⟨⟨a, b⟩, hab⟩ := hE
  simp only [mem_map, mem_sprod]
  constructor
  · rintro ⟨p, ⟨_, hcd⟩, h⟩; cases h; exact hcd
  · intro hxy; exact ⟨((a, x), (b, y)), ⟨hab, hxy⟩, rfl⟩

/-- Composition of `E ×ˢ id` and `id ×ˢ F` gives `E ×ˢ F`.
This shows that the product structure can be built from "horizontal" and "vertical" moves. -/
theorem sprod_id_comp_id_sprod (E : Entourage α) (F : Entourage β) :
    (E ×ˢ Entourage.id) ○ (Entourage.id ×ˢ F) = E ×ˢ F := by
  ext ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩
  simp only [SetRel.mem_comp, mem_sprod, Entourage.mem_id]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, rfl⟩, ⟨rfl, hb⟩⟩; exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩; exact ⟨⟨a2, b1⟩, ⟨ha, rfl⟩, ⟨rfl, hb⟩⟩

/-- The first projection of `E ×ˢ id` is `E`. -/
theorem map_fst_sprod_id [Nonempty β] (E : Entourage α) :
    (E ×ˢ Entourage.id (α := β)).map Prod.fst = E := by
  ext ⟨x, y⟩
  simp only [mem_map, mem_sprod, mem_id, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, c, d, ⟨h, rfl⟩, rfl, rfl⟩; exact h
  · intro h
    obtain ⟨b⟩ := ‹Nonempty β›
    exact ⟨x, b, y, b, ⟨h, rfl⟩, rfl, rfl⟩

/-- The second projection of `E ×ˢ id` is contained in `id`. -/
theorem map_snd_sprod_id_subset (E : Entourage α) :
    (E ×ˢ Entourage.id (α := β)).map Prod.snd ⊆ Entourage.id :=
  fun ⟨_, _⟩ ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, h⟩, rfl⟩ => h

/-- The first projection of `id ×ˢ F` is contained in `id`. -/
theorem map_fst_id_sprod_subset (F : Entourage β) :
    (Entourage.id (α := α) ×ˢ F).map Prod.fst ⊆ Entourage.id :=
  fun ⟨_, _⟩ ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨h, _⟩, rfl⟩ => h

/-- The second projection of `id ×ˢ F` is `F`. -/
theorem map_snd_id_sprod [Nonempty α] (F : Entourage β) :
    (Entourage.id (α := α) ×ˢ F).map Prod.snd = F := by
  ext ⟨x, y⟩
  simp only [mem_map, mem_sprod, mem_id, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, c, d, ⟨rfl, h⟩, rfl, rfl⟩; exact h
  · intro h
    obtain ⟨a⟩ := ‹Nonempty α›
    exact ⟨a, x, a, y, ⟨rfl, h⟩, rfl, rfl⟩

/-- Any entourage on a product is contained in the product of its coordinate projections.
This provides an upper bound for entourages in terms of their "shadows". -/
theorem subset_sprod_map_fst_snd (E : Entourage (α × β)) :
    E ⊆ (E.map Prod.fst) ×ˢ (E.map Prod.snd) :=
  fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ h => ⟨⟨_, h, rfl⟩, ⟨_, h, rfl⟩⟩

/-- The ball of a product entourage is the product of balls. -/
theorem ball_sprod (E : Entourage α) (F : Entourage β) (x : α) (y : β) :
    (E ×ˢ F).ball (x, y) = E.ball x ×ˢ F.ball y := by
  ext ⟨a, b⟩; simp only [mem_ball_iff, mem_sprod, Set.mem_prod, mem_ball_iff]

/-- The product of reflexive entourages is reflexive. -/
theorem IsRefl.sprod {E : Entourage α} {F : Entourage β}
    (hE : E.IsRefl) (hF : F.IsRefl) : (E ×ˢ F).IsRefl :=
    ⟨fun _ ↦ ⟨SetRel.rfl E, SetRel.rfl F⟩⟩

/-- The product of symmetric entourages is symmetric. -/
theorem IsSymm.sprod {E : Entourage α} {F : Entourage β}
    (hE : E.IsSymm) (hF : F.IsSymm) : (E ×ˢ F).IsSymm :=
  ⟨fun _ _ ⟨h₁, h₂⟩ ↦ ⟨SetRel.symm E h₁, SetRel.symm F h₂⟩⟩

/-- The product of transitive entourages is transitive. -/
theorem IsTrans.sprod {E : Entourage α} {F : Entourage β}
    (hE : E.IsTrans) (hF : F.IsTrans) : (E ×ˢ F).IsTrans :=
    ⟨fun _ _ _ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ ↦ ⟨SetRel.trans E h₁ h₃, SetRel.trans F h₂ h₄⟩⟩

/-! ### Pi

The pi product of a family of entourages `E : ∀ i, Entourage (X i)` gives an entourage
on `∀ i, X i`. A pair `(f, g)` is in `pi E` iff for all `i`, `(f i, g i) ∈ E i`.

This generalizes the binary product to arbitrary indexed families.
-/

/-- Pi product of a family of entourages. A pair of functions is related iff they are
related coordinate-wise. -/
def pi (E : ∀ i, Entourage (X i)) : Entourage (∀ i, X i) :=
  {p | ∀ i, (p.1 i, p.2 i) ∈ E i}

/-- Characterization of membership in a pi entourage. -/
@[simp]
theorem mem_pi {E : ∀ i, Entourage (X i)} {p : (∀ i, X i) × (∀ i, X i)} :
    p ∈ pi E ↔ ∀ i, (p.1 i, p.2 i) ∈ E i := Iff.rfl

/-- The pi of identity entourages is the identity entourage. -/
@[simp]
theorem pi_id : pi (fun _ : ι => SetRel.id (α := α)) = SetRel.id := by
  ext ⟨f, g⟩; simp only [mem_pi, SetRel.mem_id, funext_iff]

/-- The pi of empty entourages is empty (when the index is nonempty). -/
@[simp]
theorem pi_empty [Nonempty ι] : pi (fun _ : ι => (∅ : Entourage α)) = ∅ := by
  ext ⟨f, g⟩; simp

/-- Inverse distributes over pi. -/
@[simp]
theorem pi_inv (E : ∀ i, Entourage (X i)) : (pi E)⁻¹ = pi (fun i => (E i)⁻¹) := by
  ext ⟨f, g⟩; simp only [SetRel.mem_inv, mem_pi]

/-- Composition distributes over pi. -/
theorem pi_comp (E F : ∀ i, Entourage (X i)) : pi E ○ pi F = pi (fun i => E i ○ F i) := by
  ext ⟨f, g⟩
  simp only [SetRel.mem_comp, mem_pi]
  constructor
  · rintro ⟨h, hE, hF⟩ i; exact ⟨h i, hE i, hF i⟩
  · intro H
    classical
    choose w hw using H
    exact ⟨w, fun i => (hw i).1, fun i => (hw i).2⟩

/-- Pi is monotone in each coordinate. -/
@[gcongr]
theorem pi_mono {E F : ∀ i, Entourage (X i)} (h : ∀ i, E i ⊆ F i) : pi E ⊆ pi F :=
  fun _ hp i => h i (hp i)

/-- A pi entourage is nonempty iff all factors are nonempty. -/
theorem pi_nonempty {E : ∀ i, Entourage (X i)} : (pi E).Nonempty ↔ ∀ i, (E i).Nonempty := by
  constructor
  · intro ⟨p, hp⟩ i; exact ⟨(p.1 i, p.2 i), hp i⟩
  · intro hE
    classical
    choose w hw using hE
    exact ⟨(fun i => (w i).1, fun i => (w i).2), hw⟩

/-- A pi entourage is empty iff some factor is empty. -/
theorem pi_eq_empty_iff {E : ∀ i, Entourage (X i)} : pi E = ∅ ↔ ∃ i, E i = ∅ := by
  rw [← not_nonempty_iff_eq_empty, pi_nonempty]
  simp only [not_forall, not_nonempty_iff_eq_empty]

/-- The projection of a pi entourage to coordinate `i` is contained in `E i`. -/
theorem pi_map_eval_subset (E : ∀ i, Entourage (X i)) (i : ι) :
    (pi E).map (eval i) ⊆ E i := by
  rintro ⟨x, y⟩ ⟨p, hp, h⟩; cases h; exact hp i

open Classical in
/-- The projection of a nonempty pi entourage to coordinate `i` equals `E i`. -/
theorem map_eval_pi {E : ∀ i, Entourage (X i)} (hne : (pi E).Nonempty) (i : ι) :
    (pi E).map (eval i) = E i :=
  (pi_map_eval_subset E i).antisymm fun ⟨x, y⟩ hxy ↦
    let w := fun j ↦ (pi_nonempty.mp hne j).choose
    let hw := fun j ↦ (pi_nonempty.mp hne j).choose_spec
    let f := fun j ↦ if h : j = i then h ▸ x else (w j).1
    let g := fun j ↦ if h : j = i then h ▸ y else (w j).2
    have hmem : (f, g) ∈ pi E := fun j ↦
      if h : j = i then by simp only [f, g, dif_pos h]; exact h ▸ hxy
      else by simp only [f, g, dif_neg h]; exact hw j
    have heq : (eval i f, eval i g) = (x, y) := Prod.ext (dif_pos rfl) (dif_pos rfl)
    ⟨⟨f, g⟩, hmem, heq⟩

/-- The ball of a pi entourage is the set of functions whose values are in the respective balls. -/
theorem ball_pi (E : ∀ i, Entourage (X i)) (f : ∀ i, X i) :
    (pi E).ball f = {g | ∀ i, g i ∈ (E i).ball (f i)} := rfl

/-- The pi of reflexive entourages is reflexive. -/
theorem IsRefl.pi {E : ∀ i, Entourage (X i)} (hE : ∀ i, (E i).IsRefl) : (pi E).IsRefl := by
  constructor; intro f i; exact SetRel.rfl (E i)

/-- The pi of symmetric entourages is symmetric. -/
theorem IsSymm.pi {E : ∀ i, Entourage (X i)} (hE : ∀ i, (E i).IsSymm) : (pi E).IsSymm := by
  constructor
  intro f g; simp only [mem_pi]
  exact fun a i ↦ SetRel.symm (E i) (a i)

/-- The pi of transitive entourages is transitive. -/
theorem IsTrans.pi {E : ∀ i, Entourage (X i)} (hE : ∀ i, (E i).IsTrans) : (pi E).IsTrans :=
  ⟨fun _ _ _ hfg hgh i ↦ SetRel.trans (E i) (hfg i) (hgh i)⟩

/-! ### Symmetry

Properties of symmetric entourages and symmetry-preserving operations.
-/

/-- The union of an entourage with its inverse is symmetric. -/
theorem isSymm_union_inv (E : Entourage α) : (E ∪ E⁻¹).IsSymm :=
  ⟨fun _ _ h => h.elim Or.inr Or.inl⟩

/-- Symmetry is preserved by map. -/
theorem map_of_isSymm {E : Entourage α} (hE : E.IsSymm) (f : α → β) : (E.map f).IsSymm := by
  refine ⟨fun x y ⟨⟨a, b⟩, hab, heq⟩ => ?_⟩
  simp only [Prod.map_apply] at heq
  exact ⟨⟨b, a⟩, hE.symm a b hab, by simpa [and_comm] using heq⟩

/-- A symmetric entourage equals its inverse. -/
theorem inv_eq_self_of_isSymm {E : Entourage α} (hE : E.IsSymm) : E⁻¹ = E :=
  Set.ext fun ⟨x, y⟩ => ⟨fun h => hE.symm y x h, fun h => hE.symm x y h⟩

/-- The union of symmetric entourages is symmetric. -/
theorem IsSymm.union {E F : Entourage α} (hE : E.IsSymm) (hF : F.IsSymm) : (E ∪ F).IsSymm :=
  ⟨fun x y h => h.elim (fun h => Or.inl (hE.symm x y h)) (fun h => Or.inr (hF.symm x y h))⟩

/-! ### Symmetrization

The symmetrization of an entourage `E` is `E ∪ E⁻¹`, which is the smallest symmetric
entourage containing `E`. This is useful for converting arbitrary entourages into
symmetric ones while preserving control over the "size" of the entourage.
-/

/-- The symmetrization of an entourage: `E ∪ E⁻¹`. -/
def symmetrize (E : Entourage α) : Entourage α := E ∪ E⁻¹

/-- Characterization of membership in a symmetrized entourage. -/
theorem mem_symmetrize {E : Entourage α} {p : α × α} :
  p ∈ E.symmetrize ↔ p ∈ E ∨ (p.2, p.1) ∈ E := by
  rfl

/-- The symmetrization of any entourage is symmetric. -/
theorem symmetrize_isSymm (E : Entourage α) : E.symmetrize.IsSymm :=
  ⟨fun _ _ a ↦ id (Or.symm a)⟩

/-- An entourage is contained in its symmetrization. -/
theorem subset_symmetrize (E : Entourage α) : E ⊆ E.symmetrize := Set.subset_union_left

/-- The inverse of an entourage is contained in its symmetrization. -/
theorem inv_subset_symmetrize (E : Entourage α) : E⁻¹ ⊆ E.symmetrize := Set.subset_union_right

/-- Symmetrization is monotone. -/
@[gcongr]
theorem symmetrize_mono {E F : Entourage α} (h : E ⊆ F) : E.symmetrize ⊆ F.symmetrize :=
  Set.union_subset_union h (SetRel.inv_mono h)

/-- An entourage equals its symmetrization iff it is symmetric. -/
theorem symmetrize_eq_self {E : Entourage α} : E.symmetrize = E ↔ E.IsSymm := by
  constructor
  · intro h; rw [← h]; exact symmetrize_isSymm E
  · intro h; simp only [symmetrize, SetRel.inv_eq_self, union_self]

/-- Symmetrization is idempotent. -/
@[simp]
theorem symmetrize_idem (E : Entourage α) : E.symmetrize.symmetrize = E.symmetrize :=
   (symmetrize_eq_self).mpr (symmetrize_isSymm E)

/-- The symmetrization of a reflexive entourage is reflexive. -/
theorem IsRefl.symmetrize {E : Entourage α} (hE : E.IsRefl) : E.symmetrize.IsRefl :=
  ⟨fun _ ↦ Or.inl (SetRel.rfl E)⟩

theorem symmetrize_union_id_isRefl (E : Entourage α) :
    (E.symmetrize ∪ Entourage.id).IsRefl :=
  ⟨fun _ ↦ Or.inr rfl⟩

theorem symmetrize_union_id_isSymm (E : Entourage α) :
    (E.symmetrize ∪ Entourage.id).IsSymm :=
  ⟨fun x y h ↦ h.elim
    (fun h ↦ Or.inl ((symmetrize_isSymm _).symm x y h))
    (fun h ↦ Or.inr h.symm)⟩

theorem symmetrize_union_id_eq_self {E : Entourage α} (hrefl : E.IsRefl) (hsymm : E.IsSymm) :
    E.symmetrize ∪ Entourage.id = E := by
  rw [Entourage.symmetrize_eq_self.mpr hsymm]
  exact Set.union_eq_left.mpr (fun ⟨a, _⟩ h ↦ h ▸ hrefl.1 a)

/-! ### Iterated Composition

The n-fold composition `E ^ n` is defined by iterating composition:
`E ^ 0 = id`, `E ^ (n+1) = E ○ (E ^ n)`.
-/

/-- The n-fold composition of an entourage with itself. -/
private def compN (E : Entourage α) : ℕ → Entourage α
  | 0 => Entourage.id
  | n + 1 => E ○ E.compN n

/-- Power notation `E ^ n` for iterated composition of entourages. -/
instance : HPow (Entourage α) ℕ (Entourage α) where
  hPow := compN

/-- SMul notation for entourage iteration (same as HPow, for to_additive compatibility). -/
instance : HSMul ℕ (Entourage α) (Entourage α) where
  hSMul n E := compN E n

attribute [to_additive existing] instHPowNat

/-- The 0th power of any entourage is the identity. -/
@[simp]
theorem pow_zero (E : Entourage α) : E ^ 0 = Entourage.id := rfl

/-- The 1st power of an entourage is itself. -/
@[simp]
theorem pow_one (E : Entourage α) : E ^ 1 = E := SetRel.comp_id E

/-- The (n+1)th power is composition of E with the nth power. -/
@[simp]
theorem pow_succ (E : Entourage α) (n : ℕ) : E ^ (n + 1) = E ○ E ^ n := rfl

/-- Alternative form: the (n+1)th power is the nth power composed with E. -/
theorem pow_succ' (E : Entourage α) (n : ℕ) : E ^ (n + 1) = E ^ n ○ E := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← SetRel.comp_assoc, ← pow_succ]; rw [ih]

/-- Powers are additive: `E ^ (m + n) = E ^ m ○ E ^ n`. -/
theorem pow_add (E : Entourage α) (m n : ℕ) : E ^ (m + n) = E ^ m ○ E ^ n := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add, pow_succ, pow_succ, ih, SetRel.comp_assoc]

/-- Powers are multiplicative: `E ^ (m * n) = (E ^ m) ^ n`. -/
theorem pow_mul (E : Entourage α) (m n : ℕ) : E ^ (m * n) = (E ^ m) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, pow_add, ih, pow_succ']

/-- Taking powers is monotone in the base entourage. -/
@[gcongr]
theorem pow_mono {E F : Entourage α} (h : E ⊆ F) (n : ℕ) : E ^ n ⊆ F ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => exact fun _ ⟨z, hz₁, hz₂⟩ => ⟨z, h hz₁, ih hz₂⟩

/-- The inverse of a power equals the power of the inverse. -/
theorem pow_inv (E : Entourage α) (n : ℕ) : (E ^ n)⁻¹ = E⁻¹ ^ n := by
  induction n with
  | zero => simp only [pow_zero, id_eq, SetRel.inv_eq_self]
  | succ n ih => rw [pow_succ, SetRel.inv_comp, ih, pow_succ']

/-- Any power of the identity entourage is the identity. -/
theorem id_pow (n : ℕ) : (Entourage.id : Entourage α) ^ n = Entourage.id := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/-- Powers of reflexive entourages are reflexive. -/
theorem IsRefl.pow {E : Entourage α} (hE : E.IsRefl) (n : ℕ) : (E ^ n).IsRefl := by
  induction n with
  | zero => exact ⟨fun _ => rfl⟩
  | succ n ih => exact ⟨fun x => ⟨x, SetRel.rfl E, SetRel.rfl (E ^ n)⟩⟩

/-- Powers of symmetric entourages are symmetric. -/
theorem IsSymm.pow {E : Entourage α} (hE : E.IsSymm) (n : ℕ) : (E ^ n).IsSymm := by
  induction n with
  | zero => exact ⟨fun _ _ h => h.symm⟩
  | succ n ih =>
    refine ⟨fun x y ⟨z, hxz, hzy⟩ => ?_⟩
    rw [pow_succ']
    exact ⟨z, ih.symm _ _ hzy, hE.symm _ _ hxz⟩

/-- For reflexive entourages, powers grow: `E ^ n ⊆ E ^ (n + 1)`. -/
theorem subset_pow_succ {E : Entourage α} (hE : E.IsRefl) (n : ℕ) : E ^ n ⊆ E ^ (n + 1) :=
  fun _ h => ⟨_, SetRel.rfl E, h⟩

/-- For reflexive entourages, larger exponents give larger sets. -/
theorem pow_subset_pow {E : Entourage α} (hE : E.IsRefl) {m n : ℕ} (h : m ≤ n) :
    E ^ m ⊆ E ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  exact fun _ hp => ⟨_, hp, (IsRefl.pow hE k).1 _⟩

/-- Characterization of membership in `E ^ (n + 1)` via an intermediate point. -/
theorem mem_pow_succ {E : Entourage α} {x y : α} {n : ℕ} :
    (x, y) ∈ E ^ (n + 1) ↔ ∃ z, (x, z) ∈ E ∧ (z, y) ∈ E ^ n :=
  SetRel.mem_comp

/-- The ball of `E ^ (n + 1)` is the E-preimage of the ball of `E ^ n`. -/
theorem ball_pow_succ (E : Entourage α) (n : ℕ) (x : α) :
    (E ^ (n + 1)).ball x = E.preimage ((E ^ n).ball x) :=
  ball_comp E (E ^ n) x

/-- `E ⊆ E ^ (n + 1)` for reflexive entourages. -/
theorem subset_pow_of_pos {E : Entourage α} (hE : E.IsRefl) {n : ℕ} (hn : 0 < n) :
    E ⊆ E ^ n := by
  simpa using pow_subset_pow hE hn

/-- The map operation distributes over powers. -/
theorem map_pow (f : α → β) (E : Entourage α) (n : ℕ) :
    (E ^ n).map f ⊆ (E.map f) ^ n := by
  induction n with
  | zero =>
    intro ⟨a, b⟩ ⟨⟨x, y⟩, hxy, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact congrArg f hxy
  | succ n ih =>
    exact (map_comp_subset E (E ^ n) f).trans (fun _ ⟨z, hz₁, hz₂⟩ => ⟨z, hz₁, ih hz₂⟩)

/-- If `E.map f ⊆ F ^ K`, then `(E ^ n).map f ⊆ F ^ (K * n)`. -/
theorem map_pow_subset_pow_mul (f : α → β) {E : Entourage α} {F : Entourage β} {K : ℕ}
    (h : E.map f ⊆ F ^ K) (n : ℕ) : (E ^ n).map f ⊆ F ^ (K * n) :=
  calc (E ^ n).map f
      ⊆ (E.map f) ^ n := map_pow f E n
    _ ⊆ (F ^ K) ^ n := pow_mono h n
    _ = F ^ (K * n) := (pow_mul F K n).symm

/-- The comap operation distributes over powers (opposite inclusion to map). -/
theorem comap_pow (f : α → β) (E : Entourage β) (n : ℕ) :
    (E.comap f) ^ n ⊆ (E ^ n).comap f := by
  induction n with
  | zero => exact fun ⟨a, b⟩ h => congrArg f h
  | succ n ih =>
    intro ⟨a, b⟩ ⟨z, haz, hzb⟩
    exact ⟨f z, haz, ih hzb⟩

/-- Conjugating a power by a symmetric entourage stays within a higher power. -/
theorem conj_pow_subset_pow {E : Entourage α} (hE_symm : E.IsSymm) (n : ℕ) :
    E ○ E ^ n ○ E⁻¹ ⊆ E ^ (n + 2) := by
  simp only [inv_eq_self_of_isSymm hE_symm, pow_succ', SetRel.comp_assoc, ← pow_succ]
  exact comp_mono (fun ⦃a⦄ a_1 ↦ a_1) fun ⦃a⦄ a_1 ↦ a_1

/-- For a symmetric entourage, `E ○ E^n ○ E ⊆ E^(n+2)`. -/
theorem comp_pow_comp_subset_pow {E : Entourage α} (hE : E.IsSymm) (n : ℕ) :
    E ○ E ^ n ○ E ⊆ E ^ (n + 2) := by
  nth_rw 3 [← inv_eq_self_of_isSymm hE]
  exact conj_pow_subset_pow hE n

/-- If `E, G ⊆ F` and `F` is symmetric, then `E ○ F^n ○ G ⊆ F^(n+2)`. -/
theorem subset_pow_of_comp_pow_comp {E F G : Entourage α} (hF : F.IsSymm)
    (hE : E ⊆ F) (hG : G ⊆ F) (n : ℕ) :
    E ○ F ^ n ○ G ⊆ F ^ (n + 2) :=
  (comp_mono (comp_mono hE (Subset.refl _)) hG).trans (comp_pow_comp_subset_pow hF n)

theorem symmetrize_union_id_map_subset_pow {E : Entourage α} {F : Entourage β} {f : α → β} {n : ℕ}
    (hF_refl : F.IsRefl) (hF_symm : F.IsSymm)
    (hf : E.map f ⊆ F ^ n) :
    (E.symmetrize ∪ Entourage.id).map f ⊆ F ^ n := fun ⟨_, _⟩ ⟨⟨x, y⟩, hxy, hab⟩ =>
  hxy.elim
    (fun h => h.elim
      (fun h => hf ⟨(x, y), h, hab⟩)
      (fun h => hab ▸ (IsSymm.pow hF_symm n).symm _ _ (hf ⟨(y, x), h, rfl⟩)))
    (fun h => hab ▸ congrArg
      (fun z => Prod.map _ _ (x, z)) (mem_id.mp h).symm ▸
          (IsRefl.pow hF_refl n).1 (f x))

/-! ### Finiteness -/

section Finiteness

/-- On a finite type, the type of entourages is finite. -/
instance instFiniteEntourage [Finite α] : Finite (Entourage α) := by
  classical
  cases nonempty_fintype α
  exact Finite.of_fintype (Set (α × α))

end Finiteness

end Entourage
