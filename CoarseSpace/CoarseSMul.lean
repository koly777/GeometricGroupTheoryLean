/-
Copyright (c) 2025 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Algebra.Group.Pointwise.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.GroupAction.Defs

import CoarseSpace.Group.Basic

/-!
# Coarse Group Actions

This file develops the theory of group actions on coarse spaces, culminating in the
coarse Švarc-Milnor lemma.

## Main definitions

* `UniformlyControlledSMul M X` : an action where for every controlled `E`, there exists
  controlled `F` such that `E.map (m • ·) ⊆ F` for all `m : M`. This generalizes acting
  by isometries to the coarse setting.
* `IsCoarseSMul M X` : an action where orbit maps `m ↦ m • x` are coarse maps.
* `CocompactSMul M X` : an action where `X = M • s` for some coarsely bounded `s ⊆ X`.
  This is the coarse analogue of cocompact actions on metric spaces.
* `CocompactSMul.cocompactSet` : the witness set for a cocompact action.
* `CocompactSMul.mulOrbitRetraction` : a coarse inverse to the orbit inclusion.
* `CocompactSMul.mulOrbitInclCoarseEquiv` : the orbit inclusion as a coarse equivalence.
* `IsCoarseSMul.coarseEquivMulOrbit` : the orbit map as a coarse equivalence `G ≃ᶜ orbit G x₀`.

## Main results

* `mulOrbitInclusion_coarse` : orbit inclusions are always coarse maps.
* `stabilizer_smul_finite` : if the orbit map is coarsely proper, the stabilizer is finite.
* `coarselyProper_smul_iff'` : orbit maps are coarsely proper iff for every coarsely
  bounded `s`, the set `{g | (g • s ∩ s).Nonempty}` is finite.
* `isControlled_comap_smul_subtype` : under uniform control and coarse properness,
  pullbacks of controlled entourages along orbit maps are controlled.
* `mulOrbitCoarseEquiv` : **Coarse Švarc-Milnor Lemma** — if `G` acts on `X` in a uniformly
  controlled, coarse, and cocompact fashion, then the orbit map `g ↦ g • x₀` is a coarse
  equivalence `G ≃ᶜ X`.

## Implementation notes

The file uses `to_additive` throughout to generate additive versions (`VAdd`, `IsCoarseVAdd`,
etc.) automatically.

## Tags

coarse geometry, group action, Švarc-Milnor lemma, quasi-isometry

## References

* J. Roe, *Lectures on Coarse Geometry*, University Lecture Series 31, AMS, 2003
* N. Brodskiy, J. Dydak, A. Mitra, "Coarse structures and group actions", arXiv:math/0607568
-/

open MulAction

open scoped Pointwise

universe u v w

/-- An additive action of `M` on a coarse space `X` is uniformly controlled if for
every controlled set `E` in `X`, there is a controlled set `F` such that the image of
`E` under `x ↦ m +ᵥ x` is contained in `F` for all `m : M`. -/
class UniformlyControlledVAdd (M : Type u) (X : Type v) [CoarseSpace X] [VAdd M X] : Prop where
    uniformly_controlled {E} (hE : IsControlled E) :
      ∃ F, IsControlled F ∧ ∀ m : M, E.map (fun (x : X) ↦ m +ᵥ x) ⊆ F

/-- A multiplicative action of `M` on a coarse space `X` is uniformly controlled if for
every controlled set `E` in `X`, there is a controlled set `F` such that the image of
`E` under `x ↦ m • x` is contained in `F` for all `m : M`. This generalizes the notion
of acting by isometries to coarse spaces. -/
@[to_additive]
class UniformlyControlledSMul (M : Type u) (X : Type v) [CoarseSpace X] [SMul M X] : Prop where
    uniformly_controlled {E} (hE : IsControlled E) :
      ∃ F, IsControlled F ∧ ∀ m : M, E.map (fun (x : X) ↦ m • x) ⊆ F

/-- An additive action of `M` on a coarse space `X` is coarse if for each point `x : X`,
the orbit map `m ↦ m +ᵥ x` is a coarse map from `M` to `X`. -/
class IsCoarseVAdd (M : Type u) (X : Type v) [CoarseSpace M] [CoarseSpace X] [VAdd M X] : Prop where
    coarse_vadd (x : X) : Coarse (fun (m : M) ↦ m +ᵥ x)

/-- A multiplicative action of `M` on a coarse space `X` is coarse if for each point `x : X`,
the orbit map `m ↦ m • x` is a coarse map from `M` to `X`. -/
@[to_additive]
class IsCoarseSMul (M : Type u) (X : Type v) [CoarseSpace M] [CoarseSpace X] [SMul M X] : Prop where
    coarse_smul (x : X) : Coarse (fun (m : M) ↦ m • x)

/-- An additive action of `M` on a coarse space `X` is cocompact if the entire space `X`
can be covered by `M +ᵥ s` for some coarsely bounded set `s ⊆ X`. This is the coarse
analogue of acting cocompactly on a metric space. -/
class CocompactVAdd (M : Type u) (X : Type v)
    [CoarseSpace M] [CoarseSpace X] [VAdd M X] : Prop where
    univ_eq_vadd : ∃ (s : Set X), IsCoarselyBounded s ∧ @Set.univ X = @Set.univ M +ᵥ s

/-- A multiplicative action of `M` on a coarse space `X` is cocompact if the entire space `X`
can be covered by `M • s` for some coarsely bounded set `s ⊆ X`. This is the coarse
analogue of acting cocompactly on a metric space. -/
@[to_additive]
class CocompactSMul (M : Type u) (X : Type v)
    [CoarseSpace M] [CoarseSpace X] [SMul M X] : Prop where
    univ_eq_smul : ∃ (s : Set X), IsCoarselyBounded s ∧ @Set.univ X = @Set.univ M • s

export UniformlyControlledSMul (uniformly_controlled)
export IsCoarseSMul (coarse_smul)

namespace CoarseSpace

variable (G : Type v)
variable (X : Type w) [CoarseSpace X]


/-! ### Basic properties of orbit inclusions -/

section SMul

/-- The inclusion of an orbit into the ambient space is always a coarse map. -/
@[to_additive /-- The inclusion of an orbit into the ambient space is always a coarse map. -/]
theorem mulOrbitInclusion_coarse [SMul G X] (x₀ : X) :
    Coarse (Subtype.val : MulAction.orbit G x₀ → X) :=
  ⟨fun hE ↦ hE,
   fun ht ↦ (isCoarselyBounded_subtype_iff _).2 (ht.subset (Set.image_preimage_subset _ _))⟩

variable [CoarseSpace G] [SMul G X] [CocompactSMul G X]

/-- The cocompact set witnessing that the action is cocompact: a coarsely bounded set
whose orbit under `G` covers all of `X`. -/
@[to_additive CocompactVAdd.cocompactSet]
noncomputable def CocompactSMul.cocompactSet : Set X :=
  (CocompactSMul.univ_eq_smul (M := G) (X := X)).choose

/-- The cocompact witness is coarsely bounded. -/
@[to_additive CocompactVAdd.cocompactSet_bounded]
theorem CocompactSMul.cocompactSet_bounded :
    IsCoarselyBounded (CocompactSMul.cocompactSet G X) :=
  (CocompactSMul.univ_eq_smul (M := G) (X := X)).choose_spec.1

/-- The orbit of the cocompact set covers all of `X`. -/
@[to_additive cocompactSet_bounded.cocompactSet_covers]
theorem CocompactSMul.cocompactSet_covers :
    (Set.univ : Set X) = @Set.univ G • CocompactSMul.cocompactSet G X :=
  (CocompactSMul.univ_eq_smul (M := G) (X := X)).choose_spec.2

/-- For any point `x : X`, choose a pair `(g, y)` where `y` is in the cocompact set
and `g • y = x`. -/
@[to_additive CocompactVAdd.coveringPair /-- For any point `x : X`, choose a pair `(g, y)`
where `y` is in the cocompact set and `g +ᵥ y = x`. -/]
noncomputable def CocompactSMul.coveringPair (x : X) : G × X :=
  let h : x ∈ @Set.univ G • CocompactSMul.cocompactSet G X := by
    rw [← CocompactSMul.cocompactSet_covers]; exact Set.mem_univ x
  let h' := Set.mem_image2.mp h
  (h'.choose, h'.choose_spec.2.choose)

/-- The second component of `coveringPair G X x` lies in the cocompact set. -/
@[to_additive CocompactVAdd.coveringPair_mem]
theorem coveringPair_mem (x : X) :
    (CocompactSMul.coveringPair G X x).2 ∈ CocompactSMul.cocompactSet G X := by
  simp only [CocompactSMul.coveringPair]
  have h : x ∈ @Set.univ G • CocompactSMul.cocompactSet G X := by
    rw [← CocompactSMul.cocompactSet_covers]; exact Set.mem_univ x
  exact (Set.mem_image2.mp h).choose_spec.2.choose_spec.1

/-- Acting by the first component of `coveringPair` on the second gives back `x`. -/
@[to_additive CocompactVAdd.coveringPair_mem]
theorem CocompactSMul.coveringPair_smul (x : X) :
    (CocompactSMul.coveringPair G X x).1 • (CocompactSMul.coveringPair G X x).2 = x := by
  simp only [CocompactSMul.coveringPair]
  have h : x ∈ @Set.univ G • CocompactSMul.cocompactSet G X := by
    rw [← CocompactSMul.cocompactSet_covers]; exact Set.mem_univ x
  exact (Set.mem_image2.mp h).choose_spec.2.choose_spec.2

end SMul

/-! ### Orbit retractions for cocompact actions -/

section Action

variable [Group G] [MulAction G X] [CocompactSMul G X]

/-- Given a cocompact action of `G` on `X`, construct a retraction from `X` onto the
orbit of a point `x₀`. For each `x ∈ X`, we use the covering pair to find `g` such that
`g • y = x` for some `y` in the cocompact set, then map `x` to `g • g₀⁻¹ • x₀` where
`g₀ • y₀ = x₀`. -/
@[to_additive CocompactVAdd.addOrbitRetraction
/-- Given a cocompact action of `G` on `X`, construct a retraction from `X` onto the
orbit of a point `x₀`. For each `x ∈ X`, we use the covering pair to find `g` such that
`g +ᵥ y = x` for some `y` in the cocompact set, then map `x` to `g +ᵥ -g₀ +ᵥ x₀` where
`g₀ +ᵥ y₀ = x₀`. -/]
noncomputable def CocompactSMul.mulOrbitRetraction (x₀ : X) :
    X → MulAction.orbit G x₀ := fun x ↦
  (CocompactSMul.coveringPair G X x).1 •
  (CocompactSMul.coveringPair G X x₀).1⁻¹ •
  ⟨x₀, MulAction.mem_orbit_self x₀⟩

/-- The retraction evaluated at `x`, coerced to `X`. -/
@[to_additive CocompactVAdd.addOrbitRetraction_coe]
theorem CocompactSMul.mulOrbitRetraction_coe (x₀ x : X) :
    ((CocompactSMul.mulOrbitRetraction G X x₀ x) : X) =
      (CocompactSMul.coveringPair G X x).1 • (CocompactSMul.coveringPair G X x₀).2 :=
  orbit.coe_smul.trans (congrArg _ (orbit.coe_smul.trans
    (inv_smul_eq_iff.mpr (CocompactSMul.coveringPair_smul G X x₀).symm)))

end Action

variable (M : Type u) {X : Type w}

/-! ### Group actions and coarse properties -/

section Group

variable [Group G]

/-- Acting on the left component by `g` puts the pair in the `g⁻¹`-translated entourage. -/
@[to_additive /-- Acting on the left component by `g` puts the pair in the
`-g`-translated entourage. -/]
lemma Entourage.mem_map_inv_smul_of_smul_left [MulAction G X] {E : Entourage X} {g : G} {x y : X}
    (h : (g • x, y) ∈ E) : (x, g⁻¹ • y) ∈ E.map (g⁻¹ • ·) :=
  Entourage.mem_map_iff.mpr ⟨g • x, y, h, inv_smul_smul g x, rfl⟩

section SMul

variable [SMul G X]

/-- The orbit map is always controlled when `X` carries the coinduced coarse
structure from this map. -/
@[to_additive]
theorem controlled_smul (x₀ : X) :
    @Controlled G X _ (.coinducedTC (· • x₀ : G → X)) (· • x₀ : G → X) :=
  (controlled_iff_coinduced_le _ _ _).mpr le_rfl

variable [CoarseSpace X]

/-- The orbit map is coarsely proper if preimages of coarsely bounded sets under the
inverted orbit map are finite. -/
@[to_additive]
theorem coarselyProper_smul
    (h : ∀ (s : Set X), IsCoarselyBounded s → ∀ x : X, {g : G | g⁻¹ • x ∈ s}.Finite) :
    ∀ x : X, CoarselyProper (fun (g : G) ↦ g • x) := fun x {s} hs ↦
  isCoarselyBounded_iff_finite.mpr <|
    (h s hs x).image (·⁻¹) |>.subset fun g hg ↦ ⟨g⁻¹, by simpa using hg, inv_inv g⟩

/-- Characterization of when all orbit maps are coarsely proper. -/
@[to_additive]
theorem coarselyProper_smul_iff :
    (∀ x : X, CoarselyProper (fun (g : G) ↦ g • x)) ↔
    (∀ (s : Set X), IsCoarselyBounded s → ∀ x : X, {g : G | g⁻¹ • x ∈ s}.Finite) :=
  ⟨fun h _ hs x ↦
    (finite_of_isCoarselyBounded (h x hs)).image (·⁻¹) |>.subset fun g hg ↦
      ⟨g⁻¹, hg, inv_inv g⟩,
   fun h ↦ coarselyProper_smul G h⟩

end SMul

/-! ### Actions and coarse equivalences -/

section Action

variable [MulAction G X]

section Equiv

/-- If the orbit map is coarsely proper, then the stabilizer of `x₀` is finite. -/
@[to_additive]
theorem stabilizer_smul_finite [CoarseSpace X]
  (x₀ : X) (h : CoarselyProper (· • x₀ : G → X)) :
    Finite (MulAction.stabilizer G x₀) :=
  have hfin : (MulAction.stabilizer G x₀ : Set G).Finite :=
    finite_of_isCoarselyBounded <| h (isCoarselyBounded_singleton x₀)
  Set.finite_coe_iff.mp hfin

/-- The orbit map to the orbit subtype is controlled if the orbit map to `X` is controlled. -/
@[to_additive]
theorem controlled_smul_subtype [CoarseSpace X]
  (x₀ : X) (h : Controlled (· • x₀ : G → X)) :
    Controlled (· • ⟨x₀, MulAction.mem_orbit_self x₀⟩ : G → MulAction.orbit G x₀) := by
  intro E hE
  have heq :
  (E.map (· • ⟨x₀, MulAction.mem_orbit_self x₀⟩ : G → MulAction.orbit G x₀)).map Subtype.val =
             E.map (fun g ↦ g • x₀) := (Entourage.map_comp ..).symm ▸ rfl
  exact isControlled_subtype_iff.mpr (heq ▸ h hE)

/-- The orbit map to the orbit subtype is coarsely proper if the orbit map to `X` is
coarsely proper. -/
@[to_additive]
theorem coarselyProper_smul_subtype [CoarseSpace X]
    (x₀ : X) (h : CoarselyProper (· • x₀ : G → X)) :
    CoarselyProper (· • ⟨x₀, MulAction.mem_orbit_self x₀⟩ : G → MulAction.orbit G x₀) :=
  fun {s} hs ↦
    let x₀' : MulAction.orbit G x₀ := ⟨x₀, MulAction.mem_orbit_self x₀⟩
    let heq : (fun g ↦ g • x₀') ⁻¹' s = (fun g ↦ g • x₀) ⁻¹' (Subtype.val '' s) :=
      Set.ext fun g ↦
        ⟨fun hg ↦ ⟨g • x₀', hg, orbit.coe_smul⟩,
         fun ⟨y, hy, hval⟩ ↦
           have heq : y = g • x₀' :=
            Subtype.ext (hval.trans (orbit.coe_smul (m := g) (a' := x₀')).symm)
           (Set.mem_preimage.mpr <| heq.symm ▸ hy)⟩
    heq ▸ h ((isCoarselyBounded_subtype_iff s).mp hs)

/-- If the action is coarse (i.e., orbit maps are coarse maps), then the orbit map
to the orbit subtype is a coarse map. -/
@[to_additive]
theorem coarse_smul_orbit [CoarseSpace X] [IsCoarseSMul G X] (x₀ : X) :
    Coarse (· • ⟨x₀, MulAction.mem_orbit_self x₀⟩ : G → MulAction.orbit G x₀) :=
  ⟨controlled_smul_subtype G x₀ (coarse_smul x₀).controlled,
   coarselyProper_smul_subtype G x₀ (coarse_smul x₀).proper⟩

/-- The pullback of the identity entourage along the orbit map is controlled iff the
stabilizer is finite. -/
@[to_additive]
theorem isControlled_comap_smul_id (x₀ : X) (h : Finite (MulAction.stabilizer G x₀)) :
    IsControlled ((@Entourage.id X).comap (· • x₀ : G → X)) :=
  let hfin : (stabilizer G x₀ : Set G).Finite := Set.finite_coe_iff.mpr h
  let heq : (@Entourage.id X).comap (· • x₀) = leftMulEntourage (stabilizer G x₀ : Set G) :=
    Set.ext fun ⟨a, b⟩ ↦ by
      rw [Entourage.mem_comap, mem_leftMulEntourage, SetLike.mem_coe, mem_stabilizer_iff, mul_smul]
      exact ⟨fun h ↦ h.symm ▸ inv_smul_smul a x₀, fun h ↦ eq_inv_smul_iff.mp h.symm⟩
  heq ▸ hfin.coe_toFinset ▸ isControlled_leftMulEntourage hfin.toFinset

open Classical in
/-- If `E` is a controlled entourage on `G` and the stabilizer of `x₀` is finite, then
the pullback of the pushforward `(E.map (· • x₀)).comap (· • x₀)` is controlled. -/
@[to_additive /-- If `E` is a controlled entourage on `G` and the stabilizer of `x₀` is finite, then
the pullback of the pushforward `(E.map (· +ᵥ x₀)).comap (· +ᵥ x₀)` is controlled. -/]
lemma isControlled_comap_smul_of_isControlled (x₀ : X) (h : Finite (MulAction.stabilizer G x₀))
    {E : Entourage G} (hE : IsControlled E) :
    IsControlled ((E.map (· • x₀ : G → X)).comap (· • x₀ : G → X)) :=
  let hfin : (stabilizer G x₀ : Set G).Finite := Set.finite_coe_iff.mpr h
  let ⟨K, hK⟩ := exists_finset_leftMulEntourage_of_isControlled hE
  -- pullback of pushforward: {(a,b) | ∃ (a₁,b₁) ∈ E, a •x₀ = a₁•x₀ ∧ b•x₀ = b₁•x₀}
  -- this is contained in leftMulEntourage (Stab * K * Stab⁻¹)
  (isControlled_leftMulEntourage (hfin.toFinset * K * hfin.toFinset⁻¹)).subset
    fun ⟨a, b⟩ ⟨⟨a₁, b₁⟩, hab₁, h₁⟩ ↦
      -- (a₁, b₁) ∈ E with a • x₀ = a₁ • x₀ and b • x₀ = b₁ • x₀
      let ⟨ha, hb⟩ := Prod.mk_inj.mp (Prod.map_apply .. ▸ Prod.map_apply .. ▸ h₁)
      mem_leftMulEntourage.mpr
        <| Finset.coe_mul (hfin.toFinset * K) (hfin.toFinset⁻¹) ▸
           Finset.coe_mul (hfin.toFinset) K ▸
      -- decompose: a⁻¹b = (a⁻¹a₁)(a₁⁻¹b₁)(b₁⁻¹b) ∈ Stab * K * Stab⁻¹
      have hab : a⁻¹ * b ∈ (stabilizer G x₀).carrier * K * (stabilizer G x₀).carrier⁻¹ :=
        -- a⁻¹a₁ ∈ Stab since a • x₀ = a₁ • x₀
        have h₁ : a⁻¹ * a₁ ∈ stabilizer G x₀ :=
          mem_stabilizer_iff.mpr <| (mul_smul a⁻¹ a₁ x₀) ▸ inv_smul_eq_iff.mpr ha
        -- a₁⁻¹b₁ ∈ K since (a₁, b₁) ∈ E ⊆ leftMulEntourage K
        have h₂ : a₁⁻¹ * b₁ ∈ K := hK hab₁
        -- b₁⁻¹b ∈ Stab⁻¹ since b • x₀ = b₁ • x₀
        have h₃ : b₁⁻¹ * b ∈ (stabilizer G x₀).carrier⁻¹ :=
          Set.mem_inv.mpr <| mem_stabilizer_iff.mpr <|
            mul_inv_rev b₁⁻¹ b ▸ (inv_inv b₁).symm ▸
            mul_smul b⁻¹ b₁ x₀ ▸ inv_smul_eq_iff.mpr hb
        have h₄ : (a⁻¹ * a₁) * (a₁⁻¹ * b₁) * (b₁⁻¹ * b) = a⁻¹ * b :=
          (mul_assoc a⁻¹ a₁ _) ▸ (mul_inv_cancel_left a₁ b₁).symm ▸
          (mul_assoc a⁻¹ b₁ _) ▸ (mul_inv_cancel_left b₁ b).symm ▸ rfl
        h₄ ▸ Set.mul_mem_mul (Set.mul_mem_mul h₁ h₂) h₃
      Set.Finite.coe_toFinset _ ▸ Finset.coe_inv hfin.toFinset ▸
      Set.Finite.coe_toFinset _ ▸ Set.mem_mul.mpr hab

variable [MulAction.IsPretransitive G X]

/-- For a transitive action with finite stabilizer, pullbacks of controlled entourages
(in the coinduced structure) along the orbit map are controlled on `G`. -/
@[to_additive]
lemma isControlled_comap_of_coinduced_smul (x₀ : X) (h : Finite (MulAction.stabilizer G x₀))
    {E : Entourage X} (hE : IsControlled[.coinducedTC (· • x₀ : G → X)] E) :
    IsControlled (E.comap (· • x₀ : G → X)) :=
  isControlled_comap_of_coinducedTC (· • x₀)
  (MulAction.surjective_smul G x₀)
  (isControlled_comap_smul_id G _ h)
  (fun _ hF ↦ isControlled_comap_smul_of_isControlled G _ h hF) hE

/-- For a transitive action with finite stabilizer, the orbit map is coarsely
proper when `X` carries the coinduced coarse structure. -/
@[to_additive]
theorem smul_coarselyProper (x₀ : X) (h : Finite (MulAction.stabilizer G x₀)) :
    @CoarselyProper G X _ (.coinducedTC (· • x₀ : G → X)) (· • x₀ : G → X) :=
  @coarselyProper_smul G (X := X) _ _ (.coinducedTC (· • x₀ : G → X)) (fun s hs x ↦
    -- preimage of s under orbit map is finite
    let hfin := isCoarselyBounded_iff_finite.mp (isCoarselyBounded_preimage_of_coinduced _
      (· • x₀) hs (fun _ ↦ isControlled_comap_of_coinduced_smul _ _ h))
    -- by transitivity, x = g' • x₀ for some g'
    let ⟨g', hg'⟩ := exists_smul_eq G x₀ x
    -- {g | g⁻¹ • x ∈ s} = {g | g⁻¹g' • x₀ ∈ s} is a translate of the preimage, hence finite
    hg' ▸ (hfin.image (g' * ·⁻¹)).subset fun g hg ↦
      ⟨g⁻¹ * g', by simpa [mul_smul] using hg, by simp [mul_inv_cancel_left]⟩) x₀

/-- For a transitive action with finite stabilizer, the orbit map is a coarse
map when `X` carries the coinduced coarse structure. -/
@[to_additive]
theorem smul_coarse (x₀ : X) (h : Finite (MulAction.stabilizer G x₀)) :
    @Coarse G X _ (.coinducedTC (· • x₀ : G → X)) (· • x₀ : G → X) :=
  @Coarse.mk G X _ (.coinducedTC (· • x₀ : G → X)) (· • x₀ : G → X)
  (controlled_smul G x₀) (smul_coarselyProper G x₀ h)

/-- For a transitive action with finite stabilizer, the orbit map is a coarse
equivalence between `G` and `X` (with the coinduced coarse structure). -/
@[to_additive]
noncomputable
def smulCoarseEquiv (x₀ : X) (h : Finite (MulAction.stabilizer G x₀)) :
    @CoarseEquiv G X _ (.coinducedTC (· • x₀ : G → X)) :=
    @CoarseEquiv.mkOfSurjective G X _ (.coinducedTC (· • x₀ : G → X))
    (· • x₀ : G → X) (MulAction.surjective_smul G x₀)
    (smul_coarse G x₀ h) (fun _ hE ↦ isControlled_comap_of_coinduced_smul G x₀ h hE)

/-- **Uniqueness of coarse structure**: If the orbit map is a coarse equivalence
for some coarse structure on `X`, then that structure must be the coinduced structure. -/
@[to_additive]
theorem eq_coinduced_of_isCoarseEquiv_smul
  (x₀ : X) (cX : CoarseSpace X) (h : @IsCoarseEquiv G X _ cX (· • x₀ : G → X)) :
  cX = (.coinducedTC fun (g : G) ↦ g • x₀) :=
  have hsurj : Function.Surjective (fun g : G ↦ g • x₀) :=
    MulAction.surjective_smul G x₀
  have hfin : Finite (MulAction.stabilizer G x₀) :=
    stabilizer_smul_finite G x₀ h.coarse.coarselyProper
  letI : CoarseSpace X := .coinducedTC fun (g : G) ↦ g • x₀
  have h' : @IsCoarseEquiv G X _ (.coinducedTC fun (g : G) ↦ g • x₀) (fun g ↦ g • x₀) :=
    (smulCoarseEquiv G x₀ hfin).IsCoarseEquiv
  IsCoarseEquiv.coarseSpace_eq_of_surjective_isCoarseEquiv hsurj cX _ h h'

end Equiv

variable [CoarseSpace X]

/-- Alternative criterion for coarsely proper orbit maps: if for every coarsely bounded `s`,
the set of `g` such that `g • s ∩ s` is nonempty is finite, then all orbit maps are
coarsely proper. Thus an action being coarsely proper generalizes proper discontinuity
to coarse spaces. -/
@[to_additive /-- Alternative criterion for coarsely proper orbit maps: if for every
coarsely bounded `s`, the set of `g` such that `g +ᵥ s ∩ s` is nonempty is finite, then
all orbit maps are coarsely proper. Thus an action being coarsely proper generalizes
proper discontinuity to coarse spaces.-/]
theorem coarselyProper_smul'
    (h : ∀ (s : Set X), IsCoarselyBounded s → {g : G | (g • s ∩ s).Nonempty}.Finite) :
    ∀ x : X, CoarselyProper (fun (g : G) ↦ g • x) :=
  coarselyProper_smul G fun s hs x ↦
    match Set.eq_empty_or_nonempty {g : G | g⁻¹ • x ∈ s} with
    | .inl h₁ => h₁ ▸ Set.finite_empty
    | .inr ⟨g₁, h₁⟩ =>
      let h₂ : {g : G | g⁻¹ • x ∈ s} ⊆ g₁ • {g : G | (g • s ∩ s).Nonempty} :=
        fun g₂ h₂ ↦
          let h₃ : g₁⁻¹ • x ∈ (g₁⁻¹ * g₂) • s :=
            Set.mem_smul_set.mpr ⟨g₂⁻¹ • x,
              h₂, mul_smul (g₁⁻¹ * g₂) g₂⁻¹ x ▸ mul_assoc g₁⁻¹ .. ▸
                  mul_inv_cancel g₂ ▸ (mul_one g₁⁻¹).symm ▸ rfl⟩
          let h₄ : g₁⁻¹ * g₂ ∈ {g | (g • s ∩ s).Nonempty} := ⟨g₁⁻¹ • x, Set.mem_inter h₃ h₁⟩
          Set.mem_smul_set.mpr ⟨g₁⁻¹ * g₂, h₄, smul_eq_mul g₁ _ ▸ mul_inv_cancel_left ..⟩
      Set.Finite.of_surjOn (fun x ↦ g₁ • x) h₂ (h s hs)

/-! ### Uniformly controlled actions -/

section UniformlyControlledSMul

variable [UniformlyControlledSMul G X]

/-- For a uniformly controlled action, the union of all translates `g • s` where
`g • s ∩ s ≠ ∅` is coarsely bounded whenever `s` is coarsely bounded. -/
@[to_additive /-- For a uniformly controlled action, the union of all translates `g +ᵥ s` where
`g +ᵥ s ∩ s ≠ ∅` is coarsely bounded whenever `s` is coarsely bounded. -/]
theorem isCoarselyBounded_biUnion_smul_of_inter_smul_nonempty :
    ∀ (s : Set X), IsCoarselyBounded s →
    IsCoarselyBounded (⋃ g ∈ {g : G | (g • s ∩ s).Nonempty}, g • s) :=
  fun s hs ↦
  let ⟨E, hE, h⟩ := @uniformly_controlled G X _ _ _ _ hs.isControlled
  let hsub : (⋃ g ∈ {g : G | (g • s ∩ s).Nonempty}, g • s) ⊆ E.preimage s :=
    fun _ hx ↦
      let ⟨g, ⟨y, hy', hy⟩, hx'⟩ := Set.mem_iUnion₂.mp hx
      let ⟨a, ha, hax⟩ := Set.mem_smul_set.mp hx'
      let ⟨b, hb, hby⟩ := Set.mem_smul_set.mp hy'
      SetRel.mem_preimage.mpr ⟨y, hy, h g <| Entourage.mem_map.mpr
        ⟨⟨a, b⟩, ⟨(Set.mk_mem_prod ha hb), hax ▸ hby ▸ rfl⟩⟩⟩
  (isCoarselyBounded_preimage_of_isControlled hE hs).subset hsub

/-- Under uniform control, orbit maps are coarsely proper iff for every coarsely bounded `s`,
the set of `g` with `g • s ∩ s ≠ ∅` is finite. -/
@[to_additive /-- Under uniform control, orbit maps are coarsely proper iff for every coarsely
bounded `s`, the set of `g` with `g +ᵥ s ∩ s ≠ ∅` is finite. -/]
theorem coarselyProper_smul_iff' :
  (∀ (x : X), CoarselyProper (fun (g : G) ↦ g • x)) ↔
   ∀ (s : Set X), IsCoarselyBounded s → {g : G | (g • s ∩ s).Nonempty}.Finite :=
  ⟨fun h s hs ↦
    let hsub {x : X} (hx : x ∈ s) :
    {g : G | (g • s ∩ s).Nonempty} ⊆ (fun (g : G) ↦ g • x)⁻¹'
    (⋃ g ∈ {g : G | (g • s ∩ s).Nonempty}, g • s) :=
      fun g hg ↦ Set.mem_preimage.mpr <|
        Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, Set.smul_mem_smul_set hx⟩ ⟩
    match Set.eq_empty_or_nonempty {g | (g • s ∩ s).Nonempty} with
    | .inl h₁ => h₁ ▸ Set.finite_empty
    | .inr ⟨_, ⟨x, ⟨_, hx⟩⟩⟩ => isCoarselyBounded_iff_finite.mp <|
      (h x <| isCoarselyBounded_biUnion_smul_of_inter_smul_nonempty G s hs).subset <| hsub hx,
   fun h ↦ coarselyProper_smul' G h⟩

/-- If `g ↦ g • x₀` is coarsely proper, then for any controlled entourage `E` on the orbit subtype,
`E.comap (fun g ↦ g • (⟨x₀, ..⟩ : MulAction.orbit G x₀))` is controlled on `G`. -/
@[to_additive /-- If `g ↦ g +ᵥ x₀` is coarsely proper, then for any controlled entourage `E` on
the orbit subtype, `E.comap (fun g ↦ g +ᵥ (⟨x₀, ..⟩ : AddAction.orbit G x₀))`
is controlled on `G`. -/]
theorem isControlled_comap_smul_subtype
    (x₀ : X) (hproper : CoarselyProper (· • x₀ : G → X))
    {E : Entourage (MulAction.orbit G x₀)} (hE : IsControlled E) :
    IsControlled (E.comap (fun (g : G) ↦ g • (⟨x₀, MulAction.mem_orbit_self x₀⟩ : _))) :=
  -- Lift E to X; uniform control gives bound F
  let ⟨F, hF, hF_univ⟩ := uniformly_controlled (M := G) (X := X) (isControlled_subtype_iff.mp hE)
  -- K = preimage of F⁻¹.ball(x₀); finite by coarse properness
  let K : Set G := (· • x₀) ⁻¹' (Entourage.ball F.inv x₀)
  let hK : K.Finite := isCoarselyBounded_iff_finite.mp (hproper (isCoarselyBounded_ball_inv hF x₀))
  -- E.comap ⊆ leftMulEntourage K
  (isControlled_leftMulEntourage hK.toFinset).subset fun ⟨a, b⟩ hab ↦
    -- (a • x₀, b • x₀) ∈ E.map Subtype.val → (x₀, (a⁻¹b) • x₀) ∈ F → a⁻¹b ∈ K
    let hab_E' := Entourage.mem_map.mpr
      ⟨_, Entourage.mem_comap.mp hab, Prod.ext orbit.coe_smul orbit.coe_smul⟩
    let hab_F := hF_univ a⁻¹ (mul_smul a⁻¹ b x₀ ▸ Entourage.mem_map_inv_smul_of_smul_left G hab_E')
    mem_leftMulEntourage.mpr (hK.coe_toFinset.symm ▸ Entourage.mem_ball_inv_iff.mpr hab_F)

/-- When `G` acts coarsely on `X`, the orbit map gives a coarse equivalence
`G ≃ᶜ orbit G x₀`. -/
@[to_additive IsCoarseVAdd.coarseEquivAddOrbit]
noncomputable
def IsCoarseSMul.coarseEquivMulOrbit [IsCoarseSMul G X] (x₀ : X) : G ≃ᶜ MulAction.orbit G x₀ :=
  let f : G → MulAction.orbit G x₀ := (· • ⟨x₀, MulAction.mem_orbit_self x₀⟩)
  let hf : Coarse f := ⟨
    controlled_smul_subtype G x₀ (coarse_smul x₀).controlled,
    coarselyProper_smul_subtype G x₀ (coarse_smul x₀).proper⟩
  let hsurj : Function.Surjective f := fun ⟨_, hy⟩ ↦
    ⟨hy.choose, Subtype.ext (orbit.coe_smul.trans hy.choose_spec)⟩
  CoarseEquiv.mkOfSurjective f hsurj hf fun _ hE ↦
    isControlled_comap_smul_subtype G x₀ (coarse_smul x₀).proper hE

/-! ### Cocompact actions and the Švarc-Milnor lemma -/

section CocompactSMul

variable [CocompactSMul G X]

/-- The composition of the orbit retraction with the inclusion is close to the identity on `X`. -/
@[to_additive CocompactVAdd.addOrbitRetraction_close_right]
theorem CocompactSMul.mulOrbitRetraction_close_right (x₀ : X) :
    (Subtype.val ∘ CocompactSMul.mulOrbitRetraction G X x₀) =ᶜ (id : X → X) := by
  -- Cocompact set and base point data
  let s := CocompactSMul.cocompactSet G X
  let y₀ := (CocompactSMul.coveringPair G X x₀).2
  -- The product s ×ˢ {y₀} is controlled
  have hs_ctrl : IsControlled (s ×ˢ {y₀} : Entourage X) :=
    (CocompactSMul.cocompactSet_bounded G X).isControlled.subset
      (Set.prod_mono le_rfl (Set.singleton_subset_iff.mpr (coveringPair_mem G X x₀)))
  -- Uniform control gives a bounding entourage F
  obtain ⟨F, hF_ctrl, hF_uniform⟩ := uniformly_controlled (M := G) (X := X) hs_ctrl
  -- Show the closeness graph is contained in F⁻¹
  refine hF_ctrl.inv.subset fun _ ⟨x, hx⟩ ↦ SetRel.mem_inv.mpr ?_
  simp only [Function.comp_apply, id_eq] at hx
  rw [← hx, mulOrbitRetraction_coe]
  -- The pair (y(x), y₀) lies in s ×ˢ {y₀}
  have hpair_mem : ((CocompactSMul.coveringPair G X x).2, y₀) ∈ (s ×ˢ {y₀}) :=
    ⟨coveringPair_mem G X x, rfl⟩
  -- Apply uniform control to get membership in F
  have hF_mem := hF_uniform (CocompactSMul.coveringPair G X x).1
    (Entourage.mem_map.mpr ⟨_, hpair_mem, rfl⟩)
  rwa [CocompactSMul.coveringPair_smul] at hF_mem

/-- The orbit retraction is a coarse map. -/
@[to_additive CocompactVAdd.addOrbitRetraction_coarse]
theorem CocompactSMul.mulOrbitRetraction_coarse (x₀ : X) :
    Coarse (CocompactSMul.mulOrbitRetraction G X x₀) := by
  let i : MulAction.orbit G x₀ → X := Subtype.val
  let r := CocompactSMul.mulOrbitRetraction G X x₀
  have hir := coarse_of_isClose_id (mulOrbitRetraction_close_right G x₀)
  refine ⟨?_, ?_⟩
  · intro E hE
    exact (isControlled_subtype_iff).2 (by simpa [Entourage.map_comp] using hir.controlled hE)
  · intro t ht
    have hpre : r ⁻¹' t = (i ∘ r) ⁻¹' (i '' t) := Set.ext fun x ↦
      ⟨fun hx ↦ ⟨r x, hx, rfl⟩,
       fun ⟨z, hz, hz'⟩ ↦ show r x ∈ t from Subtype.val_injective hz' ▸ hz⟩
    exact hpre ▸ hir.proper ((isCoarselyBounded_subtype_iff t).1 ht)

/-- The composition of the inclusion with the orbit retraction is close to the identity
on the orbit. -/
@[to_additive CocompactVAdd.addOrbitRetraction_close_left]
theorem CocompactSMul.mulOrbitRetraction_close_left (x₀ : X) :
    (CocompactSMul.mulOrbitRetraction G X x₀ ∘ Subtype.val) =ᶜ
    (id : MulAction.orbit G x₀ → MulAction.orbit G x₀) := by
  let i : MulAction.orbit G x₀ → X := Subtype.val
  let r := CocompactSMul.mulOrbitRetraction G X x₀
  apply (isControlled_subtype_iff).2
  have hsub : Set.range (fun z : MulAction.orbit G x₀ ↦ (i (r (i z)), i z)) ⊆
              Set.range (fun x : X ↦ (i (r x), x)) := fun _ ⟨z, h⟩ ↦ ⟨i z, h⟩
  have hctrl := (mulOrbitRetraction_close_right G x₀).subset hsub
  convert hctrl using 1
  ext ⟨a, b⟩
  exact ⟨fun ⟨⟨_, _⟩, ⟨z, hz⟩, heq'⟩ ↦ ⟨z, (congrArg (Prod.map i i) hz).trans heq'⟩,
         fun ⟨z, hz⟩ ↦ ⟨(r (i z), z), ⟨z, rfl⟩, hz⟩⟩

/-- For a uniformly controlled cocompact action, the inclusion of the orbit into `X`
is a coarse equivalence, with coarse inverse given by the orbit retraction. -/
@[to_additive CocompactVAdd.addOrbitInclCoarseEquiv]
noncomputable def CocompactSMul.mulOrbitInclCoarseEquiv (x₀ : X) : (MulAction.orbit G x₀) ≃ᶜ X where
  toFun := Subtype.val
  invFun := CocompactSMul.mulOrbitRetraction G X x₀
  coarse_toFun := mulOrbitInclusion_coarse G X x₀
  coarse_invFun := CocompactSMul.mulOrbitRetraction_coarse G x₀
  isClose_id_right := CocompactSMul.mulOrbitRetraction_close_right G x₀
  isClose_id_left := CocompactSMul.mulOrbitRetraction_close_left G x₀

/-- **Coarse Švarc-Milnor Lemma**: If a group `G` acts on a coarse space `X` in a uniformly
controlled, coarse, and cocompact fashion, then the orbit map `g ↦ g • x₀` is a coarse
equivalence `G ≃ᶜ X` for any point `x₀ : X`. -/
@[to_additive /-- **Coarse Švarc-Milnor Lemma**: If a group `G` acts on a coarse space `X`
in a uniformly controlled, coarse, and cocompact fashion, then the orbit map `g ↦ g +ᵥ x₀`
is a coarse equivalence `G ≃ᶜ X` for any point `x₀ : X`. -/]
noncomputable def mulOrbitCoarseEquiv [IsCoarseSMul G X] (x₀ : X) : G ≃ᶜ X :=
  (IsCoarseSMul.coarseEquivMulOrbit G x₀).trans <| CocompactSMul.mulOrbitInclCoarseEquiv G x₀

end CocompactSMul

end UniformlyControlledSMul

end Action

end Group

end CoarseSpace
