/-
Copyright (c) 2026 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Topology.Algebra.MulAction
import ForMathlib.Topology.MetricSpace.IsometricSMul

import CoarseSpace.Algebra.UniformlyControlledSMul
import CoarseSpace.Basic
import CoarseSpace.CoarseEquiv.Defs

/-!
# The Švarc–Milnor Lemma

This file proves the Švarc–Milnor lemma at the level of coarse spaces: a group acting on a
coarse space with uniformly controlled action on both itself and the space, coarsely bounded
fundamental domain, and coarse orbit map is coarsely equivalent to the space.

The metric case: a group with a proper left invariant metric and possesing a discrete topolpogy
acting by isometries, properly discontinuously, and cocompactly, on a proper metric space
is then recovered as a special case.

## Main Definitions

* `mulOrbitCoarseEquiv`: given a group `G` acting on a coarse space `α` with
  `UniformlyControlledSMul` in both `G` and `α`, a coarsely bounded set `S` containing a
  basepoint `x₀` whose translates cover `α`, and a coarse orbit map `· • x₀`, constructs a
  coarse equivalence `G ≃ᶜ α`.
* `mulOrbitMetricCoarseEquiv`: the metric specialisation, where a group with a proper left invariant
   metric and possesing a discrete topolpogy acting by isometries, properly discontinuously, and
   cocompactly, on a proper metric space.

## Implementation Notes

The general `mulOrbitCoarseEquiv` takes the section `f` and its covering property as explicit
arguments rather than using `Classical.choice` internally. This keeps the definition computable
when the section is known and defers the noncomputability to the metric wrapper
`mulOrbitMetrocCoarseEquiv'`, which chooses `f` via  the covering lemma
`exists_smul_closedBall_eq_univ`.

## TODO

* Obtain that G is finitely generated once monogenic coarse structures have been formalized.
* Upgrade `mulOrbitMetricCoarseEquiv` to a quasi-isometry once the quasi-isometry API is
  available. The orbit map `g ↦ g • x₀` is a quasi-isometry, provided `G` and the metric space it
  acts upon have coarse midpoints. Coarse midpoints need to be formalized as well.

## Tags

Švarc–Milnor, Svarc–Milnor, coarse equivalence, group action, geometric group theory
-/

open Set SetRel MulAction Metric
open scoped Pointwise SetRel Coarse

variable {G α : Type*}
variable [Group G] [MulAction G α]

@[to_additive]
private theorem smul_comp_isClose_id [CoarseSpace α] [UniformlyControlledSMul G α]
    {S : Set α} (hS : IsCoarselyBounded S) {x₀ : α} (hx₀ : x₀ ∈ S)
    {f : α → G} (hf : ∀ x, x ∈ f x • S) :
    ((· • x₀) ∘ f) =ᶜ id :=
  (isControlled_iUnion_preimage_smul hS).subset fun _ ⟨⟨a, _⟩, rfl, heq⟩ ↦
    heq.subst <| mem_iUnion.mpr ⟨(f a)⁻¹, mem_prod.mpr
      ⟨show (f a)⁻¹ • (f a • x₀) ∈ S from (inv_smul_smul (f a) x₀).symm ▸ hx₀,
       show (f a)⁻¹ • a ∈ S from mem_smul_set_iff_inv_smul_mem.mp (hf a)⟩⟩

@[to_additive]
private theorem comp_smul_isClose_id
    [CoarseSpace G] [CoarseSpace α] [UniformlyControlledSMul G G]
    {S : Set α} (hS : IsCoarselyBounded S) (x₀ : α) (hx₀ : x₀ ∈ S)
    (f : α → G) (hf : ∀ x, x ∈ f x • S) (h_smul : IsCoarselyProperMap (· • x₀ : G → α)) :
    (f ∘ (· • x₀)) =ᶜ id :=
  let T : Set G := (· • x₀) ⁻¹' S
  have hT : IsCoarselyBounded T := h_smul S hS
  have hT₁ : (1 : G) ∈ T := mem_preimage.mpr <| (one_smul G x₀).symm ▸ hx₀
  (isControlled_iUnion_preimage_smul hT).subset fun _ ⟨⟨g, _⟩, rfl, heq⟩ ↦
    heq.subst <| mem_iUnion.mpr ⟨(f (g • x₀))⁻¹,
      show (f (g • x₀))⁻¹ * f (g • x₀) ∈ T from
        (inv_mul_cancel (f (g • x₀))).symm ▸ hT₁,
      show ((f (g • x₀))⁻¹ * g) • x₀ ∈ S from
        (mul_smul (f (g • x₀))⁻¹ g x₀).symm ▸ mem_smul_set_iff_inv_smul_mem.mp (hf (g • x₀))⟩

@[to_additive]
private theorem isControlledMap_of_smul_comp_isClose_id [CoarseSpace G] [CoarseSpace α]
    [UniformlyControlledSMul G G] [UniformlyControlledSMul G α]
    {x₀ : α} {f : α → G} (h_close : ((· • x₀) ∘ f) =ᶜ (id : α → α))
    (h_smul : IsCoarselyProperMap (· • x₀ : G → α)) :
    IsControlledMap f :=
    (isControlledMap_iff f).mpr fun U hU ↦
    let C : SetRel α α := .map ((· • x₀) ∘ f) id '' SetRel.id
    have hC : IsControlled C := h_close
    let T := C ○ U ○ C.inv
    let V : SetRel α α := ⋃ g : G, (.map (g • ·) (g • ·)) ⁻¹' T
    have hV := isControlled_iUnion_preimage_smul ((hC.comp hU).comp h_close.inv)
    have hV_mem : ∀ {a b : α}, (a, b) ∈ U → (x₀, ((f a)⁻¹ * f b) • x₀) ∈ V :=
      fun {a b} hab ↦ mem_iUnion.mpr ⟨f a,
      have : f a • (((f a)⁻¹ * f b) • x₀) = f b • x₀ :=
        (mul_smul (f a) _ x₀).symm ▸ mul_inv_cancel_left (G := G) .. ▸ rfl
      show (f a • x₀, f a • ((f a)⁻¹ * f b) • x₀) ∈ T from
        this ▸ mem_comp_comp ⟨(a, a), rfl, rfl⟩ hab ⟨(b, b), rfl, rfl⟩⟩
    let B := (V ∪ .id).inv.ball x₀
    have hB := (hV.union isControlled_id).inv.isCoarselyBounded_ball x₀
    isControlled_image_of_inv_mul_mem (h_smul _ hB)
      (mem_preimage.mpr <| (one_smul G x₀).symm ▸ (.inr rfl : x₀ ∈ B))
      fun hab ↦ mem_preimage.mpr (.inl (hV_mem hab))

/-- **Coarse Švarc–Milnor lemma** If a group `G` acts on a coarse space `α` with
uniformly controlled action on both itself and `α`, and the translates `g • S`
of a coarsely bounded set `x₀ ∈ S` cover `α`, then the orbit map `g ↦ g • x₀`
and any section `f` with `∀ x, x ∈ f x • S` assemble into a coarse equivalence `G ≃ᶜ α`. -/
@[to_additive
/-- **Coarse Švarc–Milnor lemma** If an additive group `G` acts on a coarse space `α`
with uniformly controlled action on both itself and `α`, and the translates `g +ᵥ S`
of a coarsely bounded set `x₀ ∈ S` cover `α`, then the orbit map `g ↦ g +ᵥ x₀` and any
section `f` with `∀ x, x ∈ f x +ᵥ S` assemble into a coarse equivalence `G ≃ᶜ α`. -/]
def mulOrbitCoarseEquiv [CoarseSpace G] [CoarseSpace α]
    [UniformlyControlledSMul G G] [UniformlyControlledSMul G α]
    {S : Set α} (hS : IsCoarselyBounded S) {x₀ : α} (hx₀ : x₀ ∈ S)
    {f : α → G} (hf : ∀ x, x ∈ f x • S)
    (h_smul : Coarse (· • x₀ : G → α)) : G ≃ᶜ α :=
    { toFun := (· • x₀ : G → α)
      invFun := f
      controlled_toFun := h_smul.controlled
      controlled_invFun :=
        isControlledMap_of_smul_comp_isClose_id (smul_comp_isClose_id hS hx₀ hf) h_smul.proper,
      isClose_id_right := smul_comp_isClose_id hS hx₀ hf
      isClose_id_left := comp_smul_isClose_id hS _ hx₀ _ hf h_smul.proper }

section Metric

variable [PseudoMetricSpace G] [PseudoMetricSpace α]

@[to_additive]
private theorem isControlledMap_smul [ProperSpace G]
    [IsIsometricSMul G G] [IsIsometricSMul G α] {x₀ : α}
    (h_cont : Continuous (· • x₀ : G → α)) :
    IsControlledMap (· • x₀ : G → α) :=
  (isControlledMap_iff _).mpr fun s hs ↦
    let ⟨r, hr⟩ := isControlled_iff_bounded_dist.mp hs
    let K := (· • x₀) '' closedBall (1 : G) (max r 0)
    let ⟨C, hC⟩ := isBounded_iff.mp
      ((isCompact_closedBall (1 : G) (max r 0)).image h_cont).isBounded
    have hx₀ : x₀ ∈ K := ⟨1, mem_closedBall_self (le_max_right ..), one_smul G x₀⟩
    isControlled_iff_bounded_dist.mpr ⟨C, fun _ ⟨⟨g, h⟩, hgh, heq⟩ ↦ heq ▸
      have hmem : (g⁻¹ * h) • x₀ ∈ K := ⟨g⁻¹ * h, mem_closedBall.mpr <| by
        calc  dist (g⁻¹ * h) 1
          _ = dist (g * (g⁻¹ * h)) (g * 1) := ((isometry_smul G g).dist_eq ..).symm
          _ = dist h g := by rw [mul_inv_cancel_left, mul_one]
          _ = dist g h := dist_comm ..
          _ ≤ max r 0 := (hr _ hgh).trans (le_max_left ..), rfl⟩
      calc  dist (g • x₀) (h • x₀)
        _ = dist (g • x₀) (g • ((g⁻¹ * h) • x₀)) := by rw [← mul_smul, mul_inv_cancel_left]
        _ = dist x₀ ((g⁻¹ * h) • x₀) := (isometry_smul α g).dist_eq ..
        _ ≤ C := hC hx₀ hmem⟩

@[to_additive]
private theorem isCoarselyProperMap_smul
  [ProperSpace α] [ProperlyDiscontinuousSMul G α] (x₀ : α) :
    IsCoarselyProperMap (· • x₀ : G → α) := fun s hs ↦
  isCoarselyBounded_iff_isBounded.mpr <|
    let ⟨R, hR⟩ := (isBounded_iff_subset_closedBall x₀).mp
      (isCoarselyBounded_iff_isBounded.mp hs)
    ((ProperlyDiscontinuousSMul.finite_disjoint_inter_image
        isCompact_singleton (isCompact_closedBall x₀ R)).subset
      fun g (hg : g • x₀ ∈ s) ↦ ⟨g • x₀, mem_image_of_mem _ (mem_singleton x₀), hR hg⟩).isBounded

/-- **Coarse Švarc–Milnor lemma** (metric specialization). A group `G` with a left-invariant
proper metric and a discrete topology, acting by isometries, properly discontinuously, and
cocompactly on a proper metric space `α`, is coarsely equivalent to `α` via the
orbit map `g ↦ g • x₀`. -/
@[to_additive
/-- **Coarse Švarc–Milnor lemma** (metric specialization). An additive group `G` with a
left-invariant proper metric and a discrete topology, acting by isometries,
properly discontinuously, and cocompactly on a proper metric space `α`,
is coarsely equivalent to `α` via the orbit map `g ↦ g +ᵥ x₀`. -/]
noncomputable def mulOrbitMetricCoarseEquiv
  [ProperSpace G] [DiscreteTopology G]
  [IsIsometricSMul G G] [ProperSpace α]
  [IsIsometricSMul G α] [ProperlyDiscontinuousSMul G α]
  [CompactSpace (MulAction.orbitRel.Quotient G α)] (x₀ : α) : G ≃ᶜ α :=
  have h := exists_smul_closedBall_eq_univ G x₀
  have f : ∀ x, ∃ g : G, x ∈ g • closedBall x₀ (max h.choose 0) := fun x ↦
    let ⟨g, _, y, hy, hgy⟩ := mem_image2.mp (h.choose_spec ▸ mem_univ x)
    ⟨g, mem_smul_set.mpr ⟨y, closedBall_subset_closedBall (le_max_left ..) hy, hgy⟩⟩
  mulOrbitCoarseEquiv
    isBounded_closedBall.isCoarselyBounded
    (mem_closedBall_self (le_max_right ..))
    (fun x ↦ (f x).choose_spec)
    ⟨isControlledMap_smul continuous_of_discreteTopology, isCoarselyProperMap_smul x₀⟩

end Metric
