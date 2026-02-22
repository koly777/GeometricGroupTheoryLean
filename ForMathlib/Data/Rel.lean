/-
Copyright (c) 2026 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
import Mathlib.Data.Rel

variable {α β γ δ : Type*}

namespace SetRel

/-- The residual `R ⧵ S` where `x ~[R ⧵ S] z` iff every `R`-successor of `x`
is an `S`-predecessor of `z`. -/
def res (R : SetRel α β) (S : SetRel β γ) : SetRel α γ :=
  {p | ∀ y, p.1 ~[R] y → y ~[S] p.2}

scoped infixr:70 " ⧵ " => res

variable {R : SetRel α β} {S : SetRel β γ}

@[simp]
theorem mem_res {R : SetRel α β} {S : SetRel β γ} {x z} :
    x ~[R ⧵ S] z ↔ ∀ y, x ~[R] y → y ~[S] z := .rfl

theorem compl_comp : (R ○ S)ᶜ = R ⧵ Sᶜ :=
  Set.ext fun _ ↦ not_exists.trans <| forall_congr' fun _ ↦
    not_and.trans <| imp_congr_right fun _ ↦ .rfl

theorem iterate_res_compl (s : SetRel α α) (n : ℕ) :
    (s ⧵ ·)^[n] sᶜ = ((s ○ ·)^[n] s)ᶜ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, SetRel.compl_comp]

theorem mem_comp_comp {x a b y} {R : SetRel α β} {S : SetRel β γ} {T : SetRel γ δ}
    (hR : (x, a) ∈ R) (hS : (a, b) ∈ S) (hT : (b, y) ∈ T) :
    (x, y) ∈ (R.comp S).comp T :=
  ⟨b, ⟨a, hR, hS⟩, hT⟩

variable {R R₁ R₂ : SetRel α β} {b : β}

-- See https://github.com/leanprover-community/mathlib4/pull/33077 for ball API

variable (R b) in
/-- The ball of `b : β` with respect to a relation between `α` and `β` is the set of `a : α` related
to `b`. -/
def ball : Set α := {a | a ~[R] b}

@[simp] lemma mem_ball {b a} : a ∈ R.ball b ↔ a ~[R] b := .rfl

lemma ball_mono (h : R₁ ⊆ R₂) (b : β) : R₁.ball b ⊆ R₂.ball b := fun _a hab ↦ h hab

variable (R₁ R₂ b) in
lemma ball_inter : ball (R₁ ∩ R₂) b = ball R₁ b ∩ ball R₂ b := rfl

lemma ball_iInter {ι} (R : ι → Set (α × β)) (b : β) : ball (⋂ i, R i) b = ⋂ i, ball (R i) b := by
  ext; simp

end SetRel

theorem Antitone.res {ι : Type*} [Preorder ι] {α β γ : Type*}
    {f : ι → SetRel α β} {g : ι → SetRel β γ}
    (hf : Antitone f) (hg : Monotone g) : Monotone (fun s ↦ (f s).res (g s)) :=
  fun _ _ h _ hr y hy ↦ hg h (hr y (hf h hy))
