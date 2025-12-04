import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
/-
  1.)
-/
example (x y : ℝ) : |x + y| ≤ |x| + |y| := abs_add_le x y

#check abs

example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  have hx1 : -|x| ≤ x := neg_abs_le x
  have hy1 : -|y| ≤ y := neg_abs_le y
  have hx2 : x ≤ |x| := le_abs_self x
  have hy2 : y ≤ |y| := le_abs_self y
  have hlow : -(|x| + |y|) ≤ x + y := by linarith
  have hhigh : x + y ≤ |x| + |y| := by linarith
  exact abs_le.mpr ⟨hlow, hhigh⟩

/-
  2.) Finite weighted sum monotonicity
-/
-- Given f i ≤ g i for all i, and w i ≥ 0, show:
lemma expect_mono
  {ι : Type} [Fintype ι]
  {f g w : ι → ℝ}
  (hfg : ∀ i, f i ≤ g i)
  (hw : ∀ i, 0 ≤ w i) :
  ∑ i, w i * f i ≤ ∑ i, w i * g i := by
    apply Finset.sum_le_sum
    intro i hi
    have h1 : f i ≤ g i := hfg i
    exact mul_le_mul_of_nonneg_left h1 (hw i)

/-
  3.) Supremum monotonicity over a finite set
-/
-- open scoped BigOperators

lemma sup_mono
  {ι : Type} [Fintype ι]
  {β : Type} [LinearOrder β] [OrderBot β]
  (f g : ι → β)
  (hfg : ∀ i, f i ≤ g i) :
  Finset.univ.sup f ≤ Finset.univ.sup g := by
    apply Finset.sup_le
    intro i hi
    have h1 := hfg i
    have h2 : g i ≤ Finset.univ.sup g := by
      exact Finset.le_sup hi
    exact le_trans h1 h2

/-
  4.) Monotonicity of a weighted sup

  Practice:
  - sum inside
  - sup outside
  - them together staying monotone
-/
lemma sup_of_add_mono
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {β : Type} [LinearOrder β] [OrderBot β] [Add β] [AddLeftMono β]
  {f g h : ι → β}
  (hfg : ∀ i, f i ≤ g i) :
  Finset.univ.sup (fun i => h i + f i)
    ≤
  Finset.univ.sup (fun i => h i + g i) := by
    apply sup_mono
    intro i
    have h1 : f i ≤ g i := hfg i
    exact add_le_add_left h1 (h i)

/-
  4.) Monotonicity of a weighted sup
-/
lemma mul_mono
  {ι : Type} [Fintype ι]
  {γ : ℝ} (hγ : 0 ≤ γ)
  {f g : ι → ℝ}
  (hfg : ∀ i, f i ≤ g i) :
  ∀ i, γ * f i ≤ γ * g i := by
    intro i
    have h1 : f i ≤ g i := hfg i
    exact mul_le_mul_of_nonneg_left h1 hγ


structure MDP (S A : Type) [Fintype S] [Fintype A] where
  γ : ℝ
  γ_nonneg : 0 ≤ γ
  R : S → A → ℝ
  P : S → A → S → ℝ
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  P_row_sum_one : ∀ s a, ∑ s', P s a s' = 1

namespace MDP

variable {S A : Type} [Fintype S] [Fintype A]
variable (M : MDP S A)

abbrev V (M : MDP S A) := S → ℝ

def bellmanInner (M : MDP S A) (v : M.V) (s : S) (a : A) : ℝ :=
  M.R s a + M.γ * ∑ s', M.P s a s' * v s'

lemma bellman_inner_mono
  {V W : M.V}
  (hVW : ∀ s, V s ≤ W s) :
  ∀ s a,
    M.bellmanInner V s a ≤ M.bellmanInner W s a := by
    intro s a
  -- same proof as before, but using M.γ_nonneg and M.P_nonneg
    have hsum :
      ∑ s', M.P s a s' * V s'
        ≤
      ∑ s', M.P s a s' * W s' :=
      expect_mono
        (fun s' => hVW s')
        (fun s' => M.P_nonneg s a s')
    have hmul :
      M.γ * ∑ s', M.P s a s' * V s'
        ≤
      M.γ * ∑ s', M.P s a s' * W s' :=
      mul_le_mul_of_nonneg_left hsum M.γ_nonneg
    have hadd :
      M.R s a + M.γ * ∑ s', M.P s a s' * V s'
        ≤
      M.R s a + M.γ * ∑ s', M.P s a s' * W s' :=
      add_le_add_left hmul (M.R s a)
    exact hadd
end MDP
