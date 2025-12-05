import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-
  1.) expect_mono
-/
lemma expect_mono
  {ι : Type} [Fintype ι]
  {f g w : ι → ℝ}
  (hfg : ∀ i, f i ≤ g i)
  (hw : ∀ i, 0 ≤ w i)
  : ∑ i , w i * f i ≤ ∑ i , w i * g i := by
    apply Finset.sum_le_sum
    intro i hi
    have h1 : f i ≤ g i := hfg i
    have h2 : 0 ≤ w i := hw i
    exact mul_le_mul_of_nonneg_left h1 h2

/-
  2.) sup_mono
-/
lemma sup_mono
  {ι : Type} [Fintype ι]
  {β : Type} [LinearOrder β] [OrderBot β]
  {f g : ι → β}
  (hfg : ∀ i, f i ≤ g i) :
  Finset.univ.sup f ≤ Finset.univ.sup g := by
    apply Finset.sup_le
    intro i hi
    have h1 : f i ≤ g i := hfg i
    have h2 : g i ≤ Finset.univ.sup g := by
      exact Finset.le_sup hi
    exact le_trans h1 h2

/-
  3.) sup_of_add_mono
-/
lemma sup_of_add_mono
  {ι : Type} [Fintype ι]
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
  4.) mul_mono
-/
lemma mul_mono
  {ι : Type} [Fintype ι]
  {γ : ℝ}
  (f g : ι → ℝ)
  (hγ : 0 ≤ γ)
  (hfg : ∀ i, f i ≤ g i) :
  ∀ i, γ * f i ≤ γ * g i := by
    intro i
    have h1 : f i ≤ g i := hfg i
    exact mul_le_mul_of_nonneg_left h1 hγ


/-
  5.) bellman_inner_mono
-/
structure MDP (S A : Type) [Fintype S] [Fintype A] where
  {γ : ℝ} (γ_nonneg : 0 ≤ γ)
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
    exact add_le_add_left hmul (M.R s a)

end MDP
