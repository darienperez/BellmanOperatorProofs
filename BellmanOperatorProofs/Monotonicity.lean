import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

structure MDP (S A : Type) [Fintype S] [Fintype A] where
  γ : ℝ
  γ_nonneg : 0 ≤ γ
  R : S → A → ℝ
  P : S → A → S → ℝ
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  P_row_sum_one : ∀ s a, ∑ s', P s a s' = 1

namespace MDP
variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq A] [Nonempty A]
variable (M : MDP S A)
abbrev V S := S → ℝ

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

def bellmanInner (v : V S) (s : S) (a : A) : ℝ :=
  M.R s a + M.γ * ∑ s', M.P s a s' * v s'

lemma bellman_inner_mono
  {V' W' : V S}
  (hVW : ∀ s, V' s ≤ W' s) :
  ∀ s a,
    bellmanInner M V' s a ≤ bellmanInner M W' s a := by
    intro s a
    have hsum :
      ∑ s', M.P s a s' * V' s'
        ≤
      ∑ s', M.P s a s' * W' s' :=
      expect_mono
        (fun s' => hVW s')
        (fun s' => M.P_nonneg s a s')
    have hmul :
      M.γ * ∑ s', M.P s a s' * V' s'
       ≤
      M.γ * ∑ s', M.P s a s' * W' s' :=
      mul_le_mul_of_nonneg_left hsum M.γ_nonneg
    exact add_le_add_left hmul (M.R s a)

def T (M : MDP S A) (v : V S) (s : S) : ℝ :=
  (Finset.univ : Finset A).sup' --Chat assisted. Originally Finset.sup' (Finset.univ : Finset A) ...
    (by simp)
    (fun a : A => bellmanInner M v s a)

#check T

lemma T_monotone
  (M : MDP S A)
  {V' W' : S → ℝ}
  (hVW : ∀ s, V' s ≤ W' s) :
  ∀ s, T M V' s ≤ T M W' s :=
    bellman_inner_mono (∀ s, hVW)
    sorry

end MDP
