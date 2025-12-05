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

abbrev V (S : Type) := S → ℝ

namespace MDP
variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq A] [Nonempty A]

def bellmanInner (M : MDP S A) (v : V S) (s : S) (a : A) : ℝ :=
  M.R s a + M.γ * ∑ s', M.P s a s' * v s'

def T (M : MDP S A) (v : V S) (s : S) : ℝ :=
  (Finset.univ : Finset A).sup' --Chat assisted. Originally Finset.sup' (Finset.univ : Finset A) ...
    (by simp)
    (fun a : A => bellmanInner M v s a)

lemma T_monotone
  (M : MDP S A)
  {V' W' : S → ℝ}
  (hVW : ∀ s, V' s ≤ W' s) :
  ∀ s, T M V' s ≤ T M W' s := by
    sorry

end MDP
