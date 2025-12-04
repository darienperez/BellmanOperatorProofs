import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

/-- A simple finite MDP model over states `S` and actions `A`. -/
structure MDP (S A : Type) [Fintype S] [Fintype A] where
  γ : ℝ
  γ_nonneg : 0 ≤ γ
  R : S → A → ℝ
  P : S → A → S → ℝ
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  P_row_sum_one : ∀ s a, ∑ s', P s a s' = 1

namespace MDP

variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq A] [Nonempty A]

-- Value functions are just real-valued functions on states.
abbrev V (M : MDP S A) : Type _ := S → ℝ

variable {M : MDP S A}


noncomputable def T (V : M.V) : M.V :=
  fun s =>
    Finset.univ.sup'
      (by
        simpa using (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty))
      (fun a : A =>
        M.R s a + M.γ * ∑ s', M.P s a s' * V s')


/-- Helper: expectation w.r.t. one (s,a) row of `P`. -/
def expect (V : M.V) (s : S) (a : A) : ℝ :=
  ∑ s', M.P s a s' * V s'

/-- `expect` is monotone in `V` if the coefficients are nonnegative. -/
lemma expect_mono {V W : M.V}
    (hVW : ∀ s, V s ≤ W s) :
    ∀ s a, M.expect V s a ≤ M.expect W s a := by
  intro s a
  -- `expect` expands to a finite sum; use monotonicity of sums
  -- and `M.P_nonneg` together with `hVW`.
  -- This is a good place for `have` + `linarith` or `simp` + `sum_le_sum`.
  sorry

/-- The Bellman operator `T` is monotone: if `V ≤ W` pointwise, then `T V ≤ T W` pointwise. -/
lemma T_monotone {V W : M.V}
    (hVW : ∀ s, V s ≤ W s) :
    ∀ s, M.T V s ≤ M.T W s := by
  intro s
  -- Expand the definition of `T`
  dsimp [T]
  -- We want to show: sup over actions of (R + γ * expect V) ≤ sup over actions of (R + γ * expect W)
  -- Step 1: pointwise inequality for each action:
  have h_point : ∀ a : A,
      M.R s a + M.γ * M.expect V s a ≤
      M.R s a + M.γ * M.expect W s a := by
    intro a
    -- use `expect_mono` and `γ_nonneg`
    have hx := M.expect_mono hVW s a
    have hγ := M.γ_nonneg
    -- R s a cancels; γ * ... is monotone when γ ≥ 0
    have : M.γ * M.expect V s a ≤ M.γ * M.expect W s a := by
      exact mul_le_mul_of_nonneg_left hx hγ
    linarith
  -- Step 2: lift the pointwise inequality to the Finset.sup over all actions.
  -- This is your "sup preserves order" lemma specialized to `Finset.univ`.
  -- You can prove a helper lemma:
  --   lemma sup_mono_univ {β} [LinearOrder β] [OrderBot β]
  --     (f g : A → β) (h : ∀ a, f a ≤ g a) :
  --     (Finset.univ.sup f) ≤ (Finset.univ.sup g) := ...
  -- Then just apply it to these two functions.
  have : Finset.univ.sup (fun a : A =>
      M.R s a + M.γ * M.expect V s a)
      ≤
      Finset.univ.sup (fun a : A =>
      M.R s a + M.γ * M.expect W s a) := by
    -- use your Week-2-style sup-mono lemma here
    sorry
  exact this

end MDP
