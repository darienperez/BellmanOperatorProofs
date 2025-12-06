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

variable {S A : Type} [Fintype S] [Fintype A]
variable (M : MDP S A)

namespace MDP
abbrev V S := S → ℝ

lemma expect_mono -- refined
  {ι : Type} [Fintype ι]
  {f g w : ι → ℝ}
  (hfg : ∀ i, f i ≤ g i)
  (hw : ∀ i, 0 ≤ w i) :
  ∑ i, w i * f i ≤ ∑ i, w i * g i := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hfg i) (hw i)

def bellmanInner (v : V S) (s : S) (a : A) : ℝ :=
  M.R s a + M.γ * ∑ s', M.P s a s' * v s'

lemma bellman_inner_mono
  {V' W' : V S} [Nonempty S]
  (hVW : ∀ s, V' s ≤ W' s) :
  ∀ s a,
    bellmanInner M V' s a
       ≤
    bellmanInner M W' s a := by
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

lemma mono_of_bellman_inner -- refined
  {V' W' : V S} [Nonempty S]
  (hVW : ∀ s, V' s ≤ W' s) :
  ∀ s a,
    bellmanInner M V' s a
      ≤
    bellmanInner M W' s a := by
    intro s a
    have hsum :
      ∑ s', M.P s a s' * V' s'
        ≤
      ∑ s', M.P s a s' * W' s' :=
      expect_mono
        (fun s' => hVW s')
        (fun s' => M.P_nonneg s a s')
    unfold bellmanInner
    exact add_le_add_left (mul_le_mul_of_nonneg_left hsum M.γ_nonneg) (M.R s a)

lemma sup'_mono --This one was challenging but rewarding. Real numbers really are useless 😂
  {ι : Type} [Fintype ι] [Nonempty ι]
  {f g : ι → ℝ}
  (hfg : ∀ i, f i ≤ g i) :
  (Finset.univ : Finset ι).sup' (by exact Finset.univ_nonempty) f
    ≤
  (Finset.univ : Finset ι).sup' (by exact Finset.univ_nonempty) g := by
    have h0 : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
    apply Finset.sup'_le
    intro i hi
    have h1 : f i ≤ g i := hfg i
    have h2 : g i ≤ (Finset.univ : Finset ι).sup' h0 g :=
      Finset.le_sup' (s := (Finset.univ : Finset ι)) g (b := i) hi
    exact le_trans h1 h2

lemma mono_of_sup' -- refined
 {ι : Type} [Fintype ι][Nonempty ι]
 {f g : ι → ℝ}
 (h0 : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty)
 (hfg : ∀ i, f i ≤ g i) :
 (Finset.univ : Finset ι).sup' h0 f
    ≤
 (Finset.univ : Finset ι).sup' h0 g := by
  apply Finset.sup'_le
  intro i hi
  exact le_trans
    (hfg i) (Finset.le_sup' (s := (Finset.univ : Finset ι)) g (b := i) hi)

def T (M : MDP S A) (v : V S) (s : S) [Nonempty A] : ℝ :=
  (Finset.univ : Finset A).sup' --Chat assisted. Originally Finset.sup' (Finset.univ : Finset A) ...
    (by exact Finset.univ_nonempty)
    (fun a : A => bellmanInner M v s a)

#check T

lemma T_mono
  (M : MDP S A) [Nonempty S] [Nonempty A]
  {V' W' : S → ℝ}
  (hVW : ∀ s, V' s ≤ W' s) :
  ∀ s, T M V' s ≤ T M W' s := by
    intro s
    have hpoint :
      ∀ a,
      bellmanInner M V' s a ≤ bellmanInner M W' s a := by
        exact bellman_inner_mono M hVW s
    have hsup' :
      (Finset.univ : Finset A).sup'
        (by exact Finset.univ_nonempty)
        (fun a => bellmanInner M V' s a)
        ≤
      (Finset.univ : Finset A).sup'
       (by exact Finset.univ_nonempty)
       (fun a => bellmanInner M W' s a) := by
       exact sup'_mono
        (ι := A)
        (f := fun a => bellmanInner M V' s a)
        (g := fun a => bellmanInner M W' s a)
        hpoint
    exact hsup'

lemma mono_of_T -- refined
  (M : MDP S A) [Nonempty S] [Nonempty A]
  {V' W' : S → ℝ}
  (hVW : ∀ s, V' s ≤ W' s) :
  ∀ s, T M V' s≤ T M W' s := by
    unfold T
    intro s
    have hpoint :
      ∀ a,
        bellmanInner M V' s a ≤ bellmanInner M W' s a := by
          exact mono_of_bellman_inner M hVW s
    exact sup'_mono
        (ι := A)
        (f := fun a => bellmanInner M V' s a)
        (g := fun a => bellmanInner M W' s a)
        hpoint
end MDP
