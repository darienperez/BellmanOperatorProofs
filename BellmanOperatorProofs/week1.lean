import Mathlib

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
