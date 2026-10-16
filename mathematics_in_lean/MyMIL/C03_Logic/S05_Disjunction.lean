module
public import MIL.Common
public import Mathlib.Basic.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro hx; left; exact hx
  · rw [abs_of_neg h]
    intro hx; right; exact hx

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have hm : (x-1) * (x+1) = 0 := by linarith [h]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hm with h | h
  . rw [sub_eq_zero] at h
    left
    exact h
  . rw [add_eq_zero_iff_eq_neg] at h
    right
    exact h

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have hm : (x-1) * (x+1) = 0 := by linarith [h]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hm with h | h
  . left
    linarith
  . right
    linarith


example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have hxy : (x - y) * (x + y) = 0 := by linarith [h]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hxy with h | h
  . left; linarith
  . right; linarith

example (a b : ℝ) (h : a - b = 0) : a = b := by
  rw?
