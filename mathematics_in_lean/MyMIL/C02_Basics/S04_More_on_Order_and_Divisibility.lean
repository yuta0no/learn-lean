module
public import MIL.Common
public import Mathlib.Basic.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (le_max_left  a b : a ≤ max a b)
#check (le_max_right  a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  apply h
  apply h

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  . show min (min a b) c ≤ min a (min b c)
    apply le_min
    . apply le_trans (min_le_left (min a b) c)
      apply min_le_left
    . apply le_min
      . apply le_trans (min_le_left (min a b) c)
        apply min_le_right
      . apply min_le_right
  . show  min a (min b c) ≤ min (min a b) c
    apply le_min
    . apply le_min
      . apply min_le_left
      . apply le_trans (min_le_right a (min b c))
        apply min_le_left
    . apply le_trans (min_le_right a (min b c))
      apply min_le_right


#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
#check add_sub_cancel_right

example : |a| - |b| ≤ |a - b| := by
  have h : |a| + |b| ≤ |a - b| + |b| + |b| := by
    calc
      |a| + |b| = |a + b - b| + |b| := by rw [add_sub_cancel_right]
      _ = |(a - b) + b| + |b| := by rw [add_sub_cancel_right, sub_add_cancel]
      _ ≤ |a - b| + |b| + |b| := by
        gcongr
        exact abs_add_le (a - b) b
  linarith


example : |a| - |b| ≤ |a - b| := by
  have h : |a| ≤ |a - b| + |b| := by
    calc
      |a| = |(a - b) + b| := by rw [sub_add_cancel]
      _ ≤ |a - b| + |b| := abs_add_le (a - b) b
  linarith

example : |a| - |b| ≤ |a - b| := by
  have h := abs_add_le (a - b) b
  rw [sub_add_cancel] at h
  linarith

variable (x y z : Nat)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left


variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : dist x x ≤ dist x y + dist y x := dist_triangle x y x
  rw [dist_self, dist_comm y x] at h
  linarith


end
