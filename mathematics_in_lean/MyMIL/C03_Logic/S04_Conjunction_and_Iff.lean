module
public import MIL.Common
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by
    apply le_antisymm
    . -- x ^ 2 ≤ 0
      linarith [sq_nonneg y]
    . --x ^ 2 ≥ 0
      exact sq_nonneg x
  eq_zero_of_pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  . rintro h
    constructor
    . exact aux h
    . rw [add_comm] at h
      exact aux h
  . rintro ⟨hx0, hy0⟩
    rw [hx0, hy0]
    norm_num

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  . rintro h
    constructor
    . exact aux h
    . rw [add_comm] at h
      exact aux h
  . rintro ⟨rfl, rfl⟩
    norm_num

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push Not
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [Monotone]
  push Not
  use 1, 2
  norm_num

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff]
  use 1, 2
  norm_num
