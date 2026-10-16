module
public import MIL.Common
public import Mathlib.Basic.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε


example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert! (mul_lt_mul_iff_left₀ _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert! (mul_lt_mul_iff_left₀ _).2 h
  · rw [one_mul]
  . exact lt_trans zero_lt_one h

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert! (mul_lt_mul_iff_left₀ (lt_trans zero_lt_one h)).2 h
  · rw [one_mul]

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos


theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have hst1 : |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by
    congr; ring
  have hst2 : |(s n - a) + (t n - b)| ≤ |s n - a| + |t n - b| := by
    apply abs_add_le (s n - a) (t n - b)
  have hst : |s n + t n - (a + b)| ≤ |s n - a| + |t n - b| := by linarith
  have hsn : |s n - a| < ε / 2 := hs n (le_of_max_le_left hn)
  have htn : |t n - b| < ε / 2 := ht n (le_of_max_le_right hn)
  linarith


theorem convergesTo_add_ {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  calc
        |s n + t n - (a + b)|
    _ = |s n - a + (t n - b)| := by congr 1; ring
    _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs n (le_of_max_le_left hn)) (ht n (le_of_max_le_right hn))
    _ = ε := by ring
