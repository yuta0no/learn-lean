import Mathlib

open Finset

variable {Ω : Type} [Fintype Ω]
variable (p : Ω → ℝ)
variable (hp_sum : ∑ ω, p ω = 1)

section DiscreteProbability


-- E[X] = Σ X(ω) p(ω)
noncomputable def E (X : Ω → ℝ) : ℝ :=
  ∑ ω, X ω * p ω


-- V[X] = E[X-E[X]]
noncomputable def V (X : Ω → ℝ) : ℝ :=
  E p (fun ω => (X ω - E p X)^2)


lemma E_add (X Y : Ω → ℝ) : E p (fun ω => X ω + Y ω) = E p X + E p Y := by
  unfold E
  have h : (fun ω => (X ω + Y ω) * p ω) = (fun ω => X ω * p ω + Y ω * p ω) := by
    ext ω; ring
  rw [h]
  exact sum_add_distrib


lemma E_sub (X Y : Ω → ℝ) : E p (fun ω => X ω - Y ω) = E p X - E p Y := by
  unfold E
  have h : (fun ω => (X ω - Y ω) * p ω) = (fun ω => X ω * p ω - Y ω * p ω) := by
    ext ω; ring
  rw [h]
  exact sum_sub_distrib (fun ω => X ω * p ω) (fun ω => Y ω * p ω)

lemma E_const_mul (c : ℝ) (X : Ω → ℝ) : E p (fun ω => c * X ω) = c * E p X := by
  unfold E
  have h : (fun ω => c * X ω * p ω) = (fun ω => c * (X ω * p ω)) := by
    ext ω; ring
  rw [h, ← mul_sum]


lemma E_const (c : ℝ) (hp_sum : ∑ ω, p ω = 1) : E p (fun _ => c) = c := by
  unfold E
  calc
    ∑ ω, c * p ω = c * ∑ ω, p ω := by rw [← mul_sum]
    _ = c * 1 := by rw [hp_sum]
    _ = c := by ring


-- E[(X-a)^2] = E[(X - E[X])^2 + (E[X] - a)^2]
-- = E[(X - E[X])^2] + (E[X] - a)^2 = V[X] + (E[X] - a)^2
theorem bias_variance_decomposition (hp_sum : ∑ ω, p ω = 1) (X : Ω → ℝ) (a : ℝ) :
  E p (fun ω => (X ω - a)^2) = V p X + (E p X - a)^2 := by
  have h_expand : (fun ω => (X ω - a)^2) = (fun ω => (X ω - E p X)^2 + 2 * (X ω - E p X) * (E p X - a) + (E p X - a)^2) := by
    ext ω; ring
  rw [h_expand]
  rw [E_add, E_add]
  have h_middle : E p (fun ω => 2 * (X ω - E p X) * (E p X - a)) = 0 := by
    have h_rearrange : (fun ω => 2 * (X ω - E p X) * (E p X - a)) = (fun ω => 2 * (E p X - a) * (X ω - E p X)) := by
      ext ω; ring
    rw [h_rearrange]
    rw [E_const_mul]
    have h_zero : E p (fun ω => X ω - E p X) = 0 := by
      rw [E_sub, E_const (hp_sum := hp_sum)]
      ring
    rw [h_zero]
    ring
  have h_right : E p (fun _ => (E p X - a)^2) = (E p X - a)^2 := by
    rw [E_const (hp_sum := hp_sum)]
  have h_V : E p (fun ω => (X ω - E p X)^2) = V p X := rfl
  rw [h_middle, h_right, h_V]
  ring

end DiscreteProbability
