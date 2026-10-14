import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Ring

/-! ... -/

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

section ContinuousProbability

noncomputable def E (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ∂μ

noncomputable def V (X : Ω → ℝ) : ℝ :=
  E μ (fun ω => (X ω - E μ X)^2)

variable {X Y : Ω → ℝ}
variable (hX : Integrable X μ) (hY : Integrable Y μ)

lemma E_add (hX : Integrable X μ) (hY : Integrable Y μ) : E μ (fun ω => X ω + Y ω) = E μ X + E μ Y := by
  unfold E
  exact integral_add hX hY

lemma E_sub (hX : Integrable X μ) (hY : Integrable Y μ) : E μ (fun ω => X ω - Y ω) = E μ X - E μ Y := by
  unfold E
  exact integral_sub hX hY

lemma E_const_mul (c : ℝ) : E μ (fun ω => c * X ω) = c * E μ X := by
  unfold E
  exact integral_const_mul c X

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma E_const (c : ℝ) : E μ (fun _ => c) = c := by
  unfold E
  simp [integral_const]


theorem bias_variance_decomposition
  (a : ℝ)
  (h_int_X2 : Integrable (fun ω => (X ω - E μ X)^2) μ)
  (h_int_cross : Integrable (fun ω => 2 * (X ω - E μ X) * (E μ X - a)) μ) :
  E μ (fun ω => (X ω - a)^2) = V μ X + (E μ X - a)^2 := by

  have h_expand : (fun ω => (X ω - a)^2) =
    (fun ω => (X ω - E μ X)^2 + 2 * (X ω - E μ X) * (E μ X - a) + (E μ X - a)^2) := by
    ext ω; ring

  unfold V
  rw [h_expand]

  sorry

end ContinuousProbability
