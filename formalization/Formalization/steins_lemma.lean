import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
/-! theorem 1 in the group meeting on 13/10/2026 -/
open MeasureTheory ProbabilityTheory NNReal Real

variable (μ : ℝ) (v : ℝ≥0)

def X : ℝ → ℝ := id


lemma hasDerivAt_gaussianPDFReal (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v) (-((x - μ) / v) * gaussianPDFReal μ v x) x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  -- derivative of the exponent -(x-μ)²/(2v)
  have h : HasDerivAt (fun x : ℝ => -(x - μ) ^ 2 / (2 * (v : ℝ))) (-((x - μ) / v)) x := by
    refine ((((hasDerivAt_id' x).sub_const μ).pow 2).neg.div_const (2 * (v : ℝ))).congr_deriv ?_
    field_simp
    try ring
  -- multiply exp(...) by the normalising constant; Lean unfolds gaussianPDFReal to match
  refine (h.exp.const_mul (√(2 * π * v))⁻¹).congr_deriv ?_
  unfold gaussianPDFReal
  ring


/-! ### Step 1: integrability against `gaussianReal` ↔ against Lebesgue measure with the density
Hints: `gaussianReal_of_var_ne_zero`, `integrable_withDensity_iff_integrable_smul'`,
`measurable_gaussianPDF`, `gaussianPDF_lt_top`, `toReal_gaussianPDF`, `smul_eq_mul`. -/

lemma integrable_gaussianReal_iff (hv : v ≠ 0) {f : ℝ → ℝ} :
    Integrable f (gaussianReal μ v) ↔ Integrable (fun x => gaussianPDFReal μ v x * f x) := by
  sorry

/-! ### Step 2: `g` is integrable whenever `(x - μ) * g x` is and `g` is continuous
Idea: `|g x| ≤ |(x - μ) * g x| + C`, where `C` bounds `|g|` on `[μ - 1, μ + 1]`.
Hints: `IsCompact.exists_bound_of_continuousOn`, `Integrable.mono'`, `integrable_const`. -/


lemma integrable_of_integrable_mul_sub (g : ℝ → ℝ) (hg : Continuous g)
    (h1 : Integrable (fun x => (x - μ) * g x) (gaussianReal μ v)) :
    Integrable g (gaussianReal μ v) := by
  sorry


/-! ### Step 3: Stein's identity against Lebesgue measure (integration by parts)
Hints: `integral_mul_deriv_eq_deriv_mul_of_integrable` with `u := g`, `v := gaussianPDFReal μ v`
and `hasDerivAt_gaussianPDFReal`; reshape hypotheses with `Integrable.const_mul`,
`Integrable.congr`; pull constants out with `integral_const_mul`. -/

lemma stein_lebesgue (hv : v ≠ 0) (g : ℝ → ℝ) (hg : Differentiable ℝ g)
    (h1 : Integrable (fun x => gaussianPDFReal μ v x * ((x - μ) * g x)))
    (h2 : Integrable (fun x => gaussianPDFReal μ v x * deriv g x))
    (h3 : Integrable (fun x => gaussianPDFReal μ v x * g x)) :
    ∫ x, gaussianPDFReal μ v x * ((x - μ) * g x)
      = (v : ℝ) * ∫ x, gaussianPDFReal μ v x * deriv g x := by
  sorry



/-! ### Stein's lemma
Plan: get `h3` from Step 2, rewrite both integrals with
`integral_gaussianReal_eq_integral_smul hv` + `smul_eq_mul`, then apply Step 3 with the
hypotheses converted by Step 1. -/

theorem stein (hv : v ≠ 0) (g : ℝ → ℝ) (hg : Differentiable ℝ g) (h1 : Integrable (fun x => (x - μ) * g x) (gaussianReal μ v)) (h2 : Integrable (fun x => deriv g x) (gaussianReal μ v)) :
  ∫ x, (x - μ) * g x ∂(gaussianReal μ v) = (v : ℝ) * ∫ x, deriv g x ∂(gaussianReal μ v) := by
  sorry
