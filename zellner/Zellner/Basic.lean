import Mathlib

/-!
Formalization of Theorem 1 in Knoblauch, Jewson, and Damoulas (2019),
https://arxiv.org/abs/1904.02063.

As in the paper, we only assume `Z < ∞`, i.e. that `p₀ e^{-L}` is integrable.

The objective `E_q[L] + KL(q ‖ p₀)` is written as the single integral
`∫ q (L + log (q / p₀))`, as in the paper's proof. This agrees with the paper whenever
`E_q[L]` and `KL(q ‖ p₀)` are both finite, and stays well defined at `qB` even when
`E_{qB}[L] = -∞`. The negative part of the integrand is always integrable, so a `q`
whose integrand is not integrable has objective `+∞` and is excluded from `Admissible`
without loss.
-/

open MeasureTheory Real

variable {Θ : Type*} [MeasureSpace Θ]

/-- `q` is a probability density function -/
structure IsDensity (q : Θ → ℝ) : Prop where
  meas   : Measurable q
  nonneg : ∀ θ, 0 ≤ q θ
  int    : Integrable q
  one    : ∫ θ, q θ = 1

/-- KL divergence: ∫ q log(q/p)

Note that Lean's conventions `log 0 = 0` and `x / 0 = 0` are used,
so this is only meaningful when `q = 0` almost everywhere on `{p = 0}`. -/
noncomputable def kl (q p : Θ → ℝ) : ℝ := ∫ θ, q θ * log (q θ / p θ)

structure Admissible (p₀ L q : Θ → ℝ) : Prop where
  dens : IsDensity q
  supp : ∀ᵐ θ, p₀ θ = 0 → q θ = 0
  int  : Integrable (fun θ ↦ q θ * (L θ + log (q θ / p₀ θ)))

/-- `E_q[L] + KL(q ‖ p₀)`, written as a single integral -/
noncomputable def objective (p₀ L q : Θ → ℝ) : ℝ :=
  ∫ θ, q θ * (L θ + log (q θ / p₀ θ))

noncomputable def Z (p₀ L : Θ → ℝ) : ℝ := ∫ θ, p₀ θ * exp (-L θ)
noncomputable def qB (p₀ L : Θ → ℝ) (θ : Θ) : ℝ := p₀ θ * exp (-L θ) / Z p₀ L

/-! 1. Pointwise inequalities for real numbers -/

lemma sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a → 0 < b) :
    a - b ≤ a * log (a / b) := by
  rcases ha.eq_or_lt with ha0 | hapos
  · -- case: a = 0
    rw [← ha0]
    simpa using hb
  · -- case: a > 0
    have hbpos : 0 < b := h hapos
    have h1 : log (b / a) ≤ b / a - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hbpos hapos)
    calc
      a - b = -(a * (b / a - 1)) := by field_simp; ring
      _ ≤ -(a * log (b / a)) := by
        have := mul_le_mul_of_nonneg_left h1 ha
        linarith
      _ = a * log (a / b) := by
        rw [Real.log_div hbpos.ne' hapos.ne', Real.log_div hapos.ne' hbpos.ne']
        ring

lemma mul_log_div_eq_sub_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a → 0 < b) :
    a * log (a / b) = a - b ↔ a = b := by
  constructor
  · -- proof for (→)
    intro heq
    rcases ha.eq_or_lt with ha0 | hapos
    · -- case: a = 0
      rw [← ha0] at heq
      simp at heq
      linarith
    · -- case: a > 0
      have hbpos := h hapos
      by_contra hne
      have hx : b / a ≠ 1 := by
        intro hba
        apply hne
        exact ((div_eq_one_iff_eq hapos.ne').mp hba).symm
      have h1 : log (b / a) < b / a - 1 :=
        Real.log_lt_sub_one_of_pos (div_pos hbpos hapos) hx
      have hlt : a - b < a * log (a / b) := by
        calc
          a - b = -(a * (b / a - 1)) := by field_simp; ring
          _ < -(a * log (b / a)) := by
            have := mul_lt_mul_of_pos_left h1 hapos
            linarith
          _ = a * log (a / b) := by
            rw [Real.log_div hbpos.ne' hapos.ne', Real.log_div hapos.ne' hbpos.ne']
            ring
      -- a - b < a * log (a / b) = a - b (∵ hlt, heq)
      linarith
  · -- proof for (←)
    intro hab
    rw [hab]
    by_cases hb0 : b = 0
    · simp [hb0]
    · rw [div_self hb0, Real.log_one, mul_zero, sub_self]

/-! 2. Gibbs's inequality on pdf -/

/-- lemma : KL(q || q) = 0 -/
lemma kl_self (q : Θ → ℝ) : kl q q = 0 := by
  simp [kl]

/-- KL(q || r) = ∫ (q log (q/r) - q + r) -/
lemma kl_eq_integral_gibbs {q r : Θ → ℝ} (hq : IsDensity q) (hr : IsDensity r)
    (hint : Integrable (fun θ ↦ q θ * log (q θ / r θ))) :
    kl q r = ∫ θ, (q θ * log (q θ / r θ) - q θ + r θ) := by
  have h1 : Integrable (fun θ ↦ q θ * log (q θ / r θ) - q θ) := hint.sub hq.int
  rw [integral_add h1 hr.int, integral_sub hint hq.int, hq.one, hr.one, kl]
  norm_num

/-- lemma : KL(q || r) ≥ 0 -/
lemma kl_nonneg {q r : Θ → ℝ} (hq : IsDensity q) (hr : IsDensity r)
    (hsupp : ∀ᵐ θ, 0 < q θ → 0 < r θ)
    (hint : Integrable (fun θ ↦ q θ * log (q θ / r θ))) :
    0 ≤ kl q r := by
  rw [kl_eq_integral_gibbs hq hr hint]
  have h0 : ∀ᵐ θ, 0 ≤ q θ * log (q θ / r θ) - q θ + r θ := by
    filter_upwards [hsupp] with θ hθ
    have := sub_le_mul_log_div (hq.nonneg θ) (hr.nonneg θ) hθ
    linarith
  exact integral_nonneg_of_ae h0

/-- lemma: KL(q || r) = 0 → q = r (a.e.) -/
lemma ae_eq_of_kl_eq_zero {q r : Θ → ℝ} (hq : IsDensity q) (hr : IsDensity r)
    (hsupp : ∀ᵐ θ, 0 < q θ → 0 < r θ)
    (hint : Integrable (fun θ ↦ q θ * log (q θ / r θ)))
    (h : kl q r = 0) :
    ∀ᵐ θ, q θ = r θ := by
  rw [kl_eq_integral_gibbs hq hr hint] at h
  have hnonneg : ∀ᵐ θ, 0 ≤ q θ * log (q θ / r θ) - q θ + r θ := by
    filter_upwards [hsupp] with θ hθ
    have := sub_le_mul_log_div (hq.nonneg θ) (hr.nonneg θ) hθ
    linarith
  have hgi : Integrable (fun θ ↦ q θ * log (q θ / r θ) - q θ + r θ) :=
    (hint.sub hq.int).add hr.int
  have hzero : (fun θ ↦ q θ * log (q θ / r θ) - q θ + r θ) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hgi).mp h
  filter_upwards [hzero, hsupp] with θ hθ0 hθs
  have h1 : q θ * log (q θ / r θ) - q θ + r θ = 0 := hθ0
  have h2 : q θ * log (q θ / r θ) = q θ - r θ := by linarith
  exact (mul_log_div_eq_sub_iff (hq.nonneg θ) (hr.nonneg θ) hθs).mp h2

/-! 3. Normalizing constant Z -/

lemma Z_pos {p₀ L : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hZint : Integrable (fun θ ↦ p₀ θ * exp (-L θ))) :
    0 < Z p₀ L := by
  have hnonneg : ∀ᵐ θ, 0 ≤ p₀ θ * exp (-L θ) :=
    Filter.Eventually.of_forall fun θ ↦ mul_nonneg (hp₀.nonneg θ) (exp_pos _).le
  have hZ0 : 0 ≤ Z p₀ L := integral_nonneg_of_ae hnonneg
  rcases hZ0.eq_or_lt with h0 | hpos
  · -- case Z = 0; derive a contradiction
    exfalso
    have hzero : (fun θ ↦ p₀ θ * exp (-L θ)) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnonneg hZint).mp h0.symm
    have hp0 : p₀ =ᵐ[volume] 0 := by
      filter_upwards [hzero] with θ hθ
      have h1 : p₀ θ * exp (-L θ) = 0 := hθ
      exact (mul_eq_zero.mp h1).resolve_right (exp_pos _).ne'
    have hone := hp₀.one
    rw [integral_congr_ae hp0] at hone
    simp at hone  -- 0 = 1; contradiction
  · -- case Z > 0
    exact hpos

/-! 4. Generalized posterior qB -/

lemma qB_pos {p₀ L : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hZint : Integrable (fun θ ↦ p₀ θ * exp (-L θ))) {θ : Θ} (hθ : 0 < p₀ θ) :
    0 < qB p₀ L θ := by
  rw [qB]
  exact div_pos (mul_pos hθ (exp_pos _)) (Z_pos hp₀ hZint)

lemma supp_qB {p₀ L q : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hZint : Integrable (fun θ ↦ p₀ θ * exp (-L θ))) (hq : Admissible p₀ L q) :
    ∀ᵐ θ, 0 < q θ → 0 < qB p₀ L θ := by
  filter_upwards [hq.supp] with θ hθs
  intro hqpos
  have hθ : 0 < p₀ θ := by
    rcases (hp₀.nonneg θ).eq_or_lt with hp0 | hppos
    · -- case p₀ θ = 0
      apply absurd (hθs hp0.symm) hqpos.ne'
    · -- case p₀ θ > 0
      exact hppos
  exact qB_pos hp₀ hZint hθ

lemma isDensity_qB {p₀ L : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hZint : Integrable (fun θ ↦ p₀ θ * exp (-L θ))) :
    IsDensity (qB p₀ L) where
  meas := (hp₀.meas.mul hL.neg.exp).div_const _
  nonneg := by
    intro θ
    have hZ : 0 < Z p₀ L := Z_pos hp₀ hZint
    have hp : 0 ≤ p₀ θ := hp₀.nonneg θ
    unfold qB
    positivity
  int := hZint.div_const _
  one := by
    have hZ := Z_pos hp₀ hZint
    unfold qB
    rw [integral_div, div_eq_one_iff_eq hZ.ne']
    rfl

lemma mul_log_div_qB_p₀ {p₀ L : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hZint : Integrable (fun θ ↦ p₀ θ * exp (-L θ))) (θ : Θ) :
    qB p₀ L θ * log (qB p₀ L θ / p₀ θ) = qB p₀ L θ * (-L θ - log (Z p₀ L)) := by
  rcases (hp₀.nonneg θ).eq_or_lt with hp0 | hppos
  · -- case p₀ θ = 0
    unfold qB
    rw [← hp0]
    norm_num
  -- case p₀ θ > 0
  have hZ := Z_pos hp₀ hZint
  have hqB := qB_pos hp₀ hZint hppos
  calc
    qB p₀ L θ * log (qB p₀ L θ / p₀ θ)
    _ = qB p₀ L θ * log (qB p₀ L θ) - qB p₀ L θ * log (p₀ θ) := by
      rw [log_div hqB.ne' hppos.ne']
      ring
    _ = qB p₀ L θ * log (p₀ θ * exp (-L θ) / Z p₀ L) - qB p₀ L θ * log (p₀ θ) := rfl
    _ = qB p₀ L θ * log (p₀ θ) + qB p₀ L θ * (-L θ) + qB p₀ L θ * (-log (Z p₀ L))
        - qB p₀ L θ * log (p₀ θ) := by
      rw [log_div (mul_pos hppos (exp_pos _)).ne' hZ.ne',
        log_mul hppos.ne' (exp_pos _).ne', log_exp]
      ring
    _ = qB p₀ L θ * (-L θ - log (Z p₀ L)) := by ring

lemma admissible_qB {p₀ L : Θ → ℝ} (hp₀ : IsDensity p₀) (hL : Measurable L)
    (hZint : Integrable (fun θ ↦ p₀ θ * exp (-L θ))) :
    Admissible p₀ L (qB p₀ L) where
  dens := isDensity_qB hp₀ hL hZint
  supp := by
    refine Filter.Eventually.of_forall (fun θ ↦ ?_)
    intro hθ
    unfold qB
    rw [hθ]
    simp
  int := by
    have hq := isDensity_qB hp₀ hL hZint
    have h : (fun θ ↦ qB p₀ L θ * (L θ + log (qB p₀ L θ / p₀ θ)))
        = fun θ ↦ -(qB p₀ L θ * log (Z p₀ L)) := by
      funext θ
      rw [mul_add, mul_log_div_qB_p₀ hp₀ hZint θ]
      ring
    rw [h]
    exact (hq.int.mul_const _).neg

/-! 5. Key identities -/

lemma mul_log_div_qB_ae {p₀ L q : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hZint : Integrable (fun θ ↦ p₀ θ * exp (-L θ))) (hq : Admissible p₀ L q) :
    (fun θ ↦ q θ * log (q θ / qB p₀ L θ)) =ᵐ[volume]
      fun θ ↦ q θ * (L θ + log (q θ / p₀ θ)) + q θ * log (Z p₀ L) := by
  filter_upwards [hq.supp] with θ hθs
  rcases (hq.dens.nonneg θ).eq_or_lt with hq0 | hqpos
  · -- case q θ = 0
    rw [← hq0]
    simp
  -- case q θ > 0
  have hppos : 0 < p₀ θ := by
    rcases (hp₀.nonneg θ).eq_or_lt with hpz | hppos
    · -- case p₀ θ = 0
      exact absurd (hθs hpz.symm) hqpos.ne'
    · -- case p₀ θ > 0
      exact hppos
  have hZ := Z_pos hp₀ hZint
  have hqB := qB_pos hp₀ hZint hppos
  calc
    q θ * log (q θ / qB p₀ L θ)
    _ = q θ * log (q θ) - q θ * log (qB p₀ L θ) := by rw [log_div hqpos.ne' hqB.ne']; ring
    _ = q θ * log (q θ) - q θ * log (p₀ θ * exp (-L θ) / Z p₀ L) := by rw [qB]
    _ = q θ * log (q θ) - q θ * log (p₀ θ) + q θ * L θ + q θ * log (Z p₀ L) := by
      rw [log_div (mul_pos hppos (exp_pos _)).ne' hZ.ne',
        log_mul hppos.ne' (exp_pos _).ne', log_exp]
      ring
    _ = q θ * (L θ + log (q θ / p₀ θ)) + q θ * log (Z p₀ L) := by
      rw [log_div hqpos.ne' hppos.ne']
      ring

lemma integrable_mul_log_div_qB {p₀ L q : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hZint : Integrable (fun θ ↦ p₀ θ * exp (-L θ))) (hq : Admissible p₀ L q) :
    Integrable (fun θ ↦ q θ * log (q θ / qB p₀ L θ)) := by
  have h := mul_log_div_qB_ae hp₀ hZint hq
  have hint : Integrable (fun θ ↦ q θ * (L θ + log (q θ / p₀ θ)) + q θ * log (Z p₀ L)) :=
    hq.int.add (hq.dens.int.mul_const _)
  exact hint.congr h.symm

lemma objective_eq {p₀ L q : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hZint : Integrable (fun θ ↦ p₀ θ * exp (-L θ))) (hq : Admissible p₀ L q) :
    objective p₀ L q = kl q (qB p₀ L) - log (Z p₀ L) := by
  unfold objective kl
  rw [integral_congr_ae (mul_log_div_qB_ae hp₀ hZint hq),
    integral_add hq.int (hq.dens.int.mul_const (log (Z p₀ L))), integral_mul_const,
    hq.dens.one]
  ring

/-! Main theorem -/

theorem gibbs_bayes_density
    (p₀ L : Θ → ℝ) (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hZint : Integrable (fun θ ↦ p₀ θ * exp (-L θ))) :
    Admissible p₀ L (qB p₀ L) ∧
    (∀ q, Admissible p₀ L q → objective p₀ L (qB p₀ L) ≤ objective p₀ L q) ∧
    (∀ q, Admissible p₀ L q → objective p₀ L q = objective p₀ L (qB p₀ L) →
      ∀ᵐ θ, q θ = qB p₀ L θ) := by
  have hB : Admissible p₀ L (qB p₀ L) := admissible_qB hp₀ hL hZint
  have hobjB : objective p₀ L (qB p₀ L) = -log (Z p₀ L) := by
    rw [objective_eq hp₀ hZint hB, kl_self, zero_sub]
  -- achieve the first goal
  refine ⟨hB, ?_, ?_⟩
  · -- optimality of q = qB: objective q = kl q qB - log Z ≥ kl qB qB - log Z = - log Z
    intro q hq
    rw [hobjB, objective_eq hp₀ hZint hq]
    have hkl := kl_nonneg hq.dens (isDensity_qB hp₀ hL hZint)
      (supp_qB hp₀ hZint hq) (integrable_mul_log_div_qB hp₀ hZint hq)
    linarith
  · -- uniqueness of optimal q
    intro q hq heq
    rw [hobjB, objective_eq hp₀ hZint hq] at heq
    apply ae_eq_of_kl_eq_zero hq.dens (isDensity_qB hp₀ hL hZint)
      (supp_qB hp₀ hZint hq) (integrable_mul_log_div_qB hp₀ hZint hq)
    linarith
