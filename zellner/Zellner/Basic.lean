import Mathlib

/-! formalization of Theorem 1 in https://arxiv.org/abs/1904.02063 -/

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
  dens  : IsDensity q
  supp  : ∀ᵐ θ, p₀ θ = 0 → q θ = 0
  intL  : Integrable (fun θ ↦ q θ * L θ)
  intKL : Integrable (fun θ ↦ q θ * log (q θ / p₀ θ))

noncomputable def objective (p₀ L q : Θ → ℝ) : ℝ :=
  (∫ θ, q θ * L θ) + kl q p₀

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

lemma integrable_Z_integrand {p₀ L : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) :
    Integrable (fun θ ↦ p₀ θ * exp (-L θ)) := by
  sorry

lemma Z_pos {p₀ L : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) :
    0 < Z p₀ L := by
  sorry


/-! 4. Generalized posterior qB -/

lemma qB_pos {p₀ L : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) {θ : Θ} (hθ : 0 < p₀ θ) :
    0 < qB p₀ L θ := by
  sorry

lemma supp_qB {p₀ L q : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) (hq : Admissible p₀ L q) :
    ∀ᵐ θ, 0 < q θ → 0 < qB p₀ L θ := by
  sorry

lemma isDensity_qB {p₀ L : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) :
    IsDensity (qB p₀ L) := by
  sorry

lemma mul_log_div_qB_p₀ {p₀ L : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) (θ : Θ) :
    qB p₀ L θ * log (qB p₀ L θ / p₀ θ) = qB p₀ L θ * (-L θ - log (Z p₀ L)) := by
  sorry

lemma admissible_qB {p₀ L : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) :
    Admissible p₀ L (qB p₀ L) := by
  sorry


/-! 5. Key identities -/

lemma mul_log_div_qB_ae {p₀ L q : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) (hq : Admissible p₀ L q) :
    (fun θ ↦ q θ * log (q θ / qB p₀ L θ)) =ᵐ[volume]
      fun θ ↦ q θ * log (q θ / p₀ θ) + q θ * L θ + q θ * log (Z p₀ L) := by
  sorry

lemma integrable_mul_log_div_qB {p₀ L q : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) (hq : Admissible p₀ L q) :
    Integrable (fun θ ↦ q θ * log (q θ / qB p₀ L θ)) := by
  sorry

lemma objective_eq {p₀ L q : Θ → ℝ} (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) (hq : Admissible p₀ L q) :
    objective p₀ L q = kl q (qB p₀ L) - log (Z p₀ L) := by
  sorry


/-! Main theorem -/

theorem gibbs_bayes_density
    (p₀ L : Θ → ℝ) (hp₀ : IsDensity p₀)
    (hL : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) :
    Admissible p₀ L (qB p₀ L) ∧
    (∀ q, Admissible p₀ L q → objective p₀ L (qB p₀ L) ≤ objective p₀ L q) ∧
    (∀ q, Admissible p₀ L q → objective p₀ L q = objective p₀ L (qB p₀ L) →
      ∀ᵐ θ, q θ = qB p₀ L θ) := by
  have hB : Admissible p₀ L (qB p₀ L) := admissible_qB hp₀ hL hL0
  have hobjB : objective p₀ L (qB p₀ L) = -log (Z p₀ L) := by
    rw [objective_eq hp₀ hL hL0 hB, kl_self, zero_sub]
  -- achieve the first goal
  refine ⟨hB, ?_, ?_⟩
  · -- optimality of q = qB: objective q = kl q qB - log Z ≥ kl qB qB - log Z = - log Z
    intro q hq
    rw [hobjB, objective_eq hp₀ hL hL0 hq]
    have hkl := kl_nonneg hq.dens (isDensity_qB hp₀ hL hL0)
      (supp_qB hp₀ hL hL0 hq) (integrable_mul_log_div_qB hp₀ hL hL0 hq)
    linarith
  · -- uniqueness of optimal q
    intro q hq heq
    rw [hobjB, objective_eq hp₀ hL hL0 hq] at heq
    apply ae_eq_of_kl_eq_zero hq.dens (isDensity_qB hp₀ hL hL0)
      (supp_qB hp₀ hL hL0 hq) (integrable_mul_log_div_qB hp₀ hL hL0 hq)
    linarith
