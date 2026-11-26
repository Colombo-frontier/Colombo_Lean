import GradientHessian.GaussianConcentrationSmoothing
import GradientHessian.GaussianConcentrationEnergy
import GradientHessian.GaussianConcentrationLimits
import GradientHessian.GaussianPoincareDirichlet

/-! The sharp energy contraction of the actual Ornstein--Uhlenbeck
semigroup. The constant is dimension independent. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem ou_signal_le_one {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by linarith)

theorem ou_lipschitz {f : E → ℝ} {B : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f) {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith B (ornsteinUhlenbeck E t f) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (mehler_hasFDerivAt (hf.of_le (by norm_num)) hLip _ x).differentiableAt)
  intro x
  have h := mehler_fderiv_norm_le hf hLip (Real.exp (-t)) x
  rw [abs_of_pos (Real.exp_pos _)] at h
  have he := mul_le_mul_of_nonneg_right (ou_signal_le_one ht) B.coe_nonneg
  have hb : ‖fderiv ℝ (ornsteinUhlenbeck E t f) x‖ ≤ (B : ℝ) := h.trans (by simpa using he)
  exact_mod_cast hb

theorem ou_hessian_bound {f : E → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ)) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (ornsteinUhlenbeck E t f)) x‖ ≤ (C : ℝ) := by
  apply (mehler_hessian_norm_le hf hLip hH _ x).trans
  have he : Real.exp (-t) ^ 2 ≤ 1 := by
    nlinarith [ou_signal_le_one ht, Real.exp_pos (-t)]
  exact (mul_le_mul_of_nonneg_right he C.coe_nonneg).trans_eq (one_mul _)

theorem gradient_square_integrable {f : E → ℝ} {B : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f) :
    Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) (euclideanGaussianLaw E) := by
  apply gaussian_bounded_integrable E ((hf.continuous_fderiv (by norm_num)).norm.pow 2)
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hLip) 2

theorem mehler_gradient_square_le {f : E → ℝ} {B : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f) (ρ : ℝ) (x : E) :
    ‖fderiv ℝ (mehler E ρ f) x‖ ^ 2 ≤
      ρ ^ 2 * mehler E ρ (fun y => ‖fderiv ℝ f y‖ ^ 2) x := by
  have hi := smoothed_gradient_integrable E hf hLip ρ (Real.sqrt (1 - ρ ^ 2)) x
  have hq : Integrable (fun z => ‖fderiv ℝ f (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)‖ ^ 2)
      (euclideanGaussianLaw E) := by
    apply gaussian_bounded_integrable E
      ((((hf.continuous_fderiv (by norm_num)).comp
        (continuous_const.add (continuous_const.smul continuous_id))).norm).pow 2)
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hLip) 2
  have hj := weighted_integral_norm_square_le hi (integrable_const (1 : ℝ))
    (ae_of_all _ fun _ => zero_lt_one) (by simp) (by simpa using hq)
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul, div_one] at hj
  rw [mehler_fderiv (hf.of_le (by norm_num)) hLip,
    norm_smul ρ (∫ z, fderiv ℝ f (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)
      ∂euclideanGaussianLaw E), mul_pow, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_left hj (sq_nonneg ρ)

theorem ou_energy_contraction {f : E → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, ‖fderiv ℝ (ornsteinUhlenbeck E t f) x‖ ^ 2 ∂euclideanGaussianLaw E) ≤
      Real.exp (-t) ^ 2 * (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂euclideanGaussianLaw E) := by
  let ρ := Real.exp (-t)
  have hc : Continuous (fun x => ‖fderiv ℝ f x‖ ^ 2) :=
    (hf.continuous_fderiv (by norm_num)).norm.pow 2
  have hb (x : E) : ‖‖fderiv ℝ f x‖ ^ 2‖ ≤ (B : ℝ) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hLip) 2
  have hmc : Continuous (mehler E ρ (fun x => ‖fderiv ℝ f x‖ ^ 2)) := by
    change Continuous (vectorMehler ρ (fun x => ‖fderiv ℝ f x‖ ^ 2))
    exact vectorMehler_continuous hc hb ρ
  have hmi : Integrable (mehler E ρ (fun x => ‖fderiv ℝ f x‖ ^ 2)) (euclideanGaussianLaw E) :=
    gaussian_bounded_integrable E hmc
      (mehler_norm_le E hb ρ)
  have hgi : Integrable (fun x => ‖fderiv ℝ (ornsteinUhlenbeck E t f) x‖ ^ 2)
      (euclideanGaussianLaw E) :=
    gradient_square_integrable E (mehler_contDiff_two hf hLip hH ρ) (ou_lipschitz E hf hLip ht)
  have h := integral_mono hgi (hmi.const_mul (ρ ^ 2))
    (fun x => mehler_gradient_square_le E hf hLip ρ x)
  have hr : ρ ^ 2 ≤ 1 := by
    dsimp [ρ]
    nlinarith [ou_signal_le_one ht, Real.exp_pos (-t)]
  rw [integral_const_mul, mehler_invariant E hr (gradient_square_integrable E hf hLip)] at h
  exact h

end GradientHessian.GaussianConcentration
