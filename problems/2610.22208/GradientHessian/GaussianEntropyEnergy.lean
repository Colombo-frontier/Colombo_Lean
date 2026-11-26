import GradientHessian.GaussianPoincareEnergy
import GradientHessian.GaussianEntropyGenerator

/-! Sharp Fisher-information contraction of the actual Gaussian
semigroup, obtained by the proved weighted integral Cauchy--Schwarz. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def fisherIntegrand (g : E → ℝ) (x : E) : ℝ := ‖fderiv ℝ g x‖ ^ 2 / g x

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem fisher_continuous {g : E → ℝ} (hg : ContDiff ℝ 2 g) (hpos : ∀ x, 0 < g x) :
    Continuous (fisherIntegrand E g) :=
  ((hg.continuous_fderiv (by norm_num)).norm.pow 2).div hg.continuous (fun x => (hpos x).ne')

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem fisher_norm_le {g : E → ℝ} {B : ℝ≥0} (hLip : LipschitzWith B g)
    {a : ℝ} (ha : 0 < a) (hab : ∀ x, a ≤ g x) (x : E) :
    ‖fisherIntegrand E g x‖ ≤ (B : ℝ) ^ 2 / a := by
  have hpos : 0 < g x := ha.trans_le (hab x)
  have hi : (g x)⁻¹ ≤ a⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le ha (hab x)
  have hd : ‖fderiv ℝ g x‖ ^ 2 ≤ (B : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hLip) 2
  rw [fisherIntegrand, Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hpos.le),
    div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul hd hi (inv_nonneg.mpr hpos.le) (sq_nonneg _)

theorem fisher_integrable {g : E → ℝ} {B : ℝ≥0}
    (hg : ContDiff ℝ 2 g) (hLip : LipschitzWith B g)
    {a : ℝ} (ha : 0 < a) (hab : ∀ x, a ≤ g x) :
    Integrable (fisherIntegrand E g) (euclideanGaussianLaw E) :=
  gaussian_bounded_integrable E (fisher_continuous E hg (fun x => ha.trans_le (hab x)))
    (fisher_norm_le E hLip ha hab)

theorem mehler_fisher_le {g : E → ℝ} {B : ℝ≥0} {a b : ℝ}
    (hg : ContDiff ℝ 2 g) (hLip : LipschitzWith B g)
    (ha : 0 < a) (hab : ∀ x, a ≤ g x ∧ g x ≤ b) (ρ : ℝ) (x : E) :
    fisherIntegrand E (mehler E ρ g) x ≤ ρ ^ 2 * mehler E ρ (fisherIntegrand E g) x := by
  have hpos (y : E) : 0 < g y := ha.trans_le (hab y).1
  have hV := smoothed_gradient_integrable E hg hLip ρ (Real.sqrt (1 - ρ ^ 2)) x
  have hG := lipschitz_affine_integrable hLip (Real.sqrt (1 - ρ ^ 2)) (ρ • x)
  have hM : 0 < mehler E ρ g x := ha.trans_le (mehler_value_bounds hLip hab ρ x).1
  have hQ : Integrable (fun z => fisherIntegrand E g (ρ • x + Real.sqrt (1 - ρ ^ 2) • z))
      (euclideanGaussianLaw E) :=
    gaussian_bounded_integrable E ((fisher_continuous E hg hpos).comp
      (continuous_const.add (continuous_const.smul continuous_id)))
      (fun z => fisher_norm_le E hLip ha (fun y => (hab y).1) _)
  have hj := weighted_integral_norm_square_le hV hG
    (ae_of_all _ fun z => hpos (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)) hM hQ
  change ‖fderiv ℝ (mehler E ρ g) x‖ ^ 2 / mehler E ρ g x ≤ _
  rw [div_le_iff₀ hM, mehler_fderiv (hg.of_le (by norm_num)) hLip,
    norm_smul ρ (∫ z, fderiv ℝ g (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)
      ∂euclideanGaussianLaw E), mul_pow, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ ρ ^ 2 * ((∫ z, g (ρ • x + Real.sqrt (1 - ρ ^ 2) • z) ∂euclideanGaussianLaw E) *
      (∫ z, fisherIntegrand E g (ρ • x + Real.sqrt (1 - ρ ^ 2) • z) ∂euclideanGaussianLaw E)) :=
      mul_le_mul_of_nonneg_left hj (sq_nonneg ρ)
    _ = _ := by unfold mehler; ring

theorem ou_fisher_contraction {g : E → ℝ} {B C : ℝ≥0} {a b : ℝ}
    (hg : ContDiff ℝ 2 g) (hLip : LipschitzWith B g)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ (C : ℝ))
    (ha : 0 < a) (hab : ∀ x, a ≤ g x ∧ g x ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, fisherIntegrand E (ornsteinUhlenbeck E t g) x ∂euclideanGaussianLaw E) ≤
      Real.exp (-t) ^ 2 * (∫ x, fisherIntegrand E g x ∂euclideanGaussianLaw E) := by
  let ρ := Real.exp (-t)
  have hc := fisher_continuous E hg (fun x => ha.trans_le (hab x).1)
  have hb := fisher_norm_le E hLip ha (fun x => (hab x).1)
  have hmc : Continuous (mehler E ρ (fisherIntegrand E g)) := vectorMehler_continuous hc hb ρ
  have hmi : Integrable (mehler E ρ (fisherIntegrand E g)) (euclideanGaussianLaw E) :=
    gaussian_bounded_integrable E hmc (mehler_norm_le E hb ρ)
  have hgi : Integrable (fisherIntegrand E (ornsteinUhlenbeck E t g)) (euclideanGaussianLaw E) :=
    fisher_integrable E (mehler_contDiff_two hg hLip hH ρ) (ou_lipschitz E hg hLip ht)
      ha (fun x => (mehler_value_bounds hLip hab ρ x).1)
  have hi := integral_mono hgi (hmi.const_mul (ρ ^ 2)) (fun x => mehler_fisher_le E hg hLip ha hab ρ x)
  have hr : ρ ^ 2 ≤ 1 := by
    dsimp [ρ]
    nlinarith [ou_signal_le_one ht, Real.exp_pos (-t)]
  rw [integral_const_mul, mehler_invariant E hr
    (fisher_integrable E hg hLip ha (fun x => (hab x).1))] at hi
  exact hi

end GradientHessian.GaussianConcentration
