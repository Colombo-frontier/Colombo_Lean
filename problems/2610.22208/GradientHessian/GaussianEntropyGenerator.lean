import GradientHessian.GaussianEntropyDirichlet
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The entropy integration-by-parts identity for actual positive smooth
functions. No functional inequality or entropy-dissipation identity is assumed. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped NNReal BigOperators

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] in
theorem entropySlope_bound {g : E → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : ∀ x, a ≤ g x ∧ g x ≤ b) (x : E) :
    ‖1 + Real.log (g x)‖ ≤ 1 + |Real.log a| + |Real.log b| := by
  have hl := Real.log_le_log ha (hab x).1
  have hu := Real.log_le_log (ha.trans_le (hab x).1) (hab x).2
  have hlog : |Real.log (g x)| ≤ |Real.log a| + |Real.log b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
    · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]
  have h := norm_add_le (1 : ℝ) (Real.log (g x))
  simp only [norm_one, Real.norm_eq_abs] at h
  simpa only [add_assoc] using
    h.trans (add_le_add_left hlog 1)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem entropySlope_fderiv {g : E → ℝ} (hg : Differentiable ℝ g)
    (hpos : ∀ x, 0 < g x) (x : E) :
    fderiv ℝ (fun y => 1 + Real.log (g y)) x = (g x)⁻¹ • fderiv ℝ g x :=
  (((hg x).hasFDerivAt.log (hpos x).ne').const_add 1).fderiv

theorem gaussian_entropy_generator {g : E → ℝ} {B C : ℝ≥0} {a b : ℝ}
    (hg : ContDiff ℝ 2 g) (hLip : LipschitzWith B g)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ (C : ℝ))
    (ha : 0 < a) (hab : ∀ x, a ≤ g x ∧ g x ≤ b) :
    (∫ x, (1 + Real.log (g x)) * gaussianGenerator E g x ∂euclideanGaussianLaw E) =
      -(∫ x, ‖fderiv ℝ g x‖ ^ 2 / g x ∂euclideanGaussianLaw E) := by
  have hpos (x : E) : 0 < g x := ha.trans_le (hab x).1
  have hdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hu : ContDiff ℝ 1 (fun x => 1 + Real.log (g x)) :=
    contDiff_const.add ((hg.of_le (by norm_num)).log (fun x => (hpos x).ne'))
  have hU (x : E) : ‖fderiv ℝ (fun y => 1 + Real.log (g y)) x‖ ≤ (B : ℝ) / a := by
    rw [entropySlope_fderiv E hdiff hpos,
      norm_smul (g x)⁻¹ (fderiv ℝ g x), Real.norm_of_nonneg (inv_nonneg.mpr (hpos x).le)]
    have hi : (g x)⁻¹ ≤ a⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le ha (hab x).1
    calc
      _ ≤ a⁻¹ * (B : ℝ) := mul_le_mul hi (norm_fderiv_le_of_lipschitz ℝ hLip)
        (norm_nonneg _) (inv_nonneg.mpr ha.le)
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  have hd := gaussian_dirichlet_bounded_weight E hu hg hLip hH
    (entropySlope_bound E ha hab) hU
  have he (x : E) : (∑ i, coordinateDerivative E (fun y => 1 + Real.log (g y)) i x *
      coordinateDerivative E g i x) = ‖fderiv ℝ g x‖ ^ 2 / g x := by
    simp only [coordinateDerivative, entropySlope_fderiv E hdiff hpos,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    simp_rw [mul_assoc, ← pow_two]
    rw [← Finset.mul_sum, covector_parseval, div_eq_mul_inv, mul_comm]
  simpa only [he] using hd

end GradientHessian.GaussianConcentration
