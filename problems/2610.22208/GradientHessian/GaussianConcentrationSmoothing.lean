import GradientHessian.GaussianConcentrationHessian
import GradientHessian.GaussianConcentrationTimeGenerator

/-! Actual C2 preservation and derivative bounds for Gaussian smoothing.
These discharge regularity premises when applying the Dirichlet identity. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped NNReal

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem vectorMehler_continuous {f : E → V} (hf : Continuous f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (ρ : ℝ) : Continuous (vectorMehler ρ f) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro x
    exact (hf.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  · intro x
    exact ae_of_all _ fun z => hC _
  · exact integrable_const _
  · exact ae_of_all _ fun z => hf.comp ((continuous_const.smul continuous_id).add continuous_const)

theorem mehler_contDiff_two {f : E → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ)) (ρ : ℝ) :
    ContDiff ℝ 2 (mehler E ρ f) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDLip : LipschitzWith C (fderiv ℝ f) :=
    lipschitzWith_of_nnnorm_fderiv_le (hD.differentiable (by norm_num))
      (fun x => by exact_mod_cast hH x)
  have hd : Differentiable ℝ (mehler E ρ f) :=
    fun x => (mehler_hasFDerivAt (hf.of_le (by norm_num)) hLip ρ x).differentiableAt
  have he : fderiv ℝ (mehler E ρ f) = fun y => ρ • vectorMehler ρ (fderiv ℝ f) y :=
    funext (mehler_fderiv (hf.of_le (by norm_num)) hLip ρ)
  have hdd : Differentiable ℝ (fderiv ℝ (mehler E ρ f)) := by
    rw [he]
    exact fun x => ((vectorMehler_hasFDerivAt hD hDLip ρ x).const_smul ρ).differentiableAt
  have he2 : fderiv ℝ (fderiv ℝ (mehler E ρ f)) =
      fun y => ρ ^ 2 • vectorMehler ρ (fderiv ℝ (fderiv ℝ f)) y :=
    funext (mehler_hessian hf hLip hH ρ)
  have hc : Continuous (fderiv ℝ (fderiv ℝ (mehler E ρ f))) := by
    rw [he2]
    exact continuous_const.smul (vectorMehler_continuous
      (hD.continuous_fderiv (by norm_num)) hH ρ)
  change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (mehler E ρ f)
  exact contDiff_succ_iff_fderiv.mpr ⟨hd, by norm_num, contDiff_one_iff_fderiv.mpr ⟨hdd, hc⟩⟩

theorem mehler_value_bounds {f : E → ℝ} {B : ℝ≥0} (hLip : LipschitzWith B f)
    {a b : ℝ} (hab : ∀ z, a ≤ f z ∧ f z ≤ b) (ρ : ℝ) (x : E) :
    a ≤ mehler E ρ f x ∧ mehler E ρ f x ≤ b := by
  have hi := lipschitz_affine_integrable hLip (Real.sqrt (1 - ρ ^ 2)) (ρ • x)
  constructor
  · have h := integral_mono (integrable_const a) hi (fun z => (hab _).1)
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using h
  · have h := integral_mono hi (integrable_const b) (fun z => (hab _).2)
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using h

theorem mehler_fderiv_norm_le {f : E → ℝ} {B : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f) (ρ : ℝ) (x : E) :
    ‖fderiv ℝ (mehler E ρ f) x‖ ≤ |ρ| * (B : ℝ) := by
  have hi := smoothed_gradient_integrable E hf hLip ρ (Real.sqrt (1 - ρ ^ 2)) x
  have hb := integral_mono hi.norm (integrable_const (B : ℝ))
    (fun z => norm_fderiv_le_of_lipschitz ℝ hLip)
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hb
  rw [mehler_fderiv (hf.of_le (by norm_num)) hLip,
    norm_smul ρ (∫ z, fderiv ℝ f (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)
      ∂euclideanGaussianLaw E), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans hb) (abs_nonneg ρ)

theorem mehler_hessian_norm_le {f : E → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ)) (ρ : ℝ) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (mehler E ρ f)) x‖ ≤ ρ ^ 2 * (C : ℝ) := by
  have hb : ‖∫ z, fderiv ℝ (fderiv ℝ f) (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)
      ∂euclideanGaussianLaw E‖ ≤ (C : ℝ) := by
    simpa only [measureReal_univ_eq_one, mul_one] using
      (norm_integral_le_of_norm_le_const
        (f := fun z : E => fderiv ℝ (fderiv ℝ f) (ρ • x + Real.sqrt (1 - ρ ^ 2) • z))
        (μ := euclideanGaussianLaw E) (ae_of_all _ fun z => hH _))
  rw [mehler_hessian hf hLip hH]
  calc
    _ = ‖ρ ^ 2‖ * ‖∫ z, fderiv ℝ (fderiv ℝ f)
        (ρ • x + Real.sqrt (1 - ρ ^ 2) • z) ∂euclideanGaussianLaw E‖ :=
      (norm_smul_of_nonneg (sq_nonneg ρ) (∫ z, fderiv ℝ (fderiv ℝ f)
        (ρ • x + Real.sqrt (1 - ρ ^ 2) • z) ∂euclideanGaussianLaw E)).trans
        (by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ)])
    _ ≤ ρ ^ 2 * (C : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ)]
      exact mul_le_mul_of_nonneg_left hb (sq_nonneg ρ)

end GradientHessian.GaussianConcentration
