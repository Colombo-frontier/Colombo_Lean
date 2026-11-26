import GradientHessian.GaussianInterpolation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Gaussian comparison along the square-root interpolation. The comparison
criterion is stated on the actual Hessian and actual linear Gaussian maps;
The proof uses the actual Gaussian interpolation derivative. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert Filter Set
open scoped InnerProductSpace BigOperators NNReal Topology

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def gaussianInterpolationMap (A B : E →L[ℝ] F) (t : ℝ) : E →L[ℝ] F :=
  Real.sqrt t • A + Real.sqrt (1 - t) • B

def gaussianInterpolationMapDerivative (A B : E →L[ℝ] F) (t : ℝ) : E →L[ℝ] F :=
  (1 / (2 * Real.sqrt t)) • A - (1 / (2 * Real.sqrt (1 - t))) • B

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem gaussianInterpolationMap_hasDerivAt (A B : E →L[ℝ] F) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (gaussianInterpolationMap E A B)
      (gaussianInterpolationMapDerivative E A B t) t := by
  have h1 := (Real.hasDerivAt_sqrt ht.1.ne').smul_const A
  have h2 := (((hasDerivAt_id t).const_sub 1).sqrt (by linarith [ht.2] : 1 - t ≠ 0)).smul_const B
  convert h1.add h2 using 1
  simp only [gaussianInterpolationMapDerivative, neg_div, neg_smul, sub_eq_add_neg, id_eq]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem gaussianInterpolationMapDerivative_continuousAt (A B : E →L[ℝ] F) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (gaussianInterpolationMapDerivative E A B) t := by
  have ht0 := (Real.sqrt_pos.mpr ht.1).ne'
  have ht1 := (Real.sqrt_pos.mpr (show 0 < 1 - t by linarith [ht.2])).ne'
  exact ((continuousAt_const.div
    (continuousAt_const.mul Real.continuous_sqrt.continuousAt) (mul_ne_zero (by norm_num) ht0)).smul
    continuousAt_const).sub ((continuousAt_const.div
      (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
        (continuousAt_const.sub continuousAt_id))) (mul_ne_zero (by norm_num) ht1)).smul
      continuousAt_const)

omit [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_interpolation_trace (A B : E →L[ℝ] F) (H : F →L[ℝ] F →L[ℝ] ℝ)
    (hAB : ∑ i, H (A (stdOrthonormalBasis ℝ E i)) (B (stdOrthonormalBasis ℝ E i)) = 0)
    (hBA : ∑ i, H (B (stdOrthonormalBasis ℝ E i)) (A (stdOrthonormalBasis ℝ E i)) = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∑ i, H (gaussianInterpolationMap E A B t (stdOrthonormalBasis ℝ E i))
      (gaussianInterpolationMapDerivative E A B t (stdOrthonormalBasis ℝ E i))) =
      (1 / 2 : ℝ) * ((∑ i, H (A (stdOrthonormalBasis ℝ E i)) (A (stdOrthonormalBasis ℝ E i))) -
        ∑ i, H (B (stdOrthonormalBasis ℝ E i)) (B (stdOrthonormalBasis ℝ E i))) := by
  have ht0 := (Real.sqrt_pos.mpr ht.1).ne'
  have ht1 := (Real.sqrt_pos.mpr (show 0 < 1 - t by linarith [ht.2])).ne'
  simp only [gaussianInterpolationMap, gaussianInterpolationMapDerivative,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    map_add, map_sub, map_smul, smul_eq_mul]
  simp_rw [mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  rw [hAB, hBA]
  field_simp [ht0, ht1]
  ring

theorem gaussian_comparison {f : F → ℝ} {b c : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith b f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (c : ℝ))
    (A B : E →L[ℝ] F)
    (hAB : ∀ x, ∑ i, fderiv ℝ (fderiv ℝ f) x
      (A (stdOrthonormalBasis ℝ E i)) (B (stdOrthonormalBasis ℝ E i)) = 0)
    (hBA : ∀ x, ∑ i, fderiv ℝ (fderiv ℝ f) x
      (B (stdOrthonormalBasis ℝ E i)) (A (stdOrthonormalBasis ℝ E i)) = 0)
    (htrace : ∀ x, (∑ i, fderiv ℝ (fderiv ℝ f) x
      (B (stdOrthonormalBasis ℝ E i)) (B (stdOrthonormalBasis ℝ E i))) ≤
      ∑ i, fderiv ℝ (fderiv ℝ f) x
        (A (stdOrthonormalBasis ℝ E i)) (A (stdOrthonormalBasis ℝ E i))) :
    linearGaussianExpectation E f B ≤ linearGaussianExpectation E f A := by
  let H : ℝ → ℝ := fun t => linearGaussianExpectation E f (gaussianInterpolationMap E A B t)
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :=
    gaussian_interpolation_hasDerivAt E hf hLip hH
      (show ∀ᶠ s in 𝓝 t, HasDerivAt (gaussianInterpolationMap E A B)
        (gaussianInterpolationMapDerivative E A B s) s from
        Filter.Eventually.mono (isOpen_Ioo.mem_nhds ht)
          (fun s hs => gaussianInterpolationMap_hasDerivAt E A B hs))
      (gaussianInterpolationMapDerivative_continuousAt E A B ht)
  have hc : Continuous H :=
    (linearGaussianExpectation_lipschitz E hLip).continuous.comp
      ((Real.continuous_sqrt.smul continuous_const).add
        ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).smul continuous_const))
  have hm : MonotoneOn H (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc.continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t ht).deriv]
      apply integral_nonneg
      intro z
      change 0 ≤ ∑ i, fderiv ℝ (fderiv ℝ f) (gaussianInterpolationMap E A B t z)
        (gaussianInterpolationMap E A B t (stdOrthonormalBasis ℝ E i))
        (gaussianInterpolationMapDerivative E A B t (stdOrthonormalBasis ℝ E i))
      rw [gaussian_interpolation_trace E A B _ (hAB _) (hBA _) ht]
      exact mul_nonneg (by norm_num) (sub_nonneg.mpr (htrace _))
  have h := hm (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) (by norm_num)
  simpa only [H, gaussianInterpolationMap, Real.sqrt_zero, Real.sqrt_one,
    sub_zero, sub_self, zero_smul, one_smul, zero_add, add_zero] using h

end GradientHessian.GaussianConcentration
