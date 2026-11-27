import SphereConcentrationLevy
import SphereConcentration
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
Actual layer-cake integration at order 3/2. A fixed, finite real Gaussian
integral defines an absolute constant; no third-halves moment bound is a
premise of the theorem that derives it from the Gaussian-type tail.
-/

open Set MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Task006.SphereConcentration
noncomputable section

/-- A fixed, integrable one-dimensional tail weight. -/
def thirdHalfTailWeight (t : ℝ) : ℝ :=
  t ^ (1 / 2 : ℝ) * Real.exp (-(1 / 128 : ℝ) * t ^ 2)

theorem thirdHalfTailWeight_integrable :
    IntegrableOn thirdHalfTailWeight (Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) (by norm_num)

theorem thirdHalfTailWeight_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ thirdHalfTailWeight t :=
  mul_nonneg (Real.rpow_nonneg ht _) (Real.exp_pos _).le

/-- One plus the actual tail integral makes a positive absolute moment constant. -/
def thirdHalfMomentConstant : ℝ :=
  1 + (3 / 2 : ℝ) * Real.exp 128 * ∫ t in Ioi 0, thirdHalfTailWeight t

theorem thirdHalfMomentConstant_ge_one : 1 ≤ thirdHalfMomentConstant := by
  have hI : 0 ≤ ∫ t in Ioi 0, thirdHalfTailWeight t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact thirdHalfTailWeight_nonneg ht.le
  unfold thirdHalfMomentConstant
  have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) (Real.exp_pos (128 : ℝ)).le) hI
  linarith

/-- A normalized Gaussian-type tail gives a genuine 3/2-moment bound. The
finite bound B only establishes integrability of the actual variable; the
moment conclusion is obtained by layer-cake integration. -/
theorem thirdHalf_moment_of_normalized_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Measurable Y) {B : ℝ} (hbound : ∀ᵐ ω ∂μ, |Y ω| ≤ B)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t ≤ |Y ω|} ≤
      Real.exp 128 * Real.exp (-(1 / 128 : ℝ) * t ^ 2)) :
    (∫ ω, |Y ω| ^ (3 / 2 : ℝ) ∂μ) ≤ thirdHalfMomentConstant := by
  have hmoment : Integrable (fun ω => |Y ω| ^ (3 / 2 : ℝ)) μ := by
    have hm : Measurable (fun ω => |Y ω| ^ (3 / 2 : ℝ)) :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).measurable.comp hY.abs
    apply Integrable.of_bound hm.aestronglyMeasurable (B ^ (3 / 2 : ℝ))
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) hω (by norm_num)
  have hW : IntegrableOn (fun t => Real.exp 128 * thirdHalfTailWeight t) (Ioi 0) :=
    thirdHalfTailWeight_integrable.const_mul _
  have hWnn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ Real.exp 128 * thirdHalfTailWeight t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (thirdHalfTailWeight_nonneg ht.le)
  have hfiniteBound :
      (∫⁻ ω, ENNReal.ofReal (|Y ω| ^ (3 / 2 : ℝ)) ∂μ) ≤
        ENNReal.ofReal ((3 / 2 : ℝ) * Real.exp 128 *
          ∫ t in Ioi 0, thirdHalfTailWeight t) := by
    rw [lintegral_rpow_eq_lintegral_meas_le_mul μ
      (Filter.Eventually.of_forall (fun ω => abs_nonneg (Y ω))) hY.abs.aemeasurable
      (by norm_num : (0 : ℝ) < 3 / 2)]
    have hcompare :
        (∫⁻ t in Ioi (0 : ℝ), μ {ω | t ≤ |Y ω|} *
          ENNReal.ofReal (t ^ ((3 / 2 : ℝ) - 1))) ≤
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp 128 * thirdHalfTailWeight t) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hp : μ {ω | t ≤ |Y ω|} ≤
          ENNReal.ofReal (Real.exp 128 * Real.exp (-(1 / 128 : ℝ) * t ^ 2)) := by
        apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2
        exact htail t ht
      calc
        μ {ω | t ≤ |Y ω|} * ENNReal.ofReal (t ^ ((3 / 2 : ℝ) - 1)) ≤
            ENNReal.ofReal (Real.exp 128 * Real.exp (-(1 / 128 : ℝ) * t ^ 2)) *
              ENNReal.ofReal (t ^ ((3 / 2 : ℝ) - 1)) := mul_le_mul_left hp _
        _ = ENNReal.ofReal (Real.exp 128 * thirdHalfTailWeight t) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          unfold thirdHalfTailWeight
          norm_num
          ring
    calc
      ENNReal.ofReal (3 / 2 : ℝ) *
          (∫⁻ t in Ioi (0 : ℝ), μ {ω | t ≤ |Y ω|} *
            ENNReal.ofReal (t ^ ((3 / 2 : ℝ) - 1))) ≤
          ENNReal.ofReal (3 / 2 : ℝ) *
            ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp 128 * thirdHalfTailWeight t) :=
        mul_le_mul_right hcompare _
      _ = ENNReal.ofReal ((3 / 2 : ℝ) * Real.exp 128 *
          ∫ t in Ioi 0, thirdHalfTailWeight t) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hW hWnn, integral_const_mul,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
        congr 1
        ring
  have hI : 0 ≤ ∫ t in Ioi 0, thirdHalfTailWeight t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact thirdHalfTailWeight_nonneg ht.le
  have hreal := ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos (128 : ℝ)).le) hI) hfiniteBound
  have heq : (∫ ω, |Y ω| ^ (3 / 2 : ℝ) ∂μ) =
      (∫⁻ ω, ENNReal.ofReal (|Y ω| ^ (3 / 2 : ℝ)) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (abs_nonneg _) _))
      hmoment.aestronglyMeasurable
  unfold thirdHalfMomentConstant
  rw [heq]
  linarith only [hreal]

end
end Task006.SphereConcentration
