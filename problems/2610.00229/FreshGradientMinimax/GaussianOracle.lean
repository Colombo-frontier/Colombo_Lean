import FreshGradientMinimax.GaussianMoments
import FreshGradientMinimax.RealCoordinate
import FreshGradientMinimax.Oracle
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! A genuine fresh oracle: exact primal gradient and independent centered
Gaussian dual noise. Its complete contract is proved from Gaussian moments. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {dx : ℕ} {L μ : ℝ} (F : NCObjective dx 1 L μ)

def gaussianDualResponse (zt : Joint dx 1 × ℝ) : Joint dx 1 :=
  (F.gradX zt.1.1 zt.1.2, F.gradY zt.1.1 zt.1.2 + zt.2 • realVector 1)

theorem gaussianDualResponse_continuous : Continuous (gaussianDualResponse F) :=
  ((F.jointGradient_continuous.comp continuous_fst).fst).prodMk
    (((F.jointGradient_continuous.comp continuous_fst).snd).add (continuous_snd.smul continuous_const))

theorem gaussianDualResponse_measurable (z : Joint dx 1) :
    Measurable (fun t : ℝ => gaussianDualResponse F (z, t)) :=
  ((gaussianDualResponse_continuous F).comp (continuous_const.prodMk continuous_id)).measurable

def gaussianDualKernel (v : ℝ≥0) : Kernel (Joint dx 1) (Joint dx 1) :=
  (Kernel.id ×ₖ Kernel.const (Joint dx 1) (gaussianReal 0 v)).map (gaussianDualResponse F)

instance gaussianDualKernel_markov (v : ℝ≥0) : IsMarkovKernel (gaussianDualKernel F v) :=
  Kernel.IsMarkovKernel.map _ (gaussianDualResponse_continuous F).measurable

theorem gaussianDualKernel_apply (v : ℝ≥0) (z : Joint dx 1) :
    gaussianDualKernel F v z = (gaussianReal 0 v).map (fun t => gaussianDualResponse F (z, t)) := by
  rw [gaussianDualKernel, Kernel.map_apply _ (gaussianDualResponse_continuous F).measurable,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (gaussianDualResponse_continuous F).measurable measurable_prodMk_left]
  rfl

theorem gaussianDualResponse_integrable (v : ℝ≥0) (z : Joint dx 1) :
    Integrable (fun t => gaussianDualResponse F (z, t)) (gaussianReal 0 v) :=
  (integrable_const (F.gradX z.1 z.2)).prodMk
    ((integrable_const (F.gradY z.1 z.2)).add ((gaussianReal_id_integrable 0 v).smul_const (realVector 1)))

theorem gaussianDualResponse_mean (v : ℝ≥0) (z : Joint dx 1) :
    (∫ t, gaussianDualResponse F (z, t) ∂gaussianReal 0 v) = F.jointGradient z := by
  unfold gaussianDualResponse NCObjective.jointGradient
  rw [integral_pair (f := fun _ : ℝ => F.gradX z.1 z.2)
    (g := fun t : ℝ => F.gradY z.1 z.2 + t • realVector 1)
    (integrable_const _) ((integrable_const _).add
    ((gaussianReal_id_integrable 0 v).smul_const (realVector 1)))]
  rw [integral_add (f := fun _ : ℝ => F.gradY z.1 z.2) (g := fun t : ℝ => t • realVector 1)
    (integrable_const _) ((gaussianReal_id_integrable 0 v).smul_const (realVector 1)),
    integral_smul_const, gaussianReal_mean]
  simp

theorem gaussianDualResponse_error (z : Joint dx 1) (t : ℝ) :
    jointNormSq (gaussianDualResponse F (z, t) - F.jointGradient z) = t ^ 2 := by
  simp [jointNormSq, gaussianDualResponse, NCObjective.jointGradient, norm_smul_sq]

theorem gaussianDualKernel_integrable (v : ℝ≥0) (z : Joint dx 1) :
    Integrable id (gaussianDualKernel F v z) := by
  rw [gaussianDualKernel_apply]
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    (gaussianDualResponse_measurable F z).aemeasurable).mpr
    (gaussianDualResponse_integrable F v z)

theorem gaussianDualKernel_mean (v : ℝ≥0) (z : Joint dx 1) :
    (∫ r, r ∂gaussianDualKernel F v z) = F.jointGradient z := by
  rw [gaussianDualKernel_apply, integral_map (f := fun r : Joint dx 1 => r)
    (gaussianDualResponse_measurable F z).aemeasurable
    measurable_id.aestronglyMeasurable]
  exact gaussianDualResponse_mean F v z

theorem gaussianDualKernel_square_integrable (v : ℝ≥0) (z : Joint dx 1) :
    Integrable (fun r => jointNormSq (r - F.jointGradient z)) (gaussianDualKernel F v z) := by
  rw [gaussianDualKernel_apply]
  have hm : Measurable (fun r : Joint dx 1 => jointNormSq (r - F.jointGradient z)) := by
    unfold jointNormSq
    fun_prop
  apply (integrable_map_measure hm.aestronglyMeasurable
    (gaussianDualResponse_measurable F z).aemeasurable).mpr
  simpa only [Function.comp_def, gaussianDualResponse_error] using gaussianReal_pow_integrable 0 v 2

theorem gaussianDualKernel_variance (v : ℝ≥0) (z : Joint dx 1) :
    (∫ r, jointNormSq (r - F.jointGradient z) ∂gaussianDualKernel F v z) = (v : ℝ) := by
  rw [gaussianDualKernel_apply]
  have hm : Measurable (fun r : Joint dx 1 => jointNormSq (r - F.jointGradient z)) := by
    unfold jointNormSq
    fun_prop
  rw [integral_map
    (gaussianDualResponse_measurable F z).aemeasurable
    hm.aestronglyMeasurable]
  simp only [gaussianDualResponse_error, gaussianReal_second_moment, zero_pow (by norm_num : 2 ≠ 0), add_zero]

def FreshOracle.gaussianDual (σ : ℝ) : FreshOracle F σ where
  kernel := gaussianDualKernel F ⟨σ ^ 2, sq_nonneg σ⟩
  integrable := gaussianDualKernel_integrable F _
  mean := gaussianDualKernel_mean F _
  square_integrable := gaussianDualKernel_square_integrable F _
  variance_le z := le_of_eq (gaussianDualKernel_variance F _ z)

end FreshGradientMinimax
