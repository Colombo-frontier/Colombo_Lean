import SecondOrder.Model
import SecondOrder.Chord
import SecondOrder.IntegralMoments
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- Uniform line position on the unit interval, a genuine continuous law. -/
def unitLine : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance unitLine_probability : IsProbabilityMeasure unitLine := by
  constructor
  simp [unitLine]

theorem integral_unitLine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : (∫ t, f t ∂unitLine) = ∫ t in (0:ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rfl

theorem contDiff_gradient_one {d : ℕ} {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (gradient F) :=
  (InnerProductSpace.toDual ℝ (Point d)).symm.toContinuousLinearEquiv.contDiff.comp
    (hF.fderiv_right (by norm_num))

theorem continuous_hessian {d : ℕ} {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) :
    Continuous (hessian F) :=
  (contDiff_gradient_one hF).continuous_fderiv (by norm_num)

theorem gradient_has_hessian {d : ℕ} {F : Point d → ℝ} (hF : ContDiff ℝ 2 F)
    (x : Point d) : HasFDerivAt (gradient F) (hessian F x) x :=
  ((contDiff_gradient_one hF).differentiable (by norm_num) x).hasFDerivAt

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.population_hessian_norm (h : CommonLoss μ P ν F f) (x : Point d) :
    ‖hessian F x‖ ≤ P.gradientLip := by
  exact norm_fderiv_le_of_lip' ℝ P.gradientLip_pos.le
    (Eventually.of_forall (fun y => h.gradient_lipschitz y x))

/-- One point and one fresh sample; the same sample is never used at an endpoint. -/
def randomLineHvp (f : Ω → Point d → ℝ) (x y : Point d) (w : ℝ × Ω) : Point d :=
  hessian (f w.2) (x+w.1•(y-x)) (y-x)

theorem CommonLoss.randomLine_measurable (h : CommonLoss μ P ν F f) (x y : Point d) :
    Measurable (randomLineHvp f x y) := by
  have hpt : Measurable (fun w : ℝ × Ω => x+w.1•(y-x)) :=
    measurable_const.add (measurable_fst.smul measurable_const)
  exact (ContinuousLinearMap.apply ℝ (Point d) (y-x)).continuous.measurable.comp
    (h.hessian_measurable.comp (measurable_snd.prodMk hpt))

theorem CommonLoss.randomLine_norm_bound (h : CommonLoss μ P ν F f) (x y : Point d) :
    ∀ᵐ w ∂unitLine.prod μ, ‖randomLineHvp f x y w‖ ≤
      (P.hessianBound+P.gradientLip)*‖y-x‖ := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (h.randomLine_measurable x y).norm measurable_const)).mpr
  apply Eventually.of_forall
  intro t
  filter_upwards [h.global_hessian_bound] with z hz
  have hop : ‖hessian (f z) (x+t•(y-x))‖ ≤ P.hessianBound+P.gradientLip := by
    have hn := norm_add_le (hessian (f z) (x+t•(y-x))-hessian F (x+t•(y-x)))
      (hessian F (x+t•(y-x)))
    rw [sub_add_cancel] at hn
    linarith [hz (x+t•(y-x)),h.population_hessian_norm (x+t•(y-x))]
  exact ((hessian (f z) (x+t•(y-x))).le_opNorm (y-x)).trans
    (mul_le_mul_of_nonneg_right hop (norm_nonneg _))

theorem CommonLoss.randomLine_integrable (h : CommonLoss μ P ν F f) (x y : Point d) :
    Integrable (randomLineHvp f x y) (unitLine.prod μ) :=
  (integrable_const ((P.hessianBound+P.gradientLip)*‖y-x‖)).mono'
    (h.randomLine_measurable x y).aestronglyMeasurable (h.randomLine_norm_bound x y)

theorem CommonLoss.randomLine_sq_integrable (h : CommonLoss μ P ν F f) (x y : Point d) :
    Integrable (fun w => ‖randomLineHvp f x y w‖^2) (unitLine.prod μ) := by
  apply (integrable_const (((P.hessianBound+P.gradientLip)*‖y-x‖)^2)).mono'
    ((h.randomLine_measurable x y).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [h.randomLine_norm_bound x y] with w hw
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hw 2

theorem CommonLoss.hvp_integrable (h : CommonLoss μ P ν F f) (x v : Point d) :
    Integrable (fun z => hessian (f z) x v) μ :=
  (ContinuousLinearMap.apply ℝ (Point d) v).integrable_comp (h.hessian_integrable x)

theorem CommonLoss.hvp_unbiased (h : CommonLoss μ P ν F f) (x v : Point d) :
    (∫ z, hessian (f z) x v ∂μ) = hessian F x v := by
  rw [← ContinuousLinearMap.integral_apply (h.hessian_integrable x) v, h.hessian_unbiased]

/-- The unbiasedness statement of the manuscript for its actual oracle model. -/
theorem CommonLoss.randomLine_unbiased (h : CommonLoss μ P ν F f) (x y : Point d) :
    (∫ w, randomLineHvp f x y w ∂unitLine.prod μ) = gradient F y-gradient F x := by
  rw [integral_prod _ (h.randomLine_integrable x y)]
  simp only [randomLineHvp, h.hvp_unbiased]
  rw [integral_unitLine]
  exact hessian_line_integral (gradient_has_hessian h.population_smooth)
    (continuous_hessian h.population_smooth) x y

theorem CommonLoss.hvp_second_moment (h : CommonLoss μ P ν F f) (x v : Point d) :
    (∫ z, ‖hessian (f z) x v‖^2 ∂μ) ≤ (P.hessianNoise^2+P.gradientLip^2)*‖v‖^2 := by
  have hc := integral_conditional_variance (c := (0 : Point d))
    (h.hvp_integrable x v) (h.hvp_error_integrable x v) (h.hvp_unbiased x v)
  simp only [sub_zero, ContinuousLinearMap.sub_apply] at hc
  have hb : ‖hessian F x v‖ ≤ P.gradientLip*‖v‖ :=
    ((hessian F x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (h.population_hessian_norm x) (norm_nonneg _))
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hn := h.hvp_variance x v
  simp only [ContinuousLinearMap.sub_apply] at hn
  rw [hc]
  calc
    _ ≤ P.hessianNoise^2*‖v‖^2+(P.gradientLip*‖v‖)^2 := add_le_add hn hb2
    _ = _ := by ring

/-- Exact quadratic chord variance for continuous line positions and arbitrary
fresh-sample distributions, derived directly from CommonLoss. -/
theorem CommonLoss.randomLine_variance (h : CommonLoss μ P ν F f) (x y : Point d) :
    (∫ w, ‖randomLineHvp f x y w-(gradient F y-gradient F x)‖^2 ∂unitLine.prod μ) ≤
      (P.hessianNoise^2+P.gradientLip^2)*‖y-x‖^2 := by
  rw [← h.randomLine_unbiased x y]
  apply (integral_variance_le_second_moment (h.randomLine_integrable x y)
    (h.randomLine_sq_integrable x y)).trans
  rw [integral_prod _ (h.randomLine_sq_integrable x y)]
  have hb := integral_mono_of_nonneg
    (μ := unitLine) (Eventually.of_forall (fun t =>
      integral_nonneg (μ := μ) (fun z => sq_nonneg ‖randomLineHvp f x y (t,z)‖)))
    (integrable_const ((P.hessianNoise^2+P.gradientLip^2)*‖y-x‖^2))
    (Eventually.of_forall (fun t => h.hvp_second_moment (x+t•(y-x)) (y-x)))
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hb

end
end SecondOrder
