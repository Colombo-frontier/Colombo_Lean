import SecondOrder.ContinuousChord

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

def centeredLineHvp (F : Point d → ℝ) (f : Ω → Point d → ℝ)
    (x y : Point d) (w : ℝ × Ω) : Point d :=
  (hessian (f w.2) (x+w.1•(y-x))-hessian F (x+w.1•(y-x))) (y-x)

def centeredGradientDifference (F : Point d → ℝ) (f : Ω → Point d → ℝ)
    (x y : Point d) (z : Ω) : Point d :=
  (gradient (f z) y-gradient F y)-(gradient (f z) x-gradient F x)

theorem CommonLoss.centeredLine_measurable (h : CommonLoss μ P ν F f) (x y : Point d) :
    Measurable (centeredLineHvp F f x y) := by
  have hp : Measurable (fun w : ℝ × Ω => x+w.1•(y-x)) :=
    measurable_const.add (measurable_fst.smul measurable_const)
  exact (ContinuousLinearMap.apply ℝ (Point d) (y-x)).continuous.measurable.comp
    ((h.hessian_measurable.comp (measurable_snd.prodMk hp)).sub
      ((continuous_hessian h.population_smooth).measurable.comp hp))

theorem CommonLoss.centeredLine_norm_bound (h : CommonLoss μ P ν F f) (x y : Point d) :
    ∀ᵐ w ∂unitLine.prod μ, ‖centeredLineHvp F f x y w‖ ≤ P.hessianBound*‖y-x‖ := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le (h.centeredLine_measurable x y).norm measurable_const)).mpr
  apply Eventually.of_forall
  intro t
  filter_upwards [h.global_hessian_bound] with z hz
  exact ((hessian (f z) (x+t•(y-x))-hessian F (x+t•(y-x))).le_opNorm (y-x)).trans
    (mul_le_mul_of_nonneg_right (hz _) (norm_nonneg _))

theorem CommonLoss.centeredLine_integrable (h : CommonLoss μ P ν F f) (x y : Point d) :
    Integrable (centeredLineHvp F f x y) (unitLine.prod μ) :=
  (integrable_const (P.hessianBound*‖y-x‖)).mono'
    (h.centeredLine_measurable x y).aestronglyMeasurable (h.centeredLine_norm_bound x y)

theorem CommonLoss.centeredLine_sq_integrable (h : CommonLoss μ P ν F f) (x y : Point d) :
    Integrable (fun w => ‖centeredLineHvp F f x y w‖^2) (unitLine.prod μ) := by
  apply (integrable_const ((P.hessianBound*‖y-x‖)^2)).mono'
    ((h.centeredLine_measurable x y).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [h.centeredLine_norm_bound x y] with w hw
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hw 2

theorem CommonLoss.centeredGradient_measurable (h : CommonLoss μ P ν F f) (x y : Point d) :
    Measurable (centeredGradientDifference F f x y) :=
  ((h.gradient_measurable.comp (measurable_id.prodMk measurable_const)).sub measurable_const).sub
    ((h.gradient_measurable.comp (measurable_id.prodMk measurable_const)).sub measurable_const)

theorem CommonLoss.centeredGradient_line_identity (h : CommonLoss μ P ν F f) (x y : Point d) :
    ∀ᵐ z ∂μ, (∫ t, centeredLineHvp F f x y (t,z) ∂unitLine) =
      centeredGradientDifference F f x y z := by
  filter_upwards [h.sample_regularity] with z hz
  rw [integral_unitLine]
  exact centered_gradient_line_integral (gradient_has_hessian h.population_smooth)
    (gradient_has_hessian hz.1) (continuous_hessian h.population_smooth)
    (continuous_hessian hz.1) x y

theorem CommonLoss.centeredGradient_jensen (h : CommonLoss μ P ν F f) (x y : Point d) :
    ∀ᵐ z ∂μ, ‖centeredGradientDifference F f x y z‖^2 ≤
      ∫ t, ‖centeredLineHvp F f x y (t,z)‖^2 ∂unitLine := by
  filter_upwards [h.centeredGradient_line_identity x y,
    (h.centeredLine_integrable x y).prod_left_ae,
    (h.centeredLine_sq_integrable x y).prod_left_ae] with z hz hzi hz2
  rw [← hz]
  exact norm_integral_sq_le hzi hz2

theorem CommonLoss.centeredGradient_sq_integrable (h : CommonLoss μ P ν F f) (x y : Point d) :
    Integrable (fun z => ‖centeredGradientDifference F f x y z‖^2) μ := by
  apply (h.centeredLine_sq_integrable x y).integral_prod_right.mono'
    ((h.centeredGradient_measurable x y).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [h.centeredGradient_jensen x y] with z hz
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz

/-- Appendix (app:mss): the common scalar loss enforces mean-square regularity
of its centered gradients, although the oracle never exposes paired samples. -/
theorem CommonLoss.centeredGradient_mean_square (h : CommonLoss μ P ν F f) (x y : Point d) :
    (∫ z, ‖centeredGradientDifference F f x y z‖^2 ∂μ) ≤
      P.hessianNoise^2*‖y-x‖^2 := by
  have hsq := h.centeredLine_sq_integrable x y
  calc
    _ ≤ ∫ z, ∫ t, ‖centeredLineHvp F f x y (t,z)‖^2 ∂unitLine ∂μ :=
      integral_mono_ae (h.centeredGradient_sq_integrable x y)
        hsq.integral_prod_right (h.centeredGradient_jensen x y)
    _ = ∫ w, ‖centeredLineHvp F f x y w‖^2 ∂unitLine.prod μ :=
      (integral_prod_symm _ hsq).symm
    _ = ∫ t, ∫ z, ‖centeredLineHvp F f x y (t,z)‖^2 ∂μ ∂unitLine := integral_prod _ hsq
    _ ≤ ∫ t : ℝ, P.hessianNoise^2*‖y-x‖^2 ∂unitLine :=
      integral_mono_ae hsq.integral_prod_left (integrable_const _)
        (Eventually.of_forall (fun t => h.hvp_variance (x+t•(y-x)) (y-x)))
    _ = _ := by simp

end
end SecondOrder
