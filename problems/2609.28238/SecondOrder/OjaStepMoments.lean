import SecondOrder.OjaEnergy

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaUpdate_measurable (h : CommonLoss μ P ν F f)
    (η : ℝ) (x v : Point d) :
    Measurable (fun z => ojaUpdate η (sampledShiftedHessian P f x z) v) := by
  have hm : Measurable (fun z => sampledShiftedHessian P f x z v) :=
    (ContinuousLinearMap.apply ℝ (Point d) v).continuous.measurable.comp
      (h.shifted_hessian_measurable.comp (measurable_id.prodMk measurable_const))
  exact measurable_const.add (hm.const_smul η)

theorem CommonLoss.ojaUpdate_integrable (h : CommonLoss μ P ν F f)
    (η : ℝ) (x v : Point d) :
    Integrable (fun z => ojaUpdate η (sampledShiftedHessian P f x z) v) μ :=
  (integrable_const v).add ((h.shifted_hvp_integrable x v).smul η)

theorem CommonLoss.ojaUpdate_mean (h : CommonLoss μ P ν F f) (η : ℝ) (x v : Point d) :
    (∫ z, ojaUpdate η (sampledShiftedHessian P f x z) v ∂μ) =
      ojaUpdate η (shiftedHessian (eigenHessianBound P) (hessian F x)) v := by
  have hadd := integral_add (integrable_const v) ((h.shifted_hvp_integrable x v).smul η)
  simp only [Pi.smul_apply] at hadd
  rw [show (fun z => ojaUpdate η (sampledShiftedHessian P f x z) v) =
      (fun z => v + η • sampledShiftedHessian P f x z v) from rfl,
    hadd, integral_smul, h.shifted_hvp_unbiased]
  simp [ojaUpdate]

theorem CommonLoss.ojaUpdate_norm_bound (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (x v : Point d) :
    ∀ᵐ z ∂μ, ‖ojaUpdate η (sampledShiftedHessian P f x z) v‖ ≤ (1 + η) * ‖v‖ := by
  filter_upwards [h.shifted_hessian_good] with z hz
  exact ojaUpdate_norm_upper hη (hz x).2.1 v

theorem CommonLoss.ojaUpdate_norm_pow_integrable (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (x v : Point d) (k : ℕ) :
    Integrable (fun z => ‖ojaUpdate η (sampledShiftedHessian P f x z) v‖^k) μ := by
  apply (integrable_const (((1 + η) * ‖v‖)^k)).mono'
    ((h.ojaUpdate_measurable η x v).norm.pow_const k).aestronglyMeasurable
  filter_upwards [h.ojaUpdate_norm_bound hη x v] with z hz
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) k)]
  exact pow_le_pow_left₀ (norm_nonneg _) hz k

theorem CommonLoss.shifted_rayleigh_mean (h : CommonLoss μ P ν F f) (x v : Point d) :
    (∫ z, ⟪sampledShiftedHessian P f x z v, v⟫_ℝ ∂μ) =
      ⟪shiftedHessian (eigenHessianBound P) (hessian F x) v, v⟫_ℝ := by
  have hc (z : Ω) : ⟪sampledShiftedHessian P f x z v, v⟫_ℝ =
      ⟪v, sampledShiftedHessian P f x z v⟫_ℝ := real_inner_comm _ _
  simp_rw [hc]
  rw [integral_inner (h.shifted_hvp_integrable x v) v, h.shifted_hvp_unbiased,
    real_inner_comm]

/-- The fourth-moment estimate keeps the largest-mean-Rayleigh parameter ℓ,
instead of replacing it by the coarser bound 1. -/
theorem CommonLoss.ojaUpdate_fourth_moment (h : CommonLoss μ P ν F f)
    {η ℓ : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (x v : Point d)
    (hℓ : ⟪shiftedHessian (eigenHessianBound P) (hessian F x) v, v⟫_ℝ ≤ ℓ * ‖v‖^2) :
    (∫ z, ‖ojaUpdate η (sampledShiftedHessian P f x z) v‖^4 ∂μ) ≤
      (1 + (4 * η + 11 * η^2) * ℓ) * ‖v‖^4 := by
  have hi : Integrable (fun z => ‖v‖^4 + (4 * η + 11 * η^2) * ‖v‖^2 *
      ⟪sampledShiftedHessian P f x z v, v⟫_ℝ) μ :=
    (integrable_const _).add (((h.shifted_hvp_integrable x v).inner_const v).const_mul _)
  have hb := integral_mono_ae (h.ojaUpdate_norm_pow_integrable hη x v 4) hi
    (show ∀ᵐ z ∂μ, ‖ojaUpdate η (sampledShiftedHessian P f x z) v‖^4 ≤
      ‖v‖^4 + (4 * η + 11 * η^2) * ‖v‖^2 *
        ⟪sampledShiftedHessian P f x z v, v⟫_ℝ from by
      filter_upwards [h.sample_hessian_symmetric_bounded] with z hz
      exact ojaUpdate_norm_four_le hη hη1
        (shiftedHessian_firm (eigenHessianBound_pos P) (hz x).2 v)
        (shiftedHessian_rayleigh_bounds (eigenHessianBound_pos P) (hz x).2 v).2)
  rw [integral_add (integrable_const _)
      (((h.shifted_hvp_integrable x v).inner_const v).const_mul _),
    integral_const_mul, h.shifted_rayleigh_mean] at hb
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hb
  have hm := mul_le_mul_of_nonneg_left hℓ
    (by positivity : 0 ≤ (4 * η + 11 * η^2) * ‖v‖^2)
  nlinarith

end
end SecondOrder
