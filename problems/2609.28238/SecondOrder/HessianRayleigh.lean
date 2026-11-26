import SecondOrder.RayleighNoise
import SecondOrder.AdaptiveAnchor

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- A scalar curvature observation, obtainable from one HVP reply. -/
def hessianRayleigh {Ω : Type*} {d : ℕ} (f : Ω → Point d → ℝ)
    (x v : Point d) (z : Ω) : ℝ := ⟪hessian (f z) x v,v⟫_ℝ

theorem hessianRayleigh_one_query {Ω : Type*} {d : ℕ} (f : Ω → Point d → ℝ)
    (x v : Point d) (z : Ω) :
    hessianRayleigh f x v z = ⟪hvpReply f z (.hvp x v),v⟫_ℝ := rfl

theorem hessianRayleigh_error_bound {Ω : Type*} {d : ℕ} (F : Point d → ℝ)
    (f : Ω → Point d → ℝ) (x v : Point d) (z : Ω) :
    ‖hessianRayleigh f x v z - ⟪hessian F x v,v⟫_ℝ‖^2 ≤
      ‖(hessian (f z) x - hessian F x) v‖^2 * ‖v‖^2 := by
  have he : hessianRayleigh f x v z - ⟪hessian F x v,v⟫_ℝ =
      ⟪(hessian (f z) x - hessian F x) v,v⟫_ℝ := by
    simp [hessianRayleigh, inner_sub_left]
  rw [he]
  have hc : ‖⟪(hessian (f z) x - hessian F x) v,v⟫_ℝ‖ ≤
      ‖(hessian (f z) x - hessian F x) v‖ * ‖v‖ := norm_inner_le_norm _ _
  have hb := pow_le_pow_left₀ (norm_nonneg _) hc 2
  simpa only [mul_pow] using hb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.populationRayleigh_measurable (h : CommonLoss μ P ν F f) :
    Measurable (fun w : Point d × Point d => ⟪hessian F w.1 w.2,w.2⟫_ℝ) := by
  have hv : Measurable (fun w : Point d × Point d => hessian F w.1 w.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      (((continuous_hessian h.population_smooth).measurable.comp measurable_fst).prodMk measurable_snd)
  exact (continuous_fst.inner continuous_snd).measurable.comp (hv.prodMk measurable_snd)

theorem CommonLoss.hessianRayleigh_measurable (h : CommonLoss μ P ν F f) :
    Measurable (fun w : (Point d × Point d) × Ω => hessianRayleigh f w.1.1 w.1.2 w.2) := by
  have hv : Measurable (fun w : (Point d × Point d) × Ω => hessian (f w.2) w.1.1 w.1.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((h.hessian_measurable.comp (measurable_snd.prodMk measurable_fst.fst)).prodMk measurable_fst.snd)
  exact (continuous_fst.inner continuous_snd).measurable.comp (hv.prodMk measurable_fst.snd)

theorem CommonLoss.hessianRayleigh_integrable (h : CommonLoss μ P ν F f) (x v : Point d) :
    Integrable (hessianRayleigh f x v) μ :=
  ((ContinuousLinearMap.apply ℝ (Point d) v).integrable_comp (h.hessian_integrable x)).inner_const v

theorem CommonLoss.hessianRayleigh_mean (h : CommonLoss μ P ν F f) (x v : Point d) :
    (∫ z, hessianRayleigh f x v z ∂μ) = ⟪hessian F x v,v⟫_ℝ := by
  have hi : Integrable (fun z => hessian (f z) x v) μ :=
    (ContinuousLinearMap.apply ℝ (Point d) v).integrable_comp (h.hessian_integrable x)
  unfold hessianRayleigh
  have hc (z : Ω) : ⟪hessian (f z) x v,v⟫_ℝ = ⟪v,hessian (f z) x v⟫_ℝ := real_inner_comm _ _
  simp_rw [hc]
  rw [integral_inner hi v, ← ContinuousLinearMap.integral_apply (h.hessian_integrable x) v,
    h.hessian_unbiased x, real_inner_comm]

theorem CommonLoss.hessianRayleigh_error_integrable (h : CommonLoss μ P ν F f) (x v : Point d) :
    Integrable (fun z => ‖hessianRayleigh f x v z - ⟪hessian F x v,v⟫_ℝ‖^2) μ := by
  have hm : Measurable (hessianRayleigh f x v) :=
    Measurable.comp
      (g := fun w : (Point d × Point d) × Ω => hessianRayleigh f w.1.1 w.1.2 w.2)
      (f := fun z : Ω => ((x,v),z)) h.hessianRayleigh_measurable
      (measurable_const.prodMk measurable_id)
  apply ((h.hvp_error_integrable x v).mul_const (‖v‖^2)).mono'
    ((hm.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hessianRayleigh_error_bound F f x v z

theorem CommonLoss.hessianRayleigh_variance (h : CommonLoss μ P ν F f) (x v : Point d) :
    (∫ z, ‖hessianRayleigh f x v z - ⟪hessian F x v,v⟫_ℝ‖^2 ∂μ) ≤
      P.hessianNoise^2 * ‖v‖^4 := by
  have hb := integral_mono (h.hessianRayleigh_error_integrable x v)
    ((h.hvp_error_integrable x v).mul_const (‖v‖^2)) (hessianRayleigh_error_bound F f x v)
  rw [integral_mul_const] at hb
  have hv := mul_le_mul_of_nonneg_right (h.hvp_variance x v) (sq_nonneg ‖v‖)
  exact hb.trans (by nlinarith [hv])

/-- The common almost-sure operator bound also bounds the scalar
validation variance. This avoids charging the independent HVP variance
parameter to the eigensolver. -/
theorem CommonLoss.hessianRayleigh_bounded_variance (h : CommonLoss μ P ν F f)
    (x v : Point d) :
    (∫ z, ‖hessianRayleigh f x v z - ⟪hessian F x v,v⟫_ℝ‖^2 ∂μ) ≤
      P.hessianBound^2 * ‖v‖^4 := by
  have hb : ∀ᵐ z ∂μ,
      ‖hessianRayleigh f x v z - ⟪hessian F x v,v⟫_ℝ‖^2 ≤ P.hessianBound^2 * ‖v‖^4 := by
    filter_upwards [h.global_hessian_bound] with z hz
    have ho := ((hessian (f z) x - hessian F x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hz x) (norm_nonneg v))
    have hs := pow_le_pow_left₀ (norm_nonneg _) ho 2
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖v‖)
    exact (hessianRayleigh_error_bound F f x v z).trans (by nlinarith [hm])
  simpa using integral_mono_ae (h.hessianRayleigh_error_integrable x v)
    (integrable_const (P.hessianBound^2 * ‖v‖^4)) hb

end
end SecondOrder
