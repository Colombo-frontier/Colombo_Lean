import SecondOrder.OjaStepMoments
import SecondOrder.IntegralMoments

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

def shiftedRayleighError {Ω : Type*} {d : ℕ} (P : Parameters)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ) (x v : Point d) (z : Ω) : ℝ :=
  ⟪sampledShiftedHessian P f x z v,v⟫_ℝ -
    ⟪shiftedHessian (eigenHessianBound P) (hessian F x) v,v⟫_ℝ

theorem integral_add_sq_zero_mean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Integrable X μ) (hX2 : Integrable (fun z => X z ^ 2) μ)
    (hzero : (∫ z, X z ∂μ) = 0) (c : ℝ) :
    (∫ z, (c + X z)^2 ∂μ) = c^2 + ∫ z, X z^2 ∂μ := by
  have hn : Integrable (fun z => ‖X z‖^2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hX2
  simpa only [Real.norm_eq_abs, sq_abs, add_comm] using
    integral_norm_add_sq_of_mean_zero hX hn hzero c

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.mean_shifted_rayleigh_measurable (h : CommonLoss μ P ν F f) :
    Measurable (fun w : Point d × Point d =>
      ⟪shiftedHessian (eigenHessianBound P) (hessian F w.1) w.2,w.2⟫_ℝ) := by
  have hm : Measurable (fun x : Point d => shiftedHessian (eigenHessianBound P) (hessian F x)) := by
    unfold shiftedHessian
    exact (measurable_const.sub (continuous_hessian h.population_smooth).measurable).const_smul
      ((2 * eigenHessianBound P)⁻¹)
  have hv : Measurable (fun w : Point d × Point d =>
      shiftedHessian (eigenHessianBound P) (hessian F w.1) w.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hm.comp measurable_fst).prodMk measurable_snd)
  exact (continuous_fst.inner continuous_snd).measurable.comp (hv.prodMk measurable_snd)

theorem CommonLoss.shiftedRayleighError_measurable (h : CommonLoss μ P ν F f) :
    Measurable (fun w : (Point d × Point d) × Ω =>
      shiftedRayleighError P F f w.1.1 w.1.2 w.2) := by
  have hv := h.shifted_hvp_adaptive_measurable
    (show Measurable (fun w : Point d × Point d => w.1) from measurable_fst)
    (show Measurable (fun w : Point d × Point d => w.2) from measurable_snd)
  exact ((continuous_fst.inner continuous_snd).measurable.comp
    (hv.prodMk measurable_fst.snd)).sub (h.mean_shifted_rayleigh_measurable.comp measurable_fst)

theorem CommonLoss.shiftedRayleighError_integrable (h : CommonLoss μ P ν F f) (x v : Point d) :
    Integrable (shiftedRayleighError P F f x v) μ :=
  ((h.shifted_hvp_integrable x v).inner_const v).sub (integrable_const _)

theorem CommonLoss.shiftedRayleighError_mean (h : CommonLoss μ P ν F f) (x v : Point d) :
    (∫ z, shiftedRayleighError P F f x v z ∂μ) = 0 := by
  unfold shiftedRayleighError
  rw [integral_sub ((h.shifted_hvp_integrable x v).inner_const v) (integrable_const _),
    h.shifted_rayleigh_mean]
  simp

/-- The bound holds on one event for every possible query point and
direction, so it can be used after any measurable sample history. -/
theorem CommonLoss.shiftedRayleighError_abs_bound (h : CommonLoss μ P ν F f) :
    ∀ᵐ z ∂μ, ∀ (x v : Point d), |shiftedRayleighError P F f x v z| ≤ ‖v‖^2 := by
  filter_upwards [h.shifted_hessian_good] with z hz
  intro x v
  have hs := (hz x).2.2 v
  have hm := (h.mean_shifted_hessian_good x).2.2 v
  unfold shiftedRayleighError
  exact abs_le.mpr ⟨by linarith [hs.1,hm.2], by linarith [hs.2,hm.1]⟩

theorem CommonLoss.shiftedRayleighError_sq_integrable (h : CommonLoss μ P ν F f) (x v : Point d) :
    Integrable (fun z => shiftedRayleighError P F f x v z ^ 2) μ := by
  have hi : Measurable (fun z : Ω => ((x,v),z)) := measurable_const.prodMk measurable_id
  have hm := h.shiftedRayleighError_measurable.comp hi
  apply (integrable_const ((‖v‖^2)^2)).mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [h.shiftedRayleighError_abs_bound] with z hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hz x v) 2

theorem CommonLoss.shiftedRayleighError_second_moment (h : CommonLoss μ P ν F f)
    (x v : Point d) : (∫ z, shiftedRayleighError P F f x v z ^ 2 ∂μ) ≤ ‖v‖^4 := by
  have hb := integral_mono_ae (h.shiftedRayleighError_sq_integrable x v)
    (integrable_const (‖v‖^4)) (show ∀ᵐ z ∂μ, shiftedRayleighError P F f x v z ^ 2 ≤ ‖v‖^4 from by
      filter_upwards [h.shiftedRayleighError_abs_bound] with z hz
      have hs := pow_le_pow_left₀ (abs_nonneg _) (hz x v) 2
      simpa only [sq_abs, ← pow_mul] using hs)
  simpa using hb

end
end SecondOrder
