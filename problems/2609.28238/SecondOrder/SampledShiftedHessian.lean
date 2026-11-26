import SecondOrder.ShiftedHessian

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

def sampledShiftedHessian (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (z : Ω) : Point d →L[ℝ] Point d :=
  shiftedHessian (eigenHessianBound P) (hessian (f z) x)

theorem CommonLoss.shifted_hessian_measurable (h : CommonLoss μ P ν F f) :
    Measurable (fun zx : Ω × Point d => sampledShiftedHessian P f zx.2 zx.1) := by
  unfold sampledShiftedHessian shiftedHessian
  exact (measurable_const.sub h.hessian_measurable).const_smul ((2 * eigenHessianBound P)⁻¹)

theorem CommonLoss.shifted_hessian_integrable (h : CommonLoss μ P ν F f)
    (x : Point d) : Integrable (sampledShiftedHessian P f x) μ := by
  unfold sampledShiftedHessian shiftedHessian
  exact ((integrable_const _).sub (h.hessian_integrable x)).smul ((2 * eigenHessianBound P)⁻¹)

theorem CommonLoss.shifted_hessian_unbiased (h : CommonLoss μ P ν F f)
    (x : Point d) : (∫ z, sampledShiftedHessian P f x z ∂μ) =
      shiftedHessian (eigenHessianBound P) (hessian F x) := by
  simp only [sampledShiftedHessian, shiftedHessian]
  rw [integral_smul, integral_sub (integrable_const _) (h.hessian_integrable x),
    h.hessian_unbiased]
  simp

/-- A common full-measure event supplies all the hypotheses of the
positive-contraction stochastic power iteration at every possible point. -/
theorem CommonLoss.shifted_hessian_good (h : CommonLoss μ P ν F f) :
    ∀ᵐ z ∂μ, ∀ x, (sampledShiftedHessian P f x z).toLinearMap.IsSymmetric ∧
      ‖sampledShiftedHessian P f x z‖ ≤ 1 ∧
      ∀ v, 0 ≤ ⟪sampledShiftedHessian P f x z v, v⟫_ℝ ∧
        ⟪sampledShiftedHessian P f x z v, v⟫_ℝ ≤ ‖v‖^2 := by
  filter_upwards [h.sample_hessian_symmetric_bounded] with z hz
  intro x
  exact ⟨shiftedHessian_symmetric _ (hz x).1,
    shiftedHessian_norm_le_one (eigenHessianBound_pos P) (hz x).2,
    shiftedHessian_rayleigh_bounds (eigenHessianBound_pos P) (hz x).2⟩

/-- The deterministic mean enjoys the same contraction and positivity bounds. -/
theorem CommonLoss.mean_shifted_hessian_good (h : CommonLoss μ P ν F f) (x : Point d) :
    (shiftedHessian (eigenHessianBound P) (hessian F x)).toLinearMap.IsSymmetric ∧
      ‖shiftedHessian (eigenHessianBound P) (hessian F x)‖ ≤ 1 ∧
      ∀ v, 0 ≤ ⟪shiftedHessian (eigenHessianBound P) (hessian F x) v, v⟫_ℝ ∧
        ⟪shiftedHessian (eigenHessianBound P) (hessian F x) v, v⟫_ℝ ≤ ‖v‖^2 := by
  have hb : ‖hessian F x‖ ≤ eigenHessianBound P :=
    (h.population_hessian_norm x).trans (le_add_of_nonneg_right P.hessianBound_pos.le)
  exact ⟨shiftedHessian_symmetric _ (h.population_hessian_symmetric x),
    shiftedHessian_norm_le_one (eigenHessianBound_pos P) hb,
    shiftedHessian_rayleigh_bounds (eigenHessianBound_pos P) hb⟩

/-- The transformed product can be evaluated from exactly one permitted
Hessian-vector reply, without reading a matrix or another point. -/
theorem sampledShiftedHessian_one_hvp (P : Parameters) (f : Ω → Point d → ℝ)
    (x v : Point d) (z : Ω) : sampledShiftedHessian P f x z v =
      (2 * eigenHessianBound P)⁻¹ • (eigenHessianBound P • v - hvpReply f z (.hvp x v)) := rfl

theorem CommonLoss.shifted_hvp_integrable (h : CommonLoss μ P ν F f) (x v : Point d) :
    Integrable (fun z => sampledShiftedHessian P f x z v) μ :=
  (ContinuousLinearMap.apply ℝ (Point d) v).integrable_comp (h.shifted_hessian_integrable x)

theorem CommonLoss.shifted_hvp_unbiased (h : CommonLoss μ P ν F f) (x v : Point d) :
    (∫ z, sampledShiftedHessian P f x z v ∂μ) =
      shiftedHessian (eigenHessianBound P) (hessian F x) v := by
  rw [← ContinuousLinearMap.integral_apply (h.shifted_hessian_integrable x) v,
    h.shifted_hessian_unbiased]

/-- Joint measurability allows the point and direction to be selected from
an arbitrary measurable past before the fresh sample is drawn. -/
theorem CommonLoss.shifted_hvp_adaptive_measurable {A : Type*} [MeasurableSpace A]
    (h : CommonLoss μ P ν F f) {x v : A → Point d}
    (hx : Measurable x) (hv : Measurable v) :
    Measurable (fun w : A × Ω => sampledShiftedHessian P f (x w.1) w.2 (v w.1)) := by
  have hH := h.shifted_hessian_measurable.comp
    (measurable_snd.prodMk (hx.comp measurable_fst))
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp
    (hH.prodMk (hv.comp measurable_fst))

end
end SecondOrder
