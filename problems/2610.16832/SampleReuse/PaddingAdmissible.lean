import SampleReuse.PaddingGeometry

open SecondOrder MeasureTheory

namespace SampleReuse
noncomputable section

/-- Zero padding preserves all model bounds. The everywhere-smooth sample
hypothesis holds for both constructed hard families, including every finite
coefficient table, so no exceptional samples need to be modified. -/
theorem Admissible.zero_pad {Ω : Type*} [MeasurableSpace Ω] {m d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point m → ℝ} {F : Ω → Point m → ℝ} {x₀ : Point m}
    (h : Admissible μ P f F x₀) (hF : ∀ z, ContDiff ℝ 2 (F z))
    (U : Point m →ₗᵢ[ℝ] Point d) :
    Admissible μ P (paddedLoss U f) (fun z => paddedLoss U (F z)) (U x₀) := by
  have hgrad (z : Ω) (x : Point d) : gradient (paddedLoss U (F z)) x =
      U (gradient (F z) (isometryProjection U x)) :=
    congrFun (paddedLoss_gradient U ((hF z).differentiable (by norm_num))) x
  have hH (z : Ω) (x : Point d) : hessian (paddedLoss U (F z)) x =
      liftedHessian U (hessian (F z) (isometryProjection U x)) := paddedLoss_hessian U (hF z) x
  have hgpop (x : Point d) : gradient (paddedLoss U f) x =
      U (gradient f (isometryProjection U x)) :=
    congrFun (paddedLoss_gradient U (h.population_smooth.differentiable (by norm_num))) x
  have hHpop (x : Point d) : hessian (paddedLoss U f) x =
      liftedHessian U (hessian f (isometryProjection U x)) := paddedLoss_hessian U h.population_smooth x
  have hp : Measurable (fun zx : Ω × Point d => (zx.1,isometryProjection U zx.2)) :=
    measurable_fst.prodMk ((isometryProjection U).continuous.measurable.comp measurable_snd)
  refine ⟨h.population_smooth.comp (isometryProjection U).contDiff,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x
    simpa only [paddedLoss,Function.comp_apply,isometryProjection_map] using
      h.gap_bound (isometryProjection U x)
  · exact h.value_measurable.comp hp
  · simp_rw [hgrad]
    exact U.continuous.measurable.comp (h.gradient_measurable.comp hp)
  · simp_rw [hH]
    exact (liftedHessian U).continuous.measurable.comp (h.hessian_measurable.comp hp)
  · filter_upwards [h.sample_regularity] with z hz
    refine ⟨(hF z).comp (isometryProjection U).contDiff,?_,?_⟩
    · intro x y
      rw [hgrad,hgrad,← U.map_sub,U.norm_map]
      have hh := hz.2.1 (isometryProjection U x) (isometryProjection U y)
      rw [← map_sub] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (isometryProjection_apply_norm U (x-y)) P.gradientLip_pos.le)
    · intro x y
      rw [hH,hH,← map_sub]
      have hh := hz.2.2 (isometryProjection U x) (isometryProjection U y)
      rw [← map_sub] at hh
      exact (liftedHessian_norm U _).trans (hh.trans
        (mul_le_mul_of_nonneg_left (isometryProjection_apply_norm U (x-y)) P.hessianLip_pos.le))
  · intro x
    exact h.value_integrable (isometryProjection U x)
  · intro x
    simp_rw [hgrad]
    exact U.toContinuousLinearMap.integrable_comp (h.gradient_integrable (isometryProjection U x))
  · intro x
    simp_rw [hH]
    exact (liftedHessian U).integrable_comp (h.hessian_integrable (isometryProjection U x))
  · intro x
    exact h.value_unbiased (isometryProjection U x)
  · intro x
    simp_rw [hgrad,hgpop]
    change (∫ z, U.toContinuousLinearMap (gradient (F z) (isometryProjection U x)) ∂μ) = _
    rw [U.toContinuousLinearMap.integral_comp_comm (h.gradient_integrable _),h.gradient_unbiased]
    rfl
  · intro x
    simp_rw [hH,hHpop]
    rw [(liftedHessian U).integral_comp_comm (h.hessian_integrable _),h.hessian_unbiased]
  · filter_upwards [h.noise_bound] with z hz
    intro x
    constructor
    · rw [hgrad,hgpop,← U.map_sub,U.norm_map]
      exact (hz (isometryProjection U x)).1
    · rw [hH,hHpop,← map_sub]
      exact (liftedHessian_norm U _).trans (hz (isometryProjection U x)).2
  · intro x
    rw [hgpop,U.norm_map]
    exact h.population_gradient_bound _

end
end SampleReuse
