import Nonsmooth.VectorScoreCovarianceBound

open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
local instance scoreEvaluationDualNormedGroup {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance scoreEvaluationDualNormedSpace {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance


theorem score_tensor_integrable {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (s : α → E →L[ℝ] ℝ) (hs : MemLp s 2 μ) :
    Integrable (fun x => (s x).smulRight (s x)) μ := by
  have hm : AEStronglyMeasurable (fun x => (s x).smulRight (s x)) μ :=
    (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous₂.comp_aestronglyMeasurable₂
      hs.aestronglyMeasurable hs.aestronglyMeasurable
  apply Integrable.mono' (g := fun x => ‖s x‖ ^ 2) (f := fun x => (s x).smulRight (s x))
    hs.norm.integrable_sq hm
  exact Filter.Eventually.of_forall (fun x => by
    rw [ContinuousLinearMap.norm_smulRight_apply, pow_two])

theorem continuous_bilinear_integral_apply {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (H : α → E →L[ℝ] E →L[ℝ] ℝ)
    (hH : Integrable H μ) (u v : E) :
    (∫ x, H x ∂μ) u v = ∫ x, H x u v ∂μ := by
  rw [ContinuousLinearMap.integral_apply hH]
  have hi : Integrable (fun x => H x u) μ :=
    Integrable.apply_continuousLinearMap (φ := H) hH u
  exact ContinuousLinearMap.integral_apply hi v

/-- Evaluation of the actual covariance Hessian is the mean directional
Hessian minus the variance of the directional score. -/
theorem score_covariance_hessian_apply {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (s : α → E →L[ℝ] ℝ) (H : α → E →L[ℝ] E →L[ℝ] ℝ)
    (hs : MemLp s 2 μ) (hH : Integrable H μ) (v : E) :
    ((∫ x, H x - (s x).smulRight (s x) ∂μ) +
      (∫ x, s x ∂μ).smulRight (∫ x, s x ∂μ)) v v =
        (∫ x, H x v v ∂μ) - variance (fun x => s x v) μ := by
  have hi := score_tensor_integrable μ s hs
  have hd : Integrable (fun x => H x - (s x).smulRight (s x)) μ :=
    Integrable.sub (f := H) (g := fun x => (s x).smulRight (s x)) hH hi
  have hsv : MemLp (fun x => s x v) 2 μ :=
    (ContinuousLinearMap.apply ℝ ℝ v).comp_memLp' hs
  have hHv : Integrable (fun x => H x v v) μ :=
    Integrable.apply_continuousLinearMap (φ := fun x => H x v)
      (Integrable.apply_continuousLinearMap (φ := H) hH v) v
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [continuous_bilinear_integral_apply μ _ hd v v]
  simp only [sub_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, smul_eq_mul,
    ← pow_two]
  rw [integral_sub hHv hsv.integrable_sq,
    ContinuousLinearMap.integral_apply (hs.integrable (by norm_num)), variance_eq_sub hsv]
  simp only [Pi.pow_apply]
  ring

end
end Nonsmooth
