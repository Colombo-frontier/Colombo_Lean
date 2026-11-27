import Nonsmooth.StrongPotentialVariance
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Bilinear

open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem norm_mean_square_le_second {α G : Type} [MeasurableSpace α]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure α) [IsProbabilityMeasure μ] (F : α → G) (hF : MemLp F 2 μ) :
    ‖∫ x, F x ∂μ‖ ^ 2 ≤ ∫ x, ‖F x‖ ^ 2 ∂μ := by
  have hv := variance_nonneg (fun x => ‖F x‖) μ
  rw [variance_eq_sub hF.norm] at hv
  simp only [Pi.pow_apply] at hv
  have hm := norm_integral_le_integral_norm (f := F) (μ := μ)
  have h0 : 0 ≤ ∫ x, ‖F x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hs := (sq_le_sq₀ (norm_nonneg _) h0).mpr hm
  linarith

theorem bilinear_covariance_norm_bound {α A G : Type} [MeasurableSpace α]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (s : α → A) (H : α → G) (b : A →L[ℝ] A →L[ℝ] G)
    (hb : ∀ x, ‖b x x‖ ≤ ‖x‖ ^ 2)
    (hs : MemLp s 2 μ) (hH : Integrable H μ) :
    ‖(∫ x, H x - b (s x) (s x) ∂μ) + b (∫ x, s x ∂μ) (∫ x, s x ∂μ)‖ ≤
        (∫ x, ‖H x‖ ∂μ) + 2 * ∫ x, ‖s x‖ ^ 2 ∂μ := by
  have hm : AEStronglyMeasurable (fun x => b (s x) (s x)) μ :=
    b.continuous₂.comp_aestronglyMeasurable₂ hs.aestronglyMeasurable hs.aestronglyMeasurable
  have hi : Integrable (fun x => b (s x) (s x)) μ :=
    hs.norm.integrable_sq.mono' hm (Filter.Eventually.of_forall (fun x => hb (s x)))
  have hnorm := norm_add_le (∫ x, H x - b (s x) (s x) ∂μ)
    (b (∫ x, s x ∂μ) (∫ x, s x ∂μ))
  have hI := norm_integral_le_integral_norm (f := fun x => H x - b (s x) (s x)) (μ := μ)
  have hdiff : Integrable (fun x => H x - b (s x) (s x)) μ := hH.sub hi
  have hmajor : Integrable (fun x => ‖H x‖ + ‖s x‖ ^ 2) μ := hH.norm.add hs.norm.integrable_sq
  have hJ := integral_mono (f := fun x => ‖H x - b (s x) (s x)‖)
    (g := fun x => ‖H x‖ + ‖s x‖ ^ 2) hdiff.norm hmajor
    (fun x => (norm_sub_le (H x) (b (s x) (s x))).trans (add_le_add le_rfl (hb (s x))))
  rw [integral_add hH.norm hs.norm.integrable_sq] at hJ
  have hM := norm_mean_square_le_second μ s hs
  linarith [hb (∫ x, s x ∂μ)]

variable {α E : Type} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

/-- A norm bound for the Hessian expression produced by normalized
expectation differentiation, using actual first and second moments. -/
theorem score_covariance_hessian_norm_bound
    (μ : Measure α) [IsProbabilityMeasure μ]
    (s : α → E →L[ℝ] ℝ) (H : α → E →L[ℝ] E →L[ℝ] ℝ)
    (hs : MemLp s 2 μ) (hH : Integrable H μ) :
    ‖(∫ x, H x - (s x).smulRight (s x) ∂μ) +
      (∫ x, s x ∂μ).smulRight (∫ x, s x ∂μ)‖ ≤
        (∫ x, ‖H x‖ ∂μ) + 2 * ∫ x, ‖s x‖ ^ 2 ∂μ := by
  let b : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
  have hb (x : E →L[ℝ] ℝ) : ‖b x x‖ ≤ ‖x‖ ^ 2 := by
    change ‖x.smulRight x‖ ≤ ‖x‖ ^ 2
    rw [ContinuousLinearMap.norm_smulRight_apply, pow_two]
  have h := @bilinear_covariance_norm_bound α (E →L[ℝ] ℝ) (E →L[ℝ] E →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    μ inferInstance s H b hb hs hH
  have he (x y : E →L[ℝ] ℝ) : b x y = x.smulRight y := rfl
  simpa only [he] using h

end
end Nonsmooth
