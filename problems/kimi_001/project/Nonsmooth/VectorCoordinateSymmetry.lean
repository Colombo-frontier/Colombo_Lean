import Nonsmooth.VectorCoordinateMoments

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
local instance coordinateSymmetryDualNormedGroup {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] :
    NormedAddCommGroup (A →L[ℝ] ℝ) := inferInstance
local instance coordinateSymmetryDualNormedSpace {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] :
    NormedSpace ℝ (A →L[ℝ] ℝ) := inferInstance


theorem score_covariance_hessian_symmetric {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (s : α → E →L[ℝ] ℝ) (H : α → E →L[ℝ] E →L[ℝ] ℝ)
    (hs : MemLp s 2 μ) (hH : Integrable H μ)
    (hsym : ∀ x v w, H x v w = H x w v) (v w : E) :
    ((∫ x, H x - (s x).smulRight (s x) ∂μ) +
      (∫ x, s x ∂μ).smulRight (∫ x, s x ∂μ)) v w =
    ((∫ x, H x - (s x).smulRight (s x) ∂μ) +
      (∫ x, s x ∂μ).smulRight (∫ x, s x ∂μ)) w v := by
  have hi := score_tensor_integrable μ s hs
  have hd : Integrable (fun x => H x - (s x).smulRight (s x)) μ :=
    Integrable.sub (f := H) (g := fun x => (s x).smulRight (s x)) hH hi
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, smul_eq_mul]
  rw [continuous_bilinear_integral_apply μ _ hd v w,
    continuous_bilinear_integral_apply μ _ hd w v]
  have he (x : α) : (H x - (s x).smulRight (s x)) v w =
      (H x - (s x).smulRight (s x)) w v := by
    simp only [sub_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, smul_eq_mul, hsym x v w, mul_comm]
  rw [integral_congr_ae (Filter.Eventually.of_forall he)]
  ring

theorem vectorCoordinate_hessian_symmetric {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → ℝ → ℝ} (H : RegularVectorCoordinateFamily V)
    (hsym : ∀ t x v w, H.hessian t x v w = H.hessian t x w v) (t v w : E) :
    vectorCoordinateHessian H t v w = vectorCoordinateHessian H t w v :=
  score_covariance_hessian_symmetric _ (H.score t) (H.hessian t)
    (vectorCoordinate_score_memLp_two H t) (vectorCoordinate_hessian_integrable H t) (hsym t) v w

end
end Nonsmooth
