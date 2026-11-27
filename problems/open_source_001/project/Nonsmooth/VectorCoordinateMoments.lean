import Nonsmooth.RegularVectorCoordinateFamily
import Nonsmooth.PolynomialVectorDensityMoments
import Nonsmooth.ScoreCovarianceEvaluation

open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
local instance coordinateMomentDualNormedGroup {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] :
    NormedAddCommGroup (A →L[ℝ] ℝ) := inferInstance
local instance coordinateMomentDualNormedSpace {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] :
    NormedSpace ℝ (A →L[ℝ] ℝ) := inferInstance

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorCoordinate_slice_probability {V : E → ℝ → ℝ}
    (H : RegularVectorCoordinateFamily V) (t : E) :
    IsProbabilityMeasure (realDensityLaw (fun x => Real.exp (-V t x))) := by
  obtain ⟨a, B, C, D, m, l, ha, hb⟩ := H.growth t
  have hp : Continuous (fun x : ℝ => (t, x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (V t) := H.potential_continuous.comp hp
  have hi := potential_negative_exp_integrable (V t) hc ha (fun x => (hb t (by simp) x).1)
  exact realDensityLaw_probability _ hi (fun _ => (Real.exp_pos _).le) (integral_exp_pos hi)

theorem vectorCoordinate_score_memLp_two {V : E → ℝ → ℝ}
    (H : RegularVectorCoordinateFamily V) (t : E) :
    MemLp (H.score t) 2 (realDensityLaw (fun x => Real.exp (-V t x))) := by
  obtain ⟨a, B, C, D, m, l, ha, hb⟩ := H.growth t
  have hp : Continuous (fun x : ℝ => (t, x)) := continuous_const.prodMk continuous_id
  apply potential_vector_polynomial_memLp_two (V t) (H.score t)
    (H.potential_continuous.comp hp) (H.score_continuous.comp hp) ha (abs_nonneg C)
    (fun x => (hb t (by simp) x).1)
  intro x
  exact ((hb t (by simp) x).2.1).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))

theorem vectorCoordinate_hessian_integrable {V : E → ℝ → ℝ}
    (H : RegularVectorCoordinateFamily V) (t : E) :
    Integrable (H.hessian t) (realDensityLaw (fun x => Real.exp (-V t x))) := by
  obtain ⟨a, B, C, D, m, l, ha, hb⟩ := H.growth t
  have hp : Continuous (fun x : ℝ => (t, x)) := continuous_const.prodMk continuous_id
  have hs : Continuous (H.score t) := H.score_continuous.comp hp
  have hcorr : Continuous (fun x => H.hessian t x - (H.score t x).smulRight (H.score t x)) :=
    (H.hessian_continuous.comp hp).sub
      ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous₂.comp₂ hs hs)
  have hi := potential_vector_polynomial_integrable (V t)
    (fun x => H.hessian t x - (H.score t x).smulRight (H.score t x))
    (H.potential_continuous.comp hp) hcorr ha (fun x => (hb t (by simp) x).1)
    (fun x => (hb t (by simp) x).2.2)
  have ht := score_tensor_integrable _ (H.score t) (vectorCoordinate_score_memLp_two H t)
  have hadd := Integrable.add
    (f := fun x => H.hessian t x - (H.score t x).smulRight (H.score t x))
    (g := fun x => (H.score t x).smulRight (H.score t x)) hi ht
  change Integrable (fun x => (H.hessian t x - (H.score t x).smulRight (H.score t x)) +
    (H.score t x).smulRight (H.score t x)) _ at hadd
  simpa only [sub_add_cancel] using hadd

theorem vectorCoordinate_hessian_directional_formula {V : E → ℝ → ℝ}
    (H : RegularVectorCoordinateFamily V) (t v : E) :
    vectorCoordinateHessian H t v v =
      (∫ x, H.hessian t x v v ∂realDensityLaw (fun x => Real.exp (-V t x))) -
      variance (fun x => H.score t x v) (realDensityLaw (fun x => Real.exp (-V t x))) := by
  letI := vectorCoordinate_slice_probability H t
  exact score_covariance_hessian_apply _ (H.score t) (H.hessian t)
    (vectorCoordinate_score_memLp_two H t) (vectorCoordinate_hessian_integrable H t) v

end
end Nonsmooth
