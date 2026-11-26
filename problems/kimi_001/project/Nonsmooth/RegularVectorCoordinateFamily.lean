import Nonsmooth.VectorPotentialContinuity

open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance regularCoordinateDualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance regularCoordinateDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

/-- Primitive parameter derivatives and local Gaussian domination for
integrating one real coordinate. Marginal derivatives are consequences. -/
structure RegularVectorCoordinateFamily (V : E → ℝ → ℝ) where
  score : E → ℝ → E →L[ℝ] ℝ
  hessian : E → ℝ → E →L[ℝ] E →L[ℝ] ℝ
  potential_continuous : Continuous (Function.uncurry V)
  score_continuous : Continuous (Function.uncurry score)
  hessian_continuous : Continuous (Function.uncurry hessian)
  potential_derivative : ∀ r x, HasFDerivAt (fun r => V r x) (score r x) r
  score_derivative : ∀ r x, HasFDerivAt (fun r => score r x) (hessian r x) r
  growth : ∀ t, ∃ (a B C D : ℝ) (m l : ℕ), 0 < a ∧ ∀ r ∈ Metric.ball t 1, ∀ x,
    a * x ^ 2 - B ≤ V r x ∧ ‖score r x‖ ≤ C * (1 + |x| ^ m) ∧
      ‖hessian r x - (score r x).smulRight (score r x)‖ ≤ D * (1 + |x| ^ l)

def vectorCoordinateScore {V : E → ℝ → ℝ} (H : RegularVectorCoordinateFamily V) (t : E) : E →L[ℝ] ℝ :=
  ∫ x : ℝ, H.score t x ∂realDensityLaw (fun x => Real.exp (-V t x))

def vectorCoordinateHessian {V : E → ℝ → ℝ} (H : RegularVectorCoordinateFamily V) (t : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (∫ x : ℝ, H.hessian t x - (H.score t x).smulRight (H.score t x)
    ∂realDensityLaw (fun x => Real.exp (-V t x))) +
    (vectorCoordinateScore H t).smulRight (vectorCoordinateScore H t)

theorem vectorCoordinate_marginal_hasFDerivAt {V : E → ℝ → ℝ}
    (H : RegularVectorCoordinateFamily V) (t : E) :
    HasFDerivAt (fun r => -Real.log (∫ x : ℝ, Real.exp (-V r x))) (vectorCoordinateScore H t) t := by
  obtain ⟨a, B, C, D, m, l, ha, hb⟩ := H.growth t
  exact potential_negative_log_hasFDerivAt V H.score t H.potential_continuous H.score_continuous
    H.potential_derivative ha (fun r hr x => (hb r hr x).1) (fun r hr x => (hb r hr x).2.1)

theorem vectorCoordinate_score_hasFDerivAt {V : E → ℝ → ℝ}
    (H : RegularVectorCoordinateFamily V) (t : E) :
    HasFDerivAt (vectorCoordinateScore H) (vectorCoordinateHessian H t) t := by
  obtain ⟨a, B, C, D, m, l, ha, hb⟩ := H.growth t
  exact potential_vector_expectation_hasFDerivAt V H.score H.score H.hessian t
    H.potential_continuous H.score_continuous H.score_continuous H.hessian_continuous
    H.potential_derivative H.score_derivative ha (fun r hr x => (hb r hr x).1)
    (fun x => (hb t (by simp) x).2.1) (fun r hr x => (hb r hr x).2.2)
    (fun r hr x => (hb r hr x).2.1)

theorem vectorCoordinate_hessian_continuous {V : E → ℝ → ℝ}
    (H : RegularVectorCoordinateFamily V) : Continuous (vectorCoordinateHessian H) := by
  have hF : Continuous (Function.uncurry (fun r x =>
      H.hessian r x - (H.score r x).smulRight (H.score r x))) :=
    H.hessian_continuous.sub ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous₂.comp₂
      H.score_continuous H.score_continuous)
  have hI : Continuous (fun r => ∫ x : ℝ, H.hessian r x - (H.score r x).smulRight (H.score r x)
      ∂realDensityLaw (fun x => Real.exp (-V r x))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨a, B, C, D, m, l, ha, hb⟩ := H.growth t
    exact potential_vector_expectation_continuousAt V _ t H.potential_continuous hF ha
      (fun r hr x => (hb r hr x).1) (fun r hr x => (hb r hr x).2.2)
  have hS : Continuous (vectorCoordinateScore H) := continuous_iff_continuousAt.mpr
    (fun t => (vectorCoordinate_score_hasFDerivAt H t).continuousAt)
  exact hI.add ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous₂.comp₂ hS hS)

/-- The actual negative log marginal is C2 in all parameter directions,
including mixed derivatives, under the primitive coordinate-family data. -/
theorem vectorCoordinate_marginal_contDiff_two {V : E → ℝ → ℝ}
    (H : RegularVectorCoordinateFamily V) :
    ContDiff ℝ 2 (fun r => -Real.log (∫ x : ℝ, Real.exp (-V r x))) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  refine ⟨fun t => (vectorCoordinate_marginal_hasFDerivAt H t).differentiableAt, by simp, ?_⟩
  have hd : fderiv ℝ (fun r => -Real.log (∫ x : ℝ, Real.exp (-V r x))) = vectorCoordinateScore H := by
    funext t
    exact (vectorCoordinate_marginal_hasFDerivAt H t).fderiv
  rw [hd, contDiff_one_iff_fderiv]
  refine ⟨fun t => (vectorCoordinate_score_hasFDerivAt H t).differentiableAt, ?_⟩
  have he : fderiv ℝ (vectorCoordinateScore H) = vectorCoordinateHessian H := by
    funext t
    exact (vectorCoordinate_score_hasFDerivAt H t).fderiv
  rw [he]
  exact vectorCoordinate_hessian_continuous H

end
end Nonsmooth
