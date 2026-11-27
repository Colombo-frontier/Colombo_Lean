import Nonsmooth.VectorCoordinateMoments
import Nonsmooth.StrongCoordinateCovariance

open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A full block Hessian lower bound survives integration of one real
coordinate, for the actual multidimensional marginal Hessian. -/
theorem vectorCoordinate_marginal_preserves_curvature {V : E → ℝ → ℝ}
    (H : RegularVectorCoordinateFamily V) (t : E)
    (dx dxx : ℝ → ℝ) (mixed : ℝ → E →L[ℝ] ℝ)
    (hcDx : Continuous dx) (hcDxx : Continuous dxx) (hcM : Continuous mixed)
    (hdV : ∀ x, HasDerivAt (V t) (dx x) x)
    (hdDx : ∀ x, HasDerivAt dx (dxx x) x)
    (hdS : ∀ x, HasDerivAt (H.score t) (mixed x) x)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hblock : ∀ x v p, ρ * (p ^ 2 + ‖v‖ ^ 2) ≤
      dxx x * p ^ 2 + 2 * mixed x v * p + H.hessian t x v v) (v : E) :
    ρ * ‖v‖ ^ 2 ≤ vectorCoordinateHessian H t v v := by
  rw [vectorCoordinate_hessian_directional_formula H t v]
  have hp : Continuous (fun x : ℝ => (t, x)) := continuous_const.prodMk continuous_id
  have hs : Continuous (H.score t) := H.score_continuous.comp hp
  apply strong_coordinate_covariance_curvature (V t) dx dxx
    (fun x => H.score t x v) (fun x => mixed x v) (fun x => H.hessian t x v v)
    hρ (sq_nonneg _) hcDx hcDxx
    ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp hs)
    ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp hcM) hdV hdDx
  · intro x
    exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt x (hdS x)
  · intro x p q
    have hb := hblock x (q • v) p
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      map_smul, smul_apply, smul_eq_mul] at hb
    nlinarith
  · exact (ContinuousLinearMap.apply ℝ ℝ v).comp_memLp' (vectorCoordinate_score_memLp_two H t)
  · exact Integrable.apply_continuousLinearMap (φ := fun x => H.hessian t x v)
      (Integrable.apply_continuousLinearMap (φ := H.hessian t)
        (vectorCoordinate_hessian_integrable H t) v) v

theorem vectorCoordinate_marginal_fderiv_fderiv {V : E → ℝ → ℝ}
    (H : RegularVectorCoordinateFamily V) (t : E) :
    fderiv ℝ (fderiv ℝ (fun r => -Real.log (∫ x : ℝ, Real.exp (-V r x)))) t =
      vectorCoordinateHessian H t := by
  have hd : fderiv ℝ (fun r => -Real.log (∫ x : ℝ, Real.exp (-V r x))) = vectorCoordinateScore H := by
    funext r
    exact (vectorCoordinate_marginal_hasFDerivAt H r).fderiv
  rw [hd]
  exact (vectorCoordinate_score_hasFDerivAt H t).fderiv

end
end Nonsmooth
