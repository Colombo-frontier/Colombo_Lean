import Nonsmooth.C2StrongQuadraticPotential
import Nonsmooth.OrthogonalCoordinateCurvature
import Nonsmooth.VectorCoordinateSymmetry
import Nonsmooth.VectorCoordinateCurvature
import Nonsmooth.VectorCoordinateHessianGrowth
import Nonsmooth.QuadraticEnvelopeClosure

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- One-coordinate closure with all coordinate hypotheses constructed
from the original potential. The curvature constant is unchanged. -/
theorem c2StrongQuadraticPotential_orthogonal_marginal {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ)
    (L : F →ₗᵢ[ℝ] E) (u : E) (hu : ‖u‖ = 1)
    (ho : ∀ t, inner ℝ (L t) u = (0 : ℝ)) :
    C2StrongQuadraticPotential
      (fun t => -Real.log (∫ x : ℝ, Real.exp (-U (L t + x • u)))) ρ := by
  obtain ⟨a, B, ha, hB, hVB⟩ := hU.envelope
  obtain ⟨D, hD, hAB⟩ := hU.hessian_growth
  have hd := contDiff_two_derivative_data U hU.smooth
  let S := fderiv ℝ U
  let A := fderiv ℝ (fderiv ℝ U)
  let Lc := L.toContinuousLinearMap
  let V := coordinatePotential U Lc u
  let C := 6 * B
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hSB (z : E) : ‖S z‖ ≤ C * (1 + ‖z‖) :=
    c2StrongQuadraticPotential_gradient_bound hU (by linarith) ha.le hB.le hVB z
  let R : RegularVectorCoordinateFamily V := orthogonalCoordinateRegularFamily U S A
    hU.smooth.continuous hd.2.2.1 hd.2.2.2 hd.1 hd.2.1 L u hu ho ha hC hD
    (fun z => (hVB z).1) hSB hAB
  let dx : F → ℝ → ℝ := fun t x => S (coordinatePoint Lc u t x) u
  let dxx : F → ℝ → ℝ := fun t x => A (coordinatePoint Lc u t x) u u
  let mixed : F → ℝ → F →L[ℝ] ℝ := fun t x =>
    coordinatePrecompose Lc (A (coordinatePoint Lc u t x) u)
  have hp (t : F) : Continuous (fun x : ℝ => coordinatePoint Lc u t x) :=
    (coordinatePoint_continuous Lc u).comp (continuous_const.prodMk continuous_id)
  have hcd (t : F) : Continuous (dx t) :=
    (hd.2.2.1.comp (hp t)).clm_apply continuous_const
  have hcdd (t : F) : Continuous (dxx t) :=
    ((hd.2.2.2.comp (hp t)).clm_apply continuous_const).clm_apply continuous_const
  have hcm (t : F) : Continuous (mixed t) :=
    (coordinatePrecompose Lc).continuous.comp
      ((hd.2.2.2.comp (hp t)).clm_apply continuous_const)
  have hdV (t : F) (x : ℝ) : HasDerivAt (V t) (dx t x) x :=
    coordinatePotential_hasDerivAt_x U S hd.1 Lc u t x
  have hdd (t : F) (x : ℝ) : HasDerivAt (dx t) (dxx t x) x :=
    coordinateDx_hasDerivAt_x S A hd.2.1 Lc u t x
  have hds (t : F) (x : ℝ) : HasDerivAt (R.score t) (mixed t x) x :=
    coordinateScore_hasDerivAt_x S A hd.2.1 Lc u t x
  have hblock (t : F) (x : ℝ) (v : F) (p : ℝ) :
      ρ * (p ^ 2 + ‖v‖ ^ 2) ≤ dxx t x * p ^ 2 + 2 * mixed t x v * p + R.hessian t x v v :=
    orthogonal_coordinate_hessian_block A L u hu ho ρ hU.hessian_symmetric hU.hessian_lower t x v p
  have hcurv (t v : F) : ρ * ‖v‖ ^ 2 ≤ vectorCoordinateHessian R t v v :=
    vectorCoordinate_marginal_preserves_curvature R t (dx t) (dxx t) (mixed t)
      (hcd t) (hcdd t) (hcm t) (hdV t) (hdd t) (hds t) (by linarith) (hblock t) v
  have hm (t : F) : Monotone (fun x => dx t x - 1 * x) := by
    apply monotone_of_hasDerivAt_nonneg
      (fun x => (hdd t x).sub ((hasDerivAt_id x).const_mul 1))
    intro x
    have hh := hU.hessian_lower (coordinatePoint Lc u t x) u
    rw [hu, one_pow, mul_one] at hh
    change 0 ≤ dxx t x - 1 * 1
    change ρ ≤ dxx t x at hh
    linarith
  have hd0 (t : F) : |dx t 0| ≤ C * (1 + ‖t‖) := by
    have he := (S (L t)).le_opNorm u
    rw [hu, mul_one, Real.norm_eq_abs] at he
    change |S (Lc t + (0 : ℝ) • u) u| ≤ _
    simpa only [zero_smul, add_zero, Lc, LinearIsometry.coe_toContinuousLinearMap, L.norm_map] using he.trans (hSB (L t))
  have hgb := orthogonal_coordinate_global_bounds U S A L u hu ho ha.le hC
    (fun z => (hVB z).1) hSB hAB
  have hRscore (t : F) (x : ℝ) : ‖R.score t x‖ ≤ C * (1 + ‖t‖ + |x|) := (hgb t x).2.1
  have hRH (t : F) (x : ℝ) : ‖R.hessian t x‖ ≤ D * (1 + ‖t‖ ^ 2 + x ^ 2) := by
    change ‖coordinateHessian A L.toContinuousLinearMap u t x‖ ≤ _
    simpa only [sq_abs] using (hgb t x).2.2
  have hVL (t : F) (x : ℝ) : a * (‖t‖ ^ 2 + x ^ 2) - B ≤ V t x := by
    have hb := (hVB (coordinatePoint Lc u t x)).1
    rw [orthogonal_coordinate_norm_sq L u hu ho t x] at hb
    exact hb
  have hVU (t : F) (x : ℝ) : V t x ≤ B * (1 + ‖t‖ ^ 2 + x ^ 2) := by
    have hb := (hVB (coordinatePoint Lc u t x)).2
    rw [orthogonal_coordinate_norm_sq L u hu ho t x] at hb
    change U (coordinatePoint Lc u t x) ≤ _
    simpa only [add_assoc] using hb
  change C2StrongQuadraticPotential (fun t => -Real.log (∫ x : ℝ, Real.exp (-V t x))) ρ
  refine {
    smooth := vectorCoordinate_marginal_contDiff_two R
    hessian_symmetric := ?_
    hessian_lower := ?_
    envelope := ?_
    hessian_growth := ?_
  }
  · intro t v w
    rw [vectorCoordinate_marginal_fderiv_fderiv R]
    exact vectorCoordinate_hessian_symmetric R
      (fun t x v w => coordinateHessian_symmetric A hU.hessian_symmetric Lc u t x v w) t v w
  · intro t v
    rw [vectorCoordinate_marginal_fderiv_fderiv R]
    exact hcurv t v
  · obtain ⟨K, hK, hb⟩ := quadratic_marginal_envelope_exists V
      (fun t => hU.smooth.continuous.comp (hp t)) ha hB hVL hVU
    exact ⟨a, K, ha, hK, hb⟩
  · refine ⟨(D + 6 * C ^ 2) * (3 + 2 * C ^ 2), by positivity, ?_⟩
    intro t
    rw [vectorCoordinate_marginal_fderiv_fderiv R]
    exact vectorCoordinate_hessian_polynomial_growth R dx hcd hdV hm hC hC hD hd0 hRscore hRH t

end
end Nonsmooth
