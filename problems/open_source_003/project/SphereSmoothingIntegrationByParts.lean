import Mathlib

/-! Coordinate integration-by-parts groundwork for the independent spherical
boundary-gradient identity. The proofs use actual Lipschitz FTC. -/
open MeasureTheory Set Metric Function
open scoped NNReal
namespace Task006.SphereSmoothing

/-- A compactly supported Lipschitz real function has zero integral derivative,
including its a.e. derivative at nonsmooth points. -/
theorem integral_deriv_lipschitz_compactSupport_eq_zero {φ : ℝ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hc : HasCompactSupport φ) :
    (∫ x, deriv φ x) = 0 := by
  obtain ⟨R,hR,hsub⟩ := hc.isBounded.subset_ball_lt 0 (0:ℝ)
  have hzero (x : ℝ) (hx : x ∉ ball (0:ℝ) R) : φ x=0 := by
    apply notMem_support.mp
    intro hs
    exact hx (hsub (subset_tsupport φ hs))
  have hd0 (x : ℝ) (hx : x ∉ ball (0:ℝ) R) : deriv φ x=0 :=
    deriv_of_notMem_tsupport (fun hs => hx (hsub hs))
  have hnR : (-R:ℝ) ∉ ball (0:ℝ) R := by simp only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg,
    abs_of_pos hR, lt_self_iff_false, not_false_eq_true]
  have hpR : R ∉ ball (0:ℝ) R := by simp only [mem_ball, dist_zero_right, Real.norm_eq_abs,
    abs_of_pos hR, lt_self_iff_false, not_false_eq_true]
  have hftc := (hφ.lipschitzOnWith (s := uIcc (-R) R)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  rw [hzero R hpR, hzero (-R) hnR, sub_self,
    intervalIntegral.integral_of_le (by linarith : -R ≤ R)] at hftc
  have heq : (∫ x in Ioc (-R) R, deriv φ x) = ∫ x, deriv φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      apply hd0
      intro hball
      have hab : |x| < R := by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hball
      have hxmem : x ∈ Ioc (-R) R := by rw [mem_Ioc]; exact ⟨(abs_lt.mp hab).1,(abs_lt.mp hab).2.le⟩
      exact hx hxmem)
  exact heq.symm.trans hftc

/-- Translation invariance and dominated differentiation prove genuine weak
integration by parts for every compactly supported Lipschitz function. -/
theorem integral_fderiv_lipschitz_compactSupport_eq_zero {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) :
    Integrable (fderiv ℝ f) volume ∧ (∫ z, fderiv ℝ f z) = 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  obtain ⟨R,hR,hsub⟩ := hc.isBounded.subset_ball_lt 0 (0:E)
  let bound : E → ℝ := (closedBall (0:E) (R+1)).indicator (fun _ => (K:ℝ))
  have hbint : Integrable bound volume :=
    (integrableOn_const (μ := (volume : Measure E)) (s := closedBall (0:E) (R+1))
      (C := (K:ℝ)) (hs := measure_closedBall_lt_top.ne)).integrable_indicator measurableSet_closedBall
  have hzero (z : E) (hz : R ≤ ‖z‖) : f z=0 := by
    apply notMem_support.mp
    intro hs
    have hh := hsub (subset_tsupport f hs)
    have hn : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hh
    linarith
  have hm : ∀ y ∈ ball (0:E) 1, AEStronglyMeasurable (fun z => f (y+z)) volume := by
    intro y hy
    exact (hf.continuous.comp (continuous_const.add continuous_id)).measurable.aestronglyMeasurable
  have hi : Integrable (fun z : E => f (0+z)) volume := by
    simpa only [zero_add] using hf.continuous.integrable_of_hasCompactSupport hc
  have hdm : AEStronglyMeasurable (fun z : E => fderiv ℝ f z) volume :=
    (measurable_fderiv ℝ f).aestronglyMeasurable
  have hlip : ∀ᵐ z : E, ∀ y ∈ ball (0:E) 1,
      ‖f (y+z)-f (0+z)‖ ≤ bound z * ‖y-0‖ := by
    apply ae_of_all
    intro z y hy
    dsimp only [bound]
    by_cases hz : z ∈ closedBall (0:E) (R+1)
    · rw [indicator_of_mem hz]
      simpa only [zero_add, sub_zero, add_sub_cancel_right] using hf.norm_sub_le (y+z) z
    · have hnz : R+1 < ‖z‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hz
      have hny : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
      have hyz : R ≤ ‖y+z‖ := by
        have hh : ‖z‖ ≤ ‖y+z‖+‖y‖ := by
          simpa only [add_sub_cancel_left] using norm_sub_le (y+z) y
        linarith
      rw [indicator_of_notMem hz, zero_mul, zero_add,
        hzero (y+z) hyz, hzero z (by linarith), sub_self, norm_zero]
  have hdiff : ∀ᵐ z : E, HasFDerivAt (fun y : E => f (y+z)) (fderiv ℝ f z) 0 := by
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with z hz
    change DifferentiableAt ℝ f z at hz
    have hz0 : DifferentiableAt ℝ f ((0:E)+z) := by simpa only [zero_add] using hz
    convert! hz0.hasFDerivAt.comp 0 ((hasFDerivAt_id (0:E)).add_const z) using 1 <;> simp
  have ht := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (s := ball (0:E) 1) (bound := bound) (Metric.ball_mem_nhds (0:E) zero_lt_one)
    hm hi hdm hlip hbint hdiff
  have heq : (fun y : E => ∫ z : E, f (y+z)) = (fun _ : E => ∫ z : E, f z) := by
    funext y
    exact integral_add_left_eq_self f y
  have hconst : HasFDerivAt (fun y : E => ∫ z : E, f (y+z)) (0 : E →L[ℝ] ℝ) (0:E) := by
    rw [heq]
    exact hasFDerivAt_const _ _
  exact ⟨ht.1, ht.2.unique hconst⟩

end Task006.SphereSmoothing
