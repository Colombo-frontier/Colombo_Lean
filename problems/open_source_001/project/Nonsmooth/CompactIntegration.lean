import Nonsmooth.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

open MeasureTheory Metric Filter Function
open scoped Topology ContDiff
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Translation invariance of volume implies that the integral of the derivative of a compactly
supported continuously differentiable function vanishes. -/
theorem compact_integral_fderiv_eq_zero {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hk : HasCompactSupport f) :
    (∫ z : E, fderiv ℝ f z ∂volume) = 0 := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := (hk.fderiv ℝ).exists_bound_of_continuous hd
  obtain ⟨R, hR⟩ := hk.exists_bound_of_continuousOn continuous_id.continuousOn
  let B : E → ℝ := (closedBall (0 : E) (R + 1)).indicator (fun _ => C)
  have hB : Integrable B (volume : Measure E) := by
    apply IntegrableOn.integrable_indicator
    · exact integrableOn_const measure_closedBall_lt_top.ne
    · exact measurableSet_closedBall
  have hbound : ∀ z : E, ∀ y ∈ ball (0 : E) 1, ‖fderiv ℝ f (z + y)‖ ≤ B z := by
    intro z y hy
    by_cases hz : z ∈ closedBall (0 : E) (R + 1)
    · simpa only [B, Set.indicator_of_mem hz] using hC (z + y)
    · have hout : z + y ∉ tsupport f := by
        intro hin
        have hzin : ‖z‖ ≤ R + 1 := calc
          ‖z‖ = ‖(z + y) - y‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖z + y‖ + ‖y‖ := norm_sub_le _ _
          _ ≤ R + 1 := add_le_add (hR _ hin) (by
            have hh : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
            exact hh.le)
        exact hz (by simpa only [mem_closedBall, dist_zero_right] using hzin)
      simp [fderiv_of_notMem_tsupport ℝ hout, B, hz]
  have hderiv : HasFDerivAt (fun y : E => ∫ z : E, f (z + y) ∂volume)
      (∫ z : E, fderiv ℝ f (z + 0) ∂volume) 0 := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun y z : E => f (z + y))
      (F' := fun y z : E => fderiv ℝ f (z + y)) (bound := B)
      (s := ball (0 : E) 1) (ball_mem_nhds 0 zero_lt_one)
    · exact Eventually.of_forall (fun y => (hf.continuous.comp (continuous_id.add continuous_const)).measurable.aestronglyMeasurable)
    · simpa using hf.continuous.integrable_of_hasCompactSupport hk
    · exact (hd.comp (continuous_id.add continuous_const)).measurable.aestronglyMeasurable
    · exact Eventually.of_forall hbound
    · exact hB
    · exact Eventually.of_forall (fun z y _ => by
        convert! (hf.differentiable_one (z + y)).hasFDerivAt.comp y
          ((hasFDerivAt_id y).const_add z) using 1)
  simp only [integral_add_right_eq_self, add_zero] at hderiv
  exact hderiv.unique (hasFDerivAt_const (∫ z : E, f z ∂volume) (0 : E))

theorem compact_integral_fderiv_apply_eq_zero {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hk : HasCompactSupport f) (v : E) :
    (∫ z : E, fderiv ℝ f z v ∂volume) = 0 := by
  have hi : Integrable (fderiv ℝ f) (volume : Measure E) :=
    (hf.continuous_fderiv (by norm_num)).integrable_of_hasCompactSupport (hk.fderiv ℝ)
  rw [← ContinuousLinearMap.integral_apply hi v, compact_integral_fderiv_eq_zero hf hk]
  rfl

/-- Integration by parts with one compactly supported C1 factor, with all integrability
requirements deduced from compact support rather than supplied as assumptions. -/
theorem compact_integration_by_parts {f g : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hk : HasCompactSupport f) (v : E) :
    (∫ z : E, f z * fderiv ℝ g z v ∂volume) =
      -(∫ z : E, fderiv ℝ f z v * g z ∂volume) := by
  have hfg : ContDiff ℝ 1 (fun z => f z * g z) := hf.mul hg
  have hkfg : HasCompactSupport (fun z => f z * g z) := hk.mul_right
  have hzero := compact_integral_fderiv_apply_eq_zero hfg hkfg v
  have hleft : Integrable (fun z => f z * fderiv ℝ g z v) (volume : Measure E) := by
    have hc : Continuous (fun z => f z * fderiv ℝ g z v) :=
      hf.continuous.mul ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    exact hc.integrable_of_hasCompactSupport hk.mul_right
  have hright : Integrable (fun z => fderiv ℝ f z v * g z) (volume : Measure E) := by
    have hc : Continuous (fun z => fderiv ℝ f z v * g z) :=
      ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hg.continuous
    exact hc.integrable_of_hasCompactSupport (hk.fderiv_apply ℝ v).mul_right
  have hid (z : E) : fderiv ℝ (fun z => f z * g z) z v =
      f z * fderiv ℝ g z v + fderiv ℝ f z v * g z := by
    change fderiv ℝ (f * g) z v = _
    rw [fderiv_mul (hf.differentiable_one z) (hg.differentiable_one z)]
    simp [mul_comm]
  simp_rw [hid] at hzero
  rw [integral_add hleft hright] at hzero
  linarith

end
end Nonsmooth
