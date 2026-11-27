import Nonsmooth.PlaneRotation
import Nonsmooth.CompactIntegration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Metric Filter Function
open scoped Topology InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem interval_integral_square_le {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : Continuous g) : (∫ t in a..b, g t) ^ 2 ≤
      (b - a) * ∫ t in a..b, (g t) ^ 2 := by
  let m := ∫ t in a..b, g t
  let c := m / (b - a)
  have hn : 0 ≤ ∫ t in a..b, (g t - c) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab.le (fun t => sq_nonneg _)
  have he (t : ℝ) : (g t - c) ^ 2 = (g t) ^ 2 - 2 * c * g t + c ^ 2 := by ring
  simp_rw [he] at hn
  rw [intervalIntegral.integral_add (f := fun t => (g t) ^ 2 - 2 * c * g t) (g := fun _ => c ^ 2)
      (((hg.pow 2).sub (continuous_const.mul hg)).intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b),
    intervalIntegral.integral_sub (f := fun t => (g t) ^ 2) (g := fun t => 2 * c * g t) ((hg.pow 2).intervalIntegrable a b)
      ((continuous_const.mul hg).intervalIntegrable a b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hn
  have hc : c * (b - a) = m := by dsimp [c]; field_simp [ne_of_gt (sub_pos.mpr hab)]
  change 0 ≤ (∫ t in a..b, (g t) ^ 2) - 2 * c * m + (b - a) * c ^ 2 at hn
  have hp : 0 < b - a := sub_pos.mpr hab
  have hh := mul_nonneg hp.le hn
  change m ^ 2 ≤ _
  nlinarith [sq_nonneg (c * (b - a) - m)]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem circleArc_continuous (a b : E) : Continuous (circleArc a b) :=
  (Real.continuous_cos.smul continuous_const).add (Real.continuous_sin.smul continuous_const)

theorem circleTangent_continuous (a b : E) : Continuous (circleTangent a b) :=
  (Real.continuous_sin.neg.smul continuous_const).add (Real.continuous_cos.smul continuous_const)

theorem smooth_arc_energy_bound {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (a b : E) (Q : E →L[ℝ] E) :
    (f (Q b) - f (Q a)) ^ 2 ≤ (Real.pi / 2) *
      ∫ t in (0 : ℝ)..(Real.pi / 2),
        (fderiv ℝ f (Q (circleArc a b t)) (Q (circleTangent a b t))) ^ 2 := by
  let g := fun t => fderiv ℝ f (Q (circleArc a b t)) (Q (circleTangent a b t))
  have hg : Continuous g :=
    ((hf.continuous_fderiv (by norm_num)).comp (Q.continuous.comp (circleArc_continuous a b))).clm_apply
      (Q.continuous.comp (circleTangent_continuous a b))
  have hd (t : ℝ) : HasDerivAt (fun s => f (Q (circleArc a b s))) (g t) t :=
    ((hf.differentiable_one _).hasFDerivAt).comp_hasDerivAt t
      (Q.hasFDerivAt.comp_hasDerivAt t (circleArc_hasDerivAt a b t))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hg.intervalIntegrable 0 (Real.pi / 2))
  simp only [circleArc_pi_div_two, circleArc_zero] at hi
  have hb := interval_integral_square_le (by positivity : (0 : ℝ) < Real.pi / 2) hg
  rw [hi, sub_zero] at hb
  simpa only [circleArc_pi_div_two, circleArc_zero] using hb

end
end Nonsmooth
