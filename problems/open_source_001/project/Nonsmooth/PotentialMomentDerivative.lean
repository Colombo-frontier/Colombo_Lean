import Nonsmooth.StrongPotentialTilts
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def potentialMoment (U : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, x ^ n * Real.exp (t * x - U x)

theorem exponential_tilt_local_bound (U : ℝ → ℝ) (t r x : ℝ) (hr : |r - t| < 1) :
    Real.exp (r * x - U x) ≤
      Real.exp ((t - 1) * x - U x) + Real.exp ((t + 1) * x - U x) := by
  have ht := abs_lt.mp hr
  rcases le_total 0 x with hx | hx
  · have hm := mul_le_mul_of_nonneg_right (show r ≤ t + 1 by linarith [ht.2]) hx
    have he := Real.exp_le_exp.mpr (sub_le_sub_right hm (U x))
    linarith [Real.exp_pos ((t - 1) * x - U x)]
  · have hm := mul_le_mul_of_nonpos_right (show t - 1 ≤ r by linarith [ht.1]) hx
    have he := Real.exp_le_exp.mpr (sub_le_sub_right hm (U x))
    linarith [Real.exp_pos ((t + 1) * x - U x)]

/-- Differentiating a tilted moment is justified by an explicit two-sided local
integrable envelope; every derivative adds exactly one factor of x. -/
theorem potentialMoment_hasDerivAt (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (n : ℕ) (t : ℝ) :
    HasDerivAt (potentialMoment U n) (potentialMoment U (n + 1) t) t := by
  let F : ℝ → ℝ → ℝ := fun r x => x ^ n * Real.exp (r * x - U x)
  let F' : ℝ → ℝ → ℝ := fun r x => x ^ (n + 1) * Real.exp (r * x - U x)
  let B : ℝ → ℝ := fun x => ‖F' (t - 1) x‖ + ‖F' (t + 1) x‖
  have hF (r : ℝ) : Integrable (F r) := strong_potential_tilt_polynomial_integrable U s hs hρ hd hmono r n
  have hF' (r : ℝ) : Integrable (F' r) :=
    strong_potential_tilt_polynomial_integrable U s hs hρ hd hmono r (n + 1)
  have hB : Integrable B := (hF' (t - 1)).norm.add (hF' (t + 1)).norm
  have hbound : ∀ᵐ x ∂(volume : Measure ℝ), ∀ r ∈ Metric.ball t 1, ‖F' r x‖ ≤ B x := by
    apply Eventually.of_forall
    intro x r hr
    have hr' : |r - t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
    have he := mul_le_mul_of_nonneg_left (exponential_tilt_local_bound U t r x hr')
      (abs_nonneg (x ^ (n + 1)))
    simpa only [F', B, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_add] using he
  have hder : ∀ᵐ x ∂(volume : Measure ℝ), ∀ r ∈ Metric.ball t 1, HasDerivAt (F · x) (F' r x) r := by
    apply Eventually.of_forall
    intro x r _
    dsimp only [F, F']
    convert! ((((hasDerivAt_id r).mul_const x).sub_const (U x)).exp).const_mul (x ^ n) using 1 <;>
      (try simp only [id_eq, pow_succ]) <;> ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (x₀ := t) (bound := B) (Metric.ball_mem_nhds t (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun r => (hF r).aestronglyMeasurable)) (hF t)
    (hF' t).aestronglyMeasurable hbound hB hder).2

end
end Nonsmooth
