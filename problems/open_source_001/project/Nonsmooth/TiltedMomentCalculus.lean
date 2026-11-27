import Nonsmooth.StrongPotentialMGF

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def densityMoment (μ : Measure ℝ) (U : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, x ^ n * Real.exp (t * x - U x) ∂μ

/-- Moment differentiation for an arbitrary base measure. The explicit integrability
criterion can be verified by compact support, as well as by Gaussian tails. -/
theorem densityMoment_hasDerivAt (μ : Measure ℝ) (U : ℝ → ℝ)
    (hInt : ∀ (t : ℝ) (m : ℕ), Integrable (fun x : ℝ => x ^ m * Real.exp (t * x - U x)) μ)
    (n : ℕ) (t : ℝ) : HasDerivAt (densityMoment μ U n) (densityMoment μ U (n + 1) t) t := by
  let F : ℝ → ℝ → ℝ := fun r x => x ^ n * Real.exp (r * x - U x)
  let F' : ℝ → ℝ → ℝ := fun r x => x ^ (n + 1) * Real.exp (r * x - U x)
  let B : ℝ → ℝ := fun x => ‖F' (t - 1) x‖ + ‖F' (t + 1) x‖
  have hF (r : ℝ) : Integrable (F r) μ := hInt r n
  have hF' (r : ℝ) : Integrable (F' r) μ := hInt r (n + 1)
  have hB : Integrable B μ := (hF' (t - 1)).norm.add (hF' (t + 1)).norm
  have hbound : ∀ᵐ x ∂μ, ∀ r ∈ Metric.ball t 1, ‖F' r x‖ ≤ B x := by
    apply Eventually.of_forall
    intro x r hr
    have hr' : |r - t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
    have he := mul_le_mul_of_nonneg_left (exponential_tilt_local_bound U t r x hr')
      (abs_nonneg (x ^ (n + 1)))
    simpa only [F', B, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_add] using he
  have hder : ∀ᵐ x ∂μ, ∀ r ∈ Metric.ball t 1, HasDerivAt (F · x) (F' r x) r := by
    apply Eventually.of_forall
    intro x r _
    dsimp only [F, F']
    convert! ((((hasDerivAt_id r).mul_const x).sub_const (U x)).exp).const_mul (x ^ n) using 1 <;>
      (try simp only [id_eq, pow_succ]) <;> ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (x₀ := t) (bound := B) (s := Metric.ball t 1) (Metric.ball_mem_nhds t (by norm_num))
    (Eventually.of_forall (fun r => (hF r).aestronglyMeasurable)) (hF t)
    (hF' t).aestronglyMeasurable hbound hB hder).2

theorem log_partition_quadratic_of_derivatives (Z M V : ℝ → ℝ) (c : ℝ)
    (hZD : ∀ t, HasDerivAt (fun r => Real.log (Z r)) (M t) t)
    (hMD : ∀ t, HasDerivAt M (V t) t) (hV : ∀ t, V t ≤ c) (t : ℝ) :
    Real.log (Z t) ≤ Real.log (Z 0) + M 0 * t + c / 2 * t ^ 2 := by
  let F : ℝ → ℝ := fun r => c / 2 * r ^ 2 - Real.log (Z r)
  let S : ℝ → ℝ := fun r => c * r - M r
  have hSder (r : ℝ) : HasDerivAt S (c - V r) r := by
    convert! ((hasDerivAt_id r).const_mul c).sub (hMD r) using 1 <;> simp
  have hSc : Continuous S := continuous_iff_continuousAt.mpr (fun r => (hSder r).continuousAt)
  have hSm : Monotone S := monotone_of_hasDerivAt_nonneg hSder (fun r => sub_nonneg.mpr (hV r))
  have hFder (r : ℝ) : HasDerivAt F (S r) r := by
    convert! (((hasDerivAt_id r).pow 2).const_mul (c / 2)).sub (hZD r) using 1 <;>
      (try dsimp only [F, S, id_eq]) <;> ring
  have h := strong_potential_quadratic_lower F S hSc hFder (ρ := 0)
    (by simpa only [zero_mul, sub_zero] using hSm) t
  dsimp only [F, S] at h
  nlinarith

end
end Nonsmooth
