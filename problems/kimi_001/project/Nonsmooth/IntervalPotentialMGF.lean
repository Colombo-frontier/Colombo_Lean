import Nonsmooth.IntervalPotentialMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem intervalPotentialMean_hasDerivAt (U : ℝ → ℝ) (hU : Continuous U)
    {a b : ℝ} (hab : a < b) (t : ℝ) :
    HasDerivAt (intervalPotentialMean U a b)
      (variance (fun x : ℝ => x) (intervalDensityLaw (fun x => Real.exp (t * x - U x)) a b)) t := by
  have hZ := (intervalPotentialMoment_zero_pos U hU hab t).ne'
  have h := (intervalPotentialMoment_hasDerivAt U hU a b 1 t).div
    (intervalPotentialMoment_hasDerivAt U hU a b 0 t) hZ
  convert! h using 1
  rw [intervalPotentialVariance_eq U hU hab t, intervalPotentialMean]
  field_simp <;> ring

theorem intervalLogPartition_hasDerivAt (U : ℝ → ℝ) (hU : Continuous U)
    {a b : ℝ} (hab : a < b) (t : ℝ) :
    HasDerivAt (fun r => Real.log (intervalPotentialMoment U a b 0 r))
      (intervalPotentialMean U a b t) t :=
  (intervalPotentialMoment_hasDerivAt U hU a b 0 t).log
    (intervalPotentialMoment_zero_pos U hU hab t).ne'

theorem interval_potential_tilt_variance (U s : ℝ → ℝ) (hU : Continuous U) (hs : Continuous s)
    {a b ρ : ℝ} (hab : a < b) (hρ : 0 < ρ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt U (s x) x)
    (hmono : MonotoneOn (fun x => s x - ρ * x) (Icc a b)) (t : ℝ) :
    variance (fun x : ℝ => x) (intervalDensityLaw (fun x => Real.exp (t * x - U x)) a b) ≤ ρ⁻¹ := by
  have ht : ∀ x ∈ Icc a b, HasDerivAt (fun y => U y - t * y) (s x - t) x := by
    intro x hx
    convert! (hd x hx).sub ((hasDerivAt_id x).const_mul t) using 1 <;> simp
  have htm : MonotoneOn (fun x => (s x - t) - ρ * x) (Icc a b) := by
    intro x hx y hy hxy
    have h := hmono hx hy hxy
    dsimp only at h ⊢
    linarith
  simpa only [neg_sub] using convex_potential_interval_law_variance hab hρ
    (fun x => U x - t * x) (fun x => s x - t)
    (hU.sub (continuous_const.mul continuous_id)) (hs.sub continuous_const) ht htm

theorem intervalLogPartition_quadratic_upper (U s : ℝ → ℝ) (hU : Continuous U) (hs : Continuous s)
    {a b ρ : ℝ} (hab : a < b) (hρ : 0 < ρ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt U (s x) x)
    (hmono : MonotoneOn (fun x => s x - ρ * x) (Icc a b)) (t : ℝ) :
    Real.log (intervalPotentialMoment U a b 0 t) ≤ Real.log (intervalPotentialMoment U a b 0 0) +
      intervalPotentialMean U a b 0 * t + ρ⁻¹ / 2 * t ^ 2 :=
  log_partition_quadratic_of_derivatives _ _ _ ρ⁻¹
    (intervalLogPartition_hasDerivAt U hU hab) (intervalPotentialMean_hasDerivAt U hU hab)
    (interval_potential_tilt_variance U s hU hs hab hρ hd hmono) t

/-- A sharp centered exponential-moment bound for the actual interval density.
The strong convexity and derivative conditions are needed only on this interval. -/
theorem interval_potential_centered_mgf (U s : ℝ → ℝ) (hU : Continuous U) (hs : Continuous s)
    {a b ρ : ℝ} (hab : a < b) (hρ : 0 < ρ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt U (s x) x)
    (hmono : MonotoneOn (fun x => s x - ρ * x) (Icc a b)) (t : ℝ) :
    let Q := intervalDensityLaw (fun x => Real.exp (-U x)) a b
    (∫ x, Real.exp (t * (x - ∫ y : ℝ, y ∂Q)) ∂Q) ≤ Real.exp (t ^ 2 / (2 * ρ)) := by
  have hwc : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hm : intervalPotentialMean U a b 0 =
      ∫ y : ℝ, y ∂intervalDensityLaw (fun y => Real.exp (-U y)) a b := by
    simpa only [zero_mul, zero_sub] using intervalPotentialMean_eq_integral U hU hab.le 0
  dsimp only
  rw [← hm, intervalDensityLaw_integral hab.le _ hwc (fun x => (Real.exp_pos _).le)]
  have he : (fun x => Real.exp (t * (x - intervalPotentialMean U a b 0)) * Real.exp (-U x)) =
      fun x => Real.exp (-t * intervalPotentialMean U a b 0) * Real.exp (t * x - U x) := by
    funext x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he, intervalIntegral.integral_const_mul]
  have hZt := intervalPotentialMoment_zero_pos U hU hab t
  have hZ0 := intervalPotentialMoment_zero_pos U hU hab 0
  have hlog := intervalLogPartition_quadratic_upper U s hU hs hab hρ hd hmono t
  have ht0 : intervalPotentialMoment U a b 0 t = ∫ x in a..b, Real.exp (t * x - U x) := by
    simp only [intervalPotentialMoment_integral U hab.le, pow_zero, one_mul]
  have h00 : intervalPotentialMoment U a b 0 0 = ∫ x in a..b, Real.exp (-U x) := by
    simp only [intervalPotentialMoment_integral U hab.le, pow_zero, one_mul, zero_mul, zero_sub]
  rw [← ht0, ← h00]
  calc
    _ = Real.exp (Real.log (intervalPotentialMoment U a b 0 t) -
        Real.log (intervalPotentialMoment U a b 0 0) - t * intervalPotentialMean U a b 0) := by
      rw [Real.exp_sub, Real.exp_sub, Real.exp_log hZt, Real.exp_log hZ0, neg_mul, Real.exp_neg]
      ring
    _ ≤ Real.exp (t ^ 2 / (2 * ρ)) := by
      apply Real.exp_le_exp.mpr
      have ha : ρ⁻¹ / 2 * t ^ 2 = t ^ 2 / (2 * ρ) := by ring
      rw [ha] at hlog
      nlinarith

end
end Nonsmooth
