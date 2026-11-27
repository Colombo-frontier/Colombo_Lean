import Nonsmooth.PotentialPartitionDerivatives

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem realDensityLaw_integrable (w : ℝ → ℝ) (hwm : Measurable w) (hw : Integrable w)
    (hw0 : ∀ x, 0 ≤ w x) (hZ : 0 < ∫ x, w x) (f : ℝ → ℝ)
    (hfw : Integrable (fun x => f x * w x)) : Integrable f (realDensityLaw w) := by
  have hb : Integrable f (volume.withDensity (fun x => ENNReal.ofReal (w x))) := by
    rw [integrable_withDensity_iff hwm.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hw0 _)] using hfw
  have hm : (volume.withDensity (fun x => ENNReal.ofReal (w x))) univ ≠ 0 := by
    rw [realDensityMeasure_mass w hw hw0]
    exact (ENNReal.ofReal_pos.mpr hZ).ne'
  simpa only [realDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ] using
    hb.smul_measure (ENNReal.inv_ne_top.mpr hm)

theorem potentialLogPartition_quadratic_upper (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) :
    Real.log (potentialMoment U 0 t) ≤ Real.log (potentialMoment U 0 0) +
      potentialTiltMean U 0 * t + ρ⁻¹ / 2 * t ^ 2 := by
  let F : ℝ → ℝ := fun r => ρ⁻¹ / 2 * r ^ 2 - Real.log (potentialMoment U 0 r)
  let S : ℝ → ℝ := fun r => ρ⁻¹ * r - potentialTiltMean U r
  have hSder (r : ℝ) : HasDerivAt S (ρ⁻¹ - variance (fun x : ℝ => x)
      (realDensityLaw (fun x => Real.exp (r * x - U x)))) r := by
    convert! ((hasDerivAt_id r).const_mul ρ⁻¹).sub
      (potentialTiltMean_hasDerivAt U s hs hρ hd hmono r) using 1 <;> simp
  have hSc : Continuous S := continuous_iff_continuousAt.mpr (fun r => (hSder r).continuousAt)
  have hSm : Monotone S := monotone_of_hasDerivAt_nonneg hSder
    (fun r => sub_nonneg.mpr (strong_potential_tilt_law_variance U s hs hρ hd hmono r))
  have hFder (r : ℝ) : HasDerivAt F (S r) r := by
    convert! (((hasDerivAt_id r).pow 2).const_mul (ρ⁻¹ / 2)).sub
      (potentialLogPartition_hasDerivAt U s hs hρ hd hmono r) using 1 <;>
      (try dsimp only [F, S, id_eq]) <;> ring
  have h := strong_potential_quadratic_lower F S hSc hFder (ρ := 0)
    (by simpa only [zero_mul, sub_zero] using hSm) t
  dsimp only [F, S] at h
  nlinarith

theorem strong_potential_centered_exp_integrable (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) :
    Integrable (fun x => Real.exp (t * (x - ∫ y : ℝ, y ∂realDensityLaw (fun y => Real.exp (-U y)))))
      (realDensityLaw (fun x => Real.exp (-U x))) := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hwc : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hw : Integrable (fun x => Real.exp (-U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_polynomial_integrable U s hU hs hρ hd hmono 0
  have ht : Integrable (fun x => Real.exp (t * x - U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_tilt_polynomial_integrable U s hs hρ hd hmono t 0
  apply realDensityLaw_integrable _ hwc.measurable hw (fun x => (Real.exp_pos _).le)
    (integral_exp_pos hw)
  let m := ∫ y : ℝ, y ∂realDensityLaw (fun y => Real.exp (-U y))
  have he : (fun x => Real.exp (t * (x - m)) * Real.exp (-U x)) =
      fun x => Real.exp (-t * m) * Real.exp (t * x - U x) := by
    funext x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact ht.const_mul _

/-- Sharp centered exponential moments for the actual normalized one-dimensional
strongly convex density. This is not a hypothesis about an unidentified posterior. -/
theorem strong_potential_centered_mgf (U s : ℝ → ℝ) (hs : Continuous s)
    {ρ : ℝ} (hρ : 0 < ρ) (hd : ∀ x, HasDerivAt U (s x) x)
    (hmono : Monotone (fun x => s x - ρ * x)) (t : ℝ) :
    (∫ x, Real.exp (t * (x - ∫ y : ℝ, y ∂realDensityLaw (fun y => Real.exp (-U y))))
      ∂realDensityLaw (fun x => Real.exp (-U x))) ≤ Real.exp (t ^ 2 / (2 * ρ)) := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hwc : Continuous (fun x => Real.exp (-U x)) := Real.continuous_exp.comp hU.neg
  have hw : Integrable (fun x => Real.exp (-U x)) := by
    simpa only [pow_zero, one_mul] using strong_potential_polynomial_integrable U s hU hs hρ hd hmono 0
  have hm : potentialTiltMean U 0 = ∫ y : ℝ, y ∂realDensityLaw (fun y => Real.exp (-U y)) := by
    simpa only [zero_mul, zero_sub] using potentialTiltMean_eq_integral U s hs hρ hd hmono 0
  rw [← hm, realDensityLaw_integral _ hwc.measurable hw (fun x => (Real.exp_pos _).le)]
  have he : (fun x => Real.exp (t * (x - potentialTiltMean U 0)) * Real.exp (-U x)) =
      fun x => Real.exp (-t * potentialTiltMean U 0) * Real.exp (t * x - U x) := by
    funext x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he, integral_const_mul]
  have hZt := potentialMoment_zero_pos U s hs hρ hd hmono t
  have hZ0 := potentialMoment_zero_pos U s hs hρ hd hmono 0
  have hlog := potentialLogPartition_quadratic_upper U s hs hρ hd hmono t
  have ht0 : potentialMoment U 0 t = ∫ x, Real.exp (t * x - U x) := by simp only [potentialMoment, pow_zero, one_mul]
  have h00 : potentialMoment U 0 0 = ∫ x, Real.exp (-U x) := by simp only [potentialMoment, pow_zero, one_mul, zero_mul, zero_sub]
  rw [← ht0, ← h00]
  calc
    _ = Real.exp (Real.log (potentialMoment U 0 t) - Real.log (potentialMoment U 0 0) -
        t * potentialTiltMean U 0) := by
      rw [Real.exp_sub, Real.exp_sub, Real.exp_log hZt, Real.exp_log hZ0, neg_mul, Real.exp_neg]
      ring
    _ ≤ Real.exp (t ^ 2 / (2 * ρ)) := by
      apply Real.exp_le_exp.mpr
      have ha : ρ⁻¹ / 2 * t ^ 2 = t ^ 2 / (2 * ρ) := by ring
      rw [ha] at hlog
      nlinarith

end
end Nonsmooth
