import NCConcave16991.LocalizationStep
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Concrete density-based primitives for the Section D cone construction

The density is an explicit smoothed interval of height two. Unlike simply
reusing Appendix E's derivative bound eight, this construction proves the
source's required density bound two and support strictly inside `(0,1)`.
-/

namespace NCConcave16991.ConePrimitives

open LocalizationScalar LocalizationStep Set MeasureTheory
open scoped ContDiff Topology

noncomputable def softPositive (t : ℝ) : ℝ := t + 1 - radialLength 1 (t + 1)

theorem softPositive_contDiff : ContDiff ℝ ∞ softPositive := by
  unfold softPositive
  exact (contDiff_id.add contDiff_const).sub
    ((radialLength_contDiff 1).comp (contDiff_id.add contDiff_const))

theorem softPositive_hasDerivAt (t : ℝ) : HasDerivAt softPositive (Real.smoothTransition t) t := by
  have hh := ((hasDerivAt_id t).add_const 1).sub
    ((radialLength_hasDerivAt 1 (t + 1)).comp t ((hasDerivAt_id t).add_const 1))
  change HasDerivAt softPositive _ t at hh
  refine hh.congr_deriv ?_
  simp [radialSpeed]

theorem softPositive_zero {t : ℝ} (ht : t ≤ 0) : softPositive t = 0 := by
  unfold softPositive
  rw [radialLength_identity (by norm_num : (0 : ℝ) < 1) (by linarith)]
  ring

theorem softPositive_linear {t : ℝ} (ht : 1 ≤ t) : softPositive t = t - 1 / 2 := by
  unfold softPositive
  rw [radialLength_plateau (by norm_num : (0 : ℝ) < 1) (by linarith)]
  ring

/-- An explicit fixed C∞ density, bounded by two, as specified in D.1. -/
noncomputable def density (t : ℝ) : ℝ :=
  2 * (Real.smoothTransition (8 * t - 2) - Real.smoothTransition (8 * t - 6))

noncomputable def omega (t : ℝ) : ℝ :=
  (softPositive (8 * t - 2) - softPositive (8 * t - 6)) / 4

theorem omega_contDiff : ContDiff ℝ ∞ omega := by
  unfold omega
  exact ((softPositive_contDiff.comp (by fun_prop)).sub
    (softPositive_contDiff.comp (by fun_prop))).div_const 4

theorem density_contDiff : ContDiff ℝ ∞ density := by
  unfold density
  exact contDiff_const.mul ((Real.smoothTransition.contDiff.comp (by fun_prop)).sub
    (Real.smoothTransition.contDiff.comp (by fun_prop)))

theorem omega_hasDerivAt (t : ℝ) : HasDerivAt omega (density t) t := by
  have hh := (((softPositive_hasDerivAt (8 * t - 2)).comp t
    (((hasDerivAt_id t).const_mul 8).sub_const 2)).sub
    ((softPositive_hasDerivAt (8 * t - 6)).comp t
      (((hasDerivAt_id t).const_mul 8).sub_const 6))).div_const 4
  change HasDerivAt omega _ t at hh
  refine hh.congr_deriv ?_
  dsimp [density]
  ring

theorem density_nonneg (t : ℝ) : 0 ≤ density t := by
  unfold density
  have hh := Real.smoothTransition.monotone (show 8 * t - 6 ≤ 8 * t - 2 by linarith)
  linarith

theorem density_le_two (t : ℝ) : density t ≤ 2 := by
  unfold density
  linarith [Real.smoothTransition.le_one (8 * t - 2), Real.smoothTransition.nonneg (8 * t - 6)]

theorem omega_monotone : Monotone omega := by
  apply monotone_of_deriv_nonneg (fun t => (omega_hasDerivAt t).differentiableAt)
  intro t
  rw [(omega_hasDerivAt t).deriv]
  exact density_nonneg t

theorem omega_zero {t : ℝ} (ht : t ≤ 1 / 4) : omega t = 0 := by
  unfold omega
  rw [softPositive_zero (by linarith : 8 * t - 2 ≤ 0),
    softPositive_zero (by linarith : 8 * t - 6 ≤ 0)]
  ring

theorem omega_one {t : ℝ} (ht : 7 / 8 ≤ t) : omega t = 1 := by
  unfold omega
  rw [softPositive_linear (by linarith : 1 ≤ 8 * t - 2),
    softPositive_linear (by linarith : 1 ≤ 8 * t - 6)]
  ring

theorem omega_nonneg (t : ℝ) : 0 ≤ omega t := by
  by_cases ht : t ≤ 1 / 4
  · rw [omega_zero ht]
  · have hh := omega_monotone (le_of_not_ge ht)
    rw [omega_zero (le_refl (1 / 4 : ℝ))] at hh
    exact hh

theorem omega_le_one (t : ℝ) : omega t ≤ 1 := by
  by_cases ht : 7 / 8 ≤ t
  · rw [omega_one ht]
  · have hh := omega_monotone (le_of_not_ge ht)
    rw [omega_one (le_refl (7 / 8 : ℝ))] at hh
    exact hh

theorem density_zero_left {t : ℝ} (ht : t ≤ 1 / 4) : density t = 0 := by
  unfold density
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 8 * t - 2 ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : 8 * t - 6 ≤ 0)]
  ring

theorem density_zero_right {t : ℝ} (ht : 7 / 8 ≤ t) : density t = 0 := by
  unfold density
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 8 * t - 2),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 8 * t - 6)]
  ring

theorem density_support : Function.support density ⊆ Ioo (0 : ℝ) 1 := by
  intro t ht
  have hl : 1 / 4 < t := by
    by_contra hh
    exact ht (density_zero_left (le_of_not_gt hh))
  have hr : t < 7 / 8 := by
    by_contra hh
    exact ht (density_zero_right (le_of_not_gt hh))
  constructor <;> linarith

theorem density_integral_one : (∫ t in (0 : ℝ)..1, density t) = 1 := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => omega_hasDerivAt t) ((density_contDiff.continuous).intervalIntegrable 0 1)
  rw [omega_one (by norm_num : (7 / 8 : ℝ) ≤ 1), omega_zero (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hh
  simpa using hh

noncomputable def theta (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, omega s

theorem theta_hasDerivAt (t : ℝ) : HasDerivAt theta (omega t) t := by
  have hc := omega_contDiff.continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem theta_deriv : deriv theta = omega := funext fun t => (theta_hasDerivAt t).deriv

theorem theta_contDiff : ContDiff ℝ ∞ theta := by
  rw [contDiff_infty_iff_deriv, theta_deriv]
  exact ⟨fun t => (theta_hasDerivAt t).differentiableAt, omega_contDiff⟩

theorem theta_zero {t : ℝ} (ht : t ≤ 0) : theta t = 0 := by
  unfold theta
  calc
    _ = ∫ _ in (0 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact omega_zero (by have hh := hs.2; rw [max_eq_left ht] at hh; linarith)
    _ = 0 := by simp

theorem theta_nonneg (t : ℝ) : 0 ≤ theta t := by
  by_cases ht : t ≤ 0
  · rw [theta_zero ht]
  · exact intervalIntegral.integral_nonneg_of_forall (le_of_not_ge ht) omega_nonneg

theorem theta_le_positive (t : ℝ) : theta t ≤ max t 0 := by
  by_cases ht : t ≤ 0
  · rw [theta_zero ht, max_eq_right ht]
  · have hh := intervalIntegral.integral_mono (μ := volume) (le_of_not_ge ht)
      (omega_contDiff.continuous.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) omega_le_one
    simpa [theta, max_eq_left (le_of_not_ge ht)] using hh

noncomputable def latch (t : ℝ) : ℝ := omega (4 * t - 1)
noncomputable def exitStep (t : ℝ) : ℝ := omega (t - 1)

theorem latch_nonneg (t : ℝ) : 0 ≤ latch t := omega_nonneg _
theorem latch_le_one (t : ℝ) : latch t ≤ 1 := omega_le_one _
theorem latch_zero {t : ℝ} (ht : t ≤ 1 / 4) : latch t = 0 := omega_zero (by linarith)
theorem latch_one {t : ℝ} (ht : 1 / 2 ≤ t) : latch t = 1 := omega_one (by linarith)
theorem exitStep_zero {t : ℝ} (ht : t ≤ 1) : exitStep t = 0 := omega_zero (by linarith)
theorem exitStep_one {t : ℝ} (ht : 2 ≤ t) : exitStep t = 1 := omega_one (by linarith)

theorem latch_hasDerivAt (t : ℝ) : HasDerivAt latch (4 * density (4 * t - 1)) t := by
  have hh := (omega_hasDerivAt (4 * t - 1)).comp t (((hasDerivAt_id t).const_mul 4).sub_const 1)
  change HasDerivAt latch _ t at hh
  exact hh.congr_deriv (by ring)

theorem exitStep_hasDerivAt (t : ℝ) : HasDerivAt exitStep (density (t - 1)) t := by
  have hh := (omega_hasDerivAt (t - 1)).comp t ((hasDerivAt_id t).sub_const 1)
  change HasDerivAt exitStep _ t at hh
  exact hh.congr_deriv (by ring)

theorem latch_deriv_bounds (t : ℝ) : 0 ≤ deriv latch t ∧ deriv latch t ≤ 8 := by
  rw [(latch_hasDerivAt t).deriv]
  have hh := density_nonneg (4 * t - 1)
  have hh2 := density_le_two (4 * t - 1)
  constructor <;> linarith

theorem exitStep_deriv_bounds (t : ℝ) : 0 ≤ deriv exitStep t ∧ deriv exitStep t ≤ 2 := by
  rw [(exitStep_hasDerivAt t).deriv]
  exact ⟨density_nonneg _, density_le_two _⟩

end NCConcave16991.ConePrimitives
