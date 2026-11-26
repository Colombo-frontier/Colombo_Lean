import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import MatchingBounds1005.ScalarTransition

/-! A concrete smooth cutoff and the manuscript's actual scalar primitive.
This module constructs objects, rather than assuming a smooth primitive exists.
-/
namespace MatchingBounds1005.Primitive

open Filter Set
open scoped Topology ContDiff

noncomputable def cutoff (t : ℝ) : ℝ := Real.smoothTransition ((4 - t ^ 2) / 3)

theorem cutoff_smooth : ContDiff ℝ ∞ cutoff :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_id.pow 2)).div_const 3)

theorem cutoff_nonneg (t : ℝ) : 0 ≤ cutoff t := Real.smoothTransition.nonneg _
theorem cutoff_le_one (t : ℝ) : cutoff t ≤ 1 := Real.smoothTransition.le_one _
theorem cutoff_even (t : ℝ) : cutoff (-t) = cutoff t := by simp [cutoff]

theorem cutoff_core {t : ℝ} (ht : |t| ≤ 1) : cutoff t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h := (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1)).2 ht
  simp only [sq_abs, one_pow] at h
  linarith

theorem cutoff_tail {t : ℝ} (ht : 2 ≤ |t|) : cutoff t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg t)).2 ht
  simp only [sq_abs] at h
  linarith

/-- The totalized real division gives W(0)=1 automatically. -/
noncomputable def weight (t : ℝ) : ℝ := cutoff t + (1 - cutoff t) / t ^ 2

theorem weight_core {t : ℝ} (ht : |t| ≤ 1) : weight t = 1 := by
  simp [weight, cutoff_core ht]

theorem weight_tail {t : ℝ} (ht : 2 ≤ |t|) : weight t = 1 / t ^ 2 := by
  simp [weight, cutoff_tail ht]

theorem weight_pos (t : ℝ) : 0 < weight t := by
  by_cases ht : |t| ≤ 1
  · rw [weight_core ht]; norm_num
  · have ht0 : t ≠ 0 := by intro h; simp [h] at ht
    have hs : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
    have hc := cutoff_nonneg t
    have hc1 := cutoff_le_one t
    by_cases hc0 : cutoff t = 0
    · simp only [weight, hc0, sub_zero, zero_add]
      positivity
    · have hpos : 0 < cutoff t := lt_of_le_of_ne hc (Ne.symm hc0)
      exact add_pos_of_pos_of_nonneg hpos (div_nonneg (sub_nonneg.mpr hc1) hs.le)

theorem weight_smooth : ContDiff ℝ ∞ weight := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst t
    apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with y hy
    have hy' : |y| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hy
    exact weight_core hy'.le
  · exact cutoff_smooth.contDiffAt.add
      ((contDiffAt_const.sub cutoff_smooth.contDiffAt).div
        (contDiffAt_id.pow 2) (pow_ne_zero 2 ht))

noncomputable def slope (r u : ℝ) : ℝ := 120 * u ^ 2 * (u - 1) * weight (u / r)

theorem slope_smooth (r : ℝ) : ContDiff ℝ ∞ (slope r) := by
  exact (((contDiff_const.mul (contDiff_id.pow 2)).mul
    (contDiff_id.sub contDiff_const)).mul
    (weight_smooth.comp (contDiff_id.div_const r)))

noncomputable def potential (r u : ℝ) : ℝ := ∫ v in (1 : ℝ)..u, slope r v

theorem potential_hasDerivAt (r u : ℝ) : HasDerivAt (potential r) (slope r u) u := by
  have hc := (slope_smooth r).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 1 u)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem potential_deriv (r : ℝ) : deriv (potential r) = slope r := by
  funext u
  exact (potential_hasDerivAt r u).deriv

theorem potential_smooth (r : ℝ) : ContDiff ℝ ∞ (potential r) := by
  apply contDiff_infty_iff_deriv.mpr
  exact ⟨fun u => (potential_hasDerivAt r u).differentiableAt,
    by rw [potential_deriv]; exact slope_smooth r⟩

theorem potential_one (r : ℝ) : potential r 1 = 0 := by simp [potential]

theorem potential_nonneg (r u : ℝ) : 0 ≤ potential r u := by
  by_cases hu : 1 ≤ u
  · apply intervalIntegral.integral_nonneg hu
    intro v hv
    exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hv.1)) (weight_pos _).le
  · have hu' : u ≤ 1 := le_of_not_ge hu
    have h : 0 ≤ ∫ v in u..(1 : ℝ), -slope r v := by
      apply intervalIntegral.integral_nonneg hu'
      intro v hv
      apply neg_nonneg.mpr
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hv.2))
        (weight_pos _).le
    rw [intervalIntegral.integral_neg] at h
    unfold potential
    rw [intervalIntegral.integral_symm]
    exact h

theorem potential_isMinOn (r : ℝ) : IsMinOn (potential r) Set.univ 1 := by
  intro u _
  rw [potential_one]
  exact potential_nonneg r u

theorem potential_deriv_endpoints (r : ℝ) :
    deriv (potential r) 0 = 0 ∧ deriv (potential r) 1 = 0 := by
  rw [potential_deriv]
  simp [slope]

theorem slope_eq_tapered {r : ℝ} (_hr : 0 < r) (u : ℝ) :
    slope r u = taperedDerivative r cutoff u := by
  by_cases hu : u = 0
  · subst u
    simp [slope, taperedDerivative, cutoff_core (show |(0 : ℝ)| ≤ 1 by norm_num)]
  · unfold slope weight taperedDerivative
    field_simp
    ring

theorem slope_core {r u : ℝ} (hr : 0 < r) (hu : |u| ≤ r) :
    slope r u = 120 * u ^ 2 * (u - 1) := by
  rw [slope_eq_tapered hr]
  exact taperedDerivative_exact_core r hr cutoff (fun _ h => cutoff_core h) u hu

theorem slope_tail {r u : ℝ} (hr : 0 < r) (hu : 2 * r ≤ |u|) :
    slope r u = 120 * r ^ 2 * (u - 1) := by
  have hquot : 2 ≤ |u / r| := by
    rw [abs_div, abs_of_pos hr]
    exact (le_div_iff₀ hr).mpr hu
  have hu0 : u ≠ 0 := by
    intro h
    simp only [h, abs_zero] at hu
    linarith
  unfold slope
  rw [weight_tail hquot]
  field_simp
  ring

theorem quartic_hasDerivAt (u : ℝ) :
    HasDerivAt quarticCore (120 * u ^ 2 * (u - 1)) u := by
  convert ((((hasDerivAt_id u).pow 4).const_mul 30).sub
    (((hasDerivAt_id u).pow 3).const_mul 40)).add_const 10 using 1
  simp [quarticCore]
  ring

theorem potential_core {r u : ℝ} (hr : 1 ≤ r) (hu : |u| ≤ r) :
    potential r u = quarticCore u := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hc : ∀ v ∈ uIcc (1 : ℝ) u, slope r v = 120 * v ^ 2 * (v - 1) := by
    intro v hv
    apply slope_core hrpos
    apply abs_le.mpr
    have h := abs_le.mp hu
    exact ⟨(le_min (by linarith) h.1).trans hv.1,
      hv.2.trans (max_le hr h.2)⟩
  have hint : IntervalIntegrable (slope r) MeasureTheory.volume 1 u :=
    (slope_smooth r).continuous.intervalIntegrable 1 u
  have hd : ∀ v ∈ uIcc (1 : ℝ) u, HasDerivAt quarticCore (slope r v) v := by
    intro v hv
    rw [hc v hv]
    exact quartic_hasDerivAt v
  have hquartic : quarticCore 1 = 0 := by norm_num [quarticCore]
  simpa only [potential, hquartic, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint

theorem potential_zero {r : ℝ} (hr : 1 ≤ r) : potential r 0 = 10 := by
  rw [potential_core hr (by simpa using (zero_le_one.trans hr))]
  norm_num [quarticCore]

theorem slope_radial {r : ℝ} (hr : 1 ≤ r) (u : ℝ) :
    -(405 / 32 : ℝ) ≤ u * slope r u := by
  rw [slope_eq_tapered (lt_of_lt_of_le zero_lt_one hr)]
  exact taperedDerivative_radial r hr cutoff
    (fun t => ⟨cutoff_nonneg t, cutoff_le_one t⟩) (fun _ h => cutoff_core h) u

/-- The actual integral potential satisfies the manuscript's scalar transition,
with no remaining cutoff or derivative assumptions. -/
theorem scalar_transition (r : ℝ) (hr : 1 ≤ r)
    (N : ℕ) (hN : 1 ≤ N) (u : ℕ → ℝ)
    (hu0 : u 0 = 1) (huend : u (N + 1) = 0) (huN : u N < (1 / 10 : ℝ)) :
    (1 / 16 : ℝ) ≤ ∑ i ∈ Finset.Icc 1 N,
      scalarResidual (deriv (potential r)) u i ^ 2 := by
  rw [potential_deriv]
  have heq : slope r = taperedDerivative r cutoff :=
    funext (slope_eq_tapered (lt_of_lt_of_le zero_lt_one hr))
  rw [heq]
  exact tapered_scalar_transition_squared r hr cutoff
    (fun t => ⟨cutoff_nonneg t, cutoff_le_one t⟩) (fun _ h => cutoff_core h)
    N hN u hu0 huend huN

/-- The square-root-of-sum-of-squares (Euclidean norm) form of the source lemma. -/
theorem scalar_transition_norm (r : ℝ) (hr : 1 ≤ r)
    (N : ℕ) (hN : 1 ≤ N) (u : ℕ → ℝ)
    (hu0 : u 0 = 1) (huend : u (N + 1) = 0) (huN : u N < (1 / 10 : ℝ)) :
    (1 / 4 : ℝ) ≤ Real.sqrt (∑ i ∈ Finset.Icc 1 N,
      scalarResidual (deriv (potential r)) u i ^ 2) := by
  have hb := scalar_transition r hr N hN u hu0 huend huN
  have hs : 0 ≤ ∑ i ∈ Finset.Icc 1 N,
      scalarResidual (deriv (potential r)) u i ^ 2 := by positivity
  apply (Real.le_sqrt (by norm_num) hs).mpr
  norm_num
  exact hb

end MatchingBounds1005.Primitive
