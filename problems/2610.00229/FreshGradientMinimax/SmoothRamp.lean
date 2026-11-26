import FreshGradientMinimax.Basic
import FreshGradientMinimax.ScalarJoin
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! The piecewise quadratic smoothing χ from Appendix A.1, including both
joins, monotone slope, convexity, and a globally Lipschitz derivative. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def smoothRamp (η t : ℝ) : ℝ := scalarJoin 0 (fun _ => 0)
  (scalarJoin η (fun x => x ^ 2 / (2 * η)) (fun x => x - η / 2)) t

def smoothRampSlope (η t : ℝ) : ℝ := scalarJoin 0 (fun _ => 0)
  (scalarJoin η (fun x => x / η) (fun _ => 1)) t

theorem smoothRamp_derivative {η : ℝ} (hη : 0 < η) (t : ℝ) :
    HasDerivAt (smoothRamp η) (smoothRampSlope η t) t := by
  apply scalarJoin_hasDerivAt
  · exact fun x => hasDerivAt_const x 0
  · intro x
    apply scalarJoin_hasDerivAt
    · intro y
      convert ((hasDerivAt_id y).pow 2).div_const (2 * η) using 1;
        simp; field_simp; ring
    · exact fun y => (hasDerivAt_id y).sub_const (η / 2)
    · field_simp; ring
    · exact div_self hη.ne'
  · simp [scalarJoin, hη.le]
  · simp [scalarJoin, hη.le]

theorem smoothRampSlope_clamp {η : ℝ} (hη : 0 < η) (t : ℝ) :
    smoothRampSlope η t = min 1 (max 0 (t / η)) := by
  by_cases ht : t ≤ 0
  · simp [smoothRampSlope, scalarJoin, ht, max_eq_left (div_nonpos_of_nonpos_of_nonneg ht hη.le)]
  · have ht0 : 0 ≤ t / η := div_nonneg (le_of_lt (lt_of_not_ge ht)) hη.le
    by_cases htη : t ≤ η
    · simp [smoothRampSlope, scalarJoin, ht, htη, max_eq_right ht0,
        min_eq_right ((div_le_one hη).mpr htη)]
    · simp [smoothRampSlope, scalarJoin, ht, htη, max_eq_right ht0,
        min_eq_left ((one_le_div hη).mpr (le_of_lt (lt_of_not_ge htη)))]

theorem smoothRampSlope_bounds {η : ℝ} (hη : 0 < η) (t : ℝ) :
    0 ≤ smoothRampSlope η t ∧ smoothRampSlope η t ≤ 1 := by
  rw [smoothRampSlope_clamp hη]
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem smoothRampSlope_monotone {η : ℝ} (hη : 0 < η) : Monotone (smoothRampSlope η) := by
  intro x y hxy
  rw [smoothRampSlope_clamp hη, smoothRampSlope_clamp hη]
  exact min_le_min_left 1 (max_le_max_left 0 (div_le_div_of_nonneg_right hxy hη.le))

theorem smoothRampSlope_lipschitz {η : ℝ} (hη : 0 < η) :
    LipschitzWith ⟨1 / η, by positivity⟩ (smoothRampSlope η) := by
  have hdiv : LipschitzWith ⟨1 / η, by positivity⟩ (fun t : ℝ => t / η) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_mk, ← sub_div, abs_div, abs_of_pos hη]
    exact le_of_eq (by ring)
  simpa only [← smoothRampSlope_clamp hη] using (hdiv.const_max 0).const_min 1

theorem smoothRamp_contDiff {η : ℝ} (hη : 0 < η) : ContDiff ℝ 1 (smoothRamp η) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (smoothRamp_derivative hη t).differentiableAt, ?_⟩
  rw [deriv_eq (smoothRamp_derivative hη)]
  exact (smoothRampSlope_lipschitz hη).continuous

theorem smoothRamp_convex {η : ℝ} (hη : 0 < η) : ConvexOn ℝ Set.univ (smoothRamp η) := by
  apply Monotone.convexOn_univ_of_deriv (fun t => (smoothRamp_derivative hη t).differentiableAt)
  rw [deriv_eq (smoothRamp_derivative hη)]
  exact smoothRampSlope_monotone hη

theorem smoothRamp_zero {η t : ℝ} (ht : t ≤ 0) : smoothRamp η t = 0 := by
  simp [smoothRamp, scalarJoin, ht]

theorem smoothRamp_linear {η t : ℝ} (hη : 0 < η) (ht : η ≤ t) :
    smoothRamp η t = t - η / 2 := by
  have ht0 : ¬ t ≤ 0 := not_le.mpr (hη.trans_le ht)
  by_cases he : t ≤ η
  · have heq := le_antisymm he ht
    subst t
    simp only [smoothRamp, scalarJoin, if_neg ht0, if_pos le_rfl]
    field_simp; ring
  · simp [smoothRamp, scalarJoin, ht0, he]

theorem smoothRamp_nonneg {η : ℝ} (hη : 0 < η) (t : ℝ) : 0 ≤ smoothRamp η t := by
  by_cases ht : t ≤ 0
  · rw [smoothRamp_zero ht]
  · by_cases he : t ≤ η
    · simp only [smoothRamp, scalarJoin, if_neg ht, if_pos he]
      positivity
    · rw [smoothRamp_linear hη (le_of_lt (lt_of_not_ge he))]
      linarith

end FreshGradientMinimax

