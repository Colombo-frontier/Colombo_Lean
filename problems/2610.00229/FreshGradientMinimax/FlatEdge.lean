import FreshGradientMinimax.Basic
import FreshGradientMinimax.ScalarJoin
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! The exact threshold-flat edge energy used in the hidden path.
All regularity assertions include both interfaces and the zero-threshold case. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax

def flatEdge (δ t : ℝ) : ℝ := scalarJoin (-δ) (fun x => (x + δ) ^ 2 / 2)
  (scalarJoin δ (fun _ => 0) (fun x => (x - δ) ^ 2 / 2)) t

def flatEdgeSlope (δ t : ℝ) : ℝ := scalarJoin (-δ) (fun x => x + δ)
  (scalarJoin δ (fun _ => 0) (fun x => x - δ)) t

theorem flatEdge_derivative {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    HasDerivAt (flatEdge δ) (flatEdgeSlope δ t) t := by
  apply scalarJoin_hasDerivAt
  · intro x
    convert (((hasDerivAt_id x).add_const δ).pow 2).div_const 2 using 1; simp only [id_eq, pow_one, mul_one]; ring
  · intro x
    apply scalarJoin_hasDerivAt
    · exact fun y => hasDerivAt_const y 0
    · intro y
      convert (((hasDerivAt_id y).sub_const δ).pow 2).div_const 2 using 1; simp only [id_eq, pow_one, mul_one]; ring
    · simp
    · simp
  · simp [scalarJoin, show -δ ≤ δ by linarith]
  · simp [scalarJoin, show -δ ≤ δ by linarith]

theorem flatEdge_formula {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    flatEdge δ t = (max (|t| - δ) 0) ^ 2 / 2 := by
  by_cases hl : t ≤ -δ
  · have ht : t ≤ 0 := by linarith
    simp only [flatEdge, scalarJoin, if_pos hl, abs_of_nonpos ht]
    rw [max_eq_left (by linarith : 0 ≤ -t - δ)]
    ring
  · by_cases hr : t ≤ δ
    · have ht : |t| ≤ δ := abs_le.mpr ⟨by linarith, hr⟩
      simp [flatEdge, scalarJoin, hl, hr, max_eq_right (sub_nonpos.mpr ht)]
    · have ht : 0 ≤ t := by linarith
      simp [flatEdge, scalarJoin, hl, hr, abs_of_nonneg ht,
        max_eq_left (by linarith : 0 ≤ t - δ)]

theorem flatEdgeSlope_formula {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    flatEdgeSlope δ t = max (t - δ) (min 0 (t + δ)) := by
  by_cases hl : t ≤ -δ
  · simp [flatEdgeSlope, scalarJoin, hl, min_eq_right (by linarith : t + δ ≤ 0),
      max_eq_right (by linarith : t - δ ≤ t + δ)]
  · by_cases hr : t ≤ δ
    · simp [flatEdgeSlope, scalarJoin, hl, hr, min_eq_left (by linarith : 0 ≤ t + δ),
        max_eq_right (by linarith : t - δ ≤ 0)]
    · simp [flatEdgeSlope, scalarJoin, hl, hr, min_eq_left (by linarith : 0 ≤ t + δ),
        max_eq_left (by linarith : 0 ≤ t - δ)]

theorem flatEdgeSlope_lipschitz {δ : ℝ} (hδ : 0 ≤ δ) : LipschitzWith 1 (flatEdgeSlope δ) := by
  have hl : LipschitzWith 1 (fun t : ℝ => t - δ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq]
  have hr : LipschitzWith 1 (fun t : ℝ => t + δ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq]
  simpa only [max_self, ← flatEdgeSlope_formula hδ] using hl.max (hr.const_min 0)

theorem flatEdgeSlope_monotone {δ : ℝ} (hδ : 0 ≤ δ) : Monotone (flatEdgeSlope δ) := by
  intro x y hxy
  rw [flatEdgeSlope_formula hδ, flatEdgeSlope_formula hδ]
  exact max_le_max (sub_le_sub_right hxy δ) (min_le_min_left 0 (add_le_add_right hxy δ))

theorem flatEdge_contDiff {δ : ℝ} (hδ : 0 ≤ δ) : ContDiff ℝ 1 (flatEdge δ) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (flatEdge_derivative hδ t).differentiableAt, ?_⟩
  rw [deriv_eq (flatEdge_derivative hδ)]
  exact (flatEdgeSlope_lipschitz hδ).continuous

theorem flatEdge_convex {δ : ℝ} (hδ : 0 ≤ δ) : ConvexOn ℝ Set.univ (flatEdge δ) := by
  apply Monotone.convexOn_univ_of_deriv (fun t => (flatEdge_derivative hδ t).differentiableAt)
  rw [deriv_eq (flatEdge_derivative hδ)]
  exact flatEdgeSlope_monotone hδ

theorem flatEdge_flat {δ t : ℝ} (hδ : 0 ≤ δ) (ht : |t| ≤ δ) : flatEdge δ t = 0 := by
  simp [flatEdge_formula hδ, max_eq_right (sub_nonpos.mpr ht)]

theorem flatEdgeSlope_flat {δ t : ℝ} (hδ : 0 ≤ δ) (ht : |t| ≤ δ) : flatEdgeSlope δ t = 0 := by
  obtain ⟨hl, hr⟩ := abs_le.mp ht
  rw [flatEdgeSlope_formula hδ, min_eq_left (by linarith : 0 ≤ t + δ),
    max_eq_right (sub_nonpos.mpr hr)]

theorem flatEdge_bounds {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    0 ≤ flatEdge δ t ∧ flatEdge δ t ≤ t ^ 2 / 2 := by
  rw [flatEdge_formula hδ]
  have h0 : 0 ≤ max (|t| - δ) 0 := le_max_right _ _
  have hu : max (|t| - δ) 0 ≤ |t| := max_le (by linarith) (abs_nonneg _)
  constructor
  · positivity
  · nlinarith [sq_abs t]

theorem flatEdgeSlope_bound {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) : |flatEdgeSlope δ t| ≤ |t| := by
  have h := (flatEdgeSlope_lipschitz hδ).dist_le_mul t 0
  have hz := flatEdgeSlope_flat hδ (by simpa using hδ : |(0 : ℝ)| ≤ δ)
  simpa only [hz, Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] using h

theorem flatEdgeSlope_perturbation {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    |flatEdgeSlope δ t - t| ≤ δ := by
  by_cases hl : t ≤ -δ
  · simp [flatEdgeSlope, scalarJoin, hl, abs_of_nonneg hδ]
  · by_cases hr : t ≤ δ
    · simp only [flatEdgeSlope, scalarJoin, if_neg hl, if_pos hr, zero_sub, abs_neg]
      exact abs_le.mpr ⟨by linarith, hr⟩
    · simp [flatEdgeSlope, scalarJoin, hl, hr, abs_of_nonneg hδ]

theorem flatEdge_even {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) : flatEdge δ (-t) = flatEdge δ t := by
  simp [flatEdge_formula hδ]

end FreshGradientMinimax


