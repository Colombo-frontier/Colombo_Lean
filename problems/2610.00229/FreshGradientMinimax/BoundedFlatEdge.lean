import FreshGradientMinimax.FlatEdge

/-! The flat Huber edge of E.2. Writing it as a difference of two flat
quadratics gives its genuine derivative at all four interfaces as well. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def boundedFlatEdge (δ b t : ℝ) : ℝ := flatEdge δ t - flatEdge (δ + b) t
def boundedFlatSlope (δ b t : ℝ) : ℝ := flatEdgeSlope δ t - flatEdgeSlope (δ + b) t

theorem boundedFlatEdge_derivative {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (t : ℝ) :
    HasDerivAt (boundedFlatEdge δ b) (boundedFlatSlope δ b t) t :=
  (flatEdge_derivative hδ t).sub (flatEdge_derivative (add_nonneg hδ hb) t)

theorem boundedFlatSlope_clamp {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (t : ℝ) :
    boundedFlatSlope δ b t = max (-b) (min b (flatEdgeSlope δ t)) := by
  by_cases h1 : t ≤ -(δ + b)
  · have h2 : t ≤ -δ := by linarith
    simp only [boundedFlatSlope, flatEdgeSlope, scalarJoin, if_pos h1, if_pos h2]
    rw [min_eq_right (by linarith : t + δ ≤ b), max_eq_left (by linarith : t + δ ≤ -b)]
    ring
  · by_cases h2 : t ≤ -δ
    · have h3 : t ≤ δ + b := by linarith
      simp only [boundedFlatSlope, flatEdgeSlope, scalarJoin, if_neg h1, if_pos h2, if_pos h3, sub_zero]
      rw [min_eq_right (by linarith : t + δ ≤ b), max_eq_right (by linarith : -b ≤ t + δ)]
    · by_cases h3 : t ≤ δ
      · have h4 : t ≤ δ + b := by linarith
        simp only [boundedFlatSlope, flatEdgeSlope, scalarJoin, if_neg h1, if_neg h2,
          if_pos h3, if_pos h4, sub_self]
        rw [min_eq_right hb, max_eq_right (neg_nonpos.mpr hb)]
      · by_cases h4 : t ≤ δ + b
        · simp only [boundedFlatSlope, flatEdgeSlope, scalarJoin, if_neg h1, if_neg h2,
            if_neg h3, if_pos h4, sub_zero]
          rw [min_eq_right (by linarith : t - δ ≤ b), max_eq_right (by linarith : -b ≤ t - δ)]
        · simp only [boundedFlatSlope, flatEdgeSlope, scalarJoin, if_neg h1, if_neg h2,
            if_neg h3, if_neg h4]
          rw [min_eq_left (by linarith : b ≤ t - δ), max_eq_right (by linarith : -b ≤ b)]
          ring

theorem boundedFlatSlope_lipschitz {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) :
    LipschitzWith 1 (boundedFlatSlope δ b) := by
  simpa only [← boundedFlatSlope_clamp hδ hb] using
    ((flatEdgeSlope_lipschitz hδ).const_min b).const_max (-b)

theorem boundedFlatSlope_monotone {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) :
    Monotone (boundedFlatSlope δ b) := by
  intro x y hxy
  simp only [boundedFlatSlope_clamp hδ hb]
  exact max_le_max_left _ (min_le_min_left _ (flatEdgeSlope_monotone hδ hxy))

theorem boundedFlatEdge_contDiff {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) :
    ContDiff ℝ 1 (boundedFlatEdge δ b) :=
  (flatEdge_contDiff hδ).sub (flatEdge_contDiff (add_nonneg hδ hb))

theorem boundedFlatEdge_convex {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) :
    ConvexOn ℝ Set.univ (boundedFlatEdge δ b) := by
  apply Monotone.convexOn_univ_of_deriv (fun t => (boundedFlatEdge_derivative hδ hb t).differentiableAt)
  rw [deriv_eq (boundedFlatEdge_derivative hδ hb)]
  exact boundedFlatSlope_monotone hδ hb

theorem boundedFlatSlope_bound {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (t : ℝ) :
    |boundedFlatSlope δ b t| ≤ b := by
  rw [boundedFlatSlope_clamp hδ hb, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem boundedFlatEdge_flat {δ b t : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (ht : |t| ≤ δ) :
    boundedFlatEdge δ b t = 0 := by
  rw [boundedFlatEdge, flatEdge_flat hδ ht,
    flatEdge_flat (add_nonneg hδ hb) (by linarith), sub_self]

theorem boundedFlatSlope_flat {δ b t : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (ht : |t| ≤ δ) :
    boundedFlatSlope δ b t = 0 := by
  rw [boundedFlatSlope, flatEdgeSlope_flat hδ ht,
    flatEdgeSlope_flat (add_nonneg hδ hb) (by linarith), sub_self]

theorem boundedFlatEdge_core {δ b t : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (ht : |t| ≤ δ + b) :
    boundedFlatEdge δ b t = flatEdge δ t := by
  rw [boundedFlatEdge, flatEdge_flat (add_nonneg hδ hb) ht, sub_zero]

theorem boundedFlatSlope_core {δ b t : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (ht : |t| ≤ δ + b) :
    boundedFlatSlope δ b t = flatEdgeSlope δ t := by
  rw [boundedFlatSlope, flatEdgeSlope_flat (add_nonneg hδ hb) ht, sub_zero]

theorem boundedFlatEdge_outer {δ b t : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (ht : δ + b ≤ |t|) :
    boundedFlatEdge δ b t = b * (|t| - δ) - b ^ 2 / 2 := by
  rw [boundedFlatEdge, flatEdge_formula hδ, flatEdge_formula (add_nonneg hδ hb),
    max_eq_left (by linarith : 0 ≤ |t| - δ), max_eq_left (by linarith : 0 ≤ |t| - (δ + b))]
  ring

theorem boundedFlatEdge_bounds {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (t : ℝ) :
    0 ≤ boundedFlatEdge δ b t ∧ boundedFlatEdge δ b t ≤ t ^ 2 / 2 := by
  have hupper : boundedFlatEdge δ b t ≤ flatEdge δ t := by
    unfold boundedFlatEdge
    exact sub_le_self _ (flatEdge_bounds (add_nonneg hδ hb) t).1
  refine ⟨?_, hupper.trans (flatEdge_bounds hδ t).2⟩
  by_cases ht : |t| ≤ δ + b
  · rw [boundedFlatEdge_core hδ hb ht]
    exact (flatEdge_bounds hδ t).1
  · rw [boundedFlatEdge_outer hδ hb (le_of_not_ge ht)]
    have h := mul_le_mul_of_nonneg_left (show b ≤ |t| - δ by linarith) hb
    nlinarith only [h, sq_nonneg b]

theorem boundedFlatSlope_perturbation {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (t : ℝ) :
    |boundedFlatSlope δ b t - boundedFlatSlope 0 b t| ≤ δ := by
  have hclip : LipschitzWith 1 (fun x : ℝ => max (-b) (min b x)) :=
    (LipschitzWith.id.const_min b).const_max (-b)
  have h := hclip.dist_le_mul (flatEdgeSlope δ t) (flatEdgeSlope 0 t)
  have hz : flatEdgeSlope 0 t = t := by
    have h0 := flatEdgeSlope_perturbation (le_refl (0 : ℝ)) t
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, hz] at h
  rw [boundedFlatSlope_clamp hδ hb, boundedFlatSlope_clamp (le_refl 0) hb, hz]
  exact h.trans (flatEdgeSlope_perturbation hδ t)

theorem boundedFlatEdge_zero_core {b t : ℝ} (hb : 0 ≤ b) (ht : |t| ≤ b) :
    boundedFlatEdge 0 b t = t ^ 2 / 2 := by
  rw [boundedFlatEdge_core (le_refl 0) hb (by simpa only [zero_add] using ht),
    flatEdge_formula (le_refl 0), sub_zero, max_eq_left (abs_nonneg _), sq_abs]

theorem boundedFlatSlope_zero_core {b t : ℝ} (hb : 0 ≤ b) (ht : |t| ≤ b) :
    boundedFlatSlope 0 b t = t := by
  rw [boundedFlatSlope_core (le_refl 0) hb (by simpa only [zero_add] using ht)]
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (flatEdgeSlope_perturbation (le_refl 0) t))

end FreshGradientMinimax
