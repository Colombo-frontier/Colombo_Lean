import MatchingBounds1005.CUPGTaylor
import MatchingBounds1005.CUPGCubicEscape

/-! # Actual symmetric negative-curvature escape with quartic remainders -/
noncomputable section
open scoped ContDiff

namespace MatchingBounds1005.CUPG

theorem cubic_curvature_of_violation {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {L A : ℝ}
    (hlip : ∀ x y, |iteratedDeriv 3 h x - iteratedDeriv 3 h y| ≤ L * |x - y|)
    (hviolation : h 1 - h (-1) - 2 * deriv h (-1) ≤ -A) :
    iteratedDeriv 2 h 0 / 2 - iteratedDeriv 3 h 0 / 6 ≤ -A / 4 + 5 * L / 48 := by
  have he1 := (abs_le.mp (cubic_jet_error hh hlip 1)).1
  have hem1 := (abs_le.mp (cubic_jet_error hh hlip (-1))).2
  have hed := (abs_le.mp (first_jet_error hh hlip (-1))).2
  norm_num at he1 hem1 hed
  unfold cubicJet at he1 hem1
  unfold firstJet at hed
  norm_num at he1 hem1 hed
  linarith

/-- Two symmetric samples escape a first-order convexity violation.
Every smoothness and value input concerns the actual scalar function. -/
theorem normalized_symmetric_escape {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {L A R : ℝ}
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hR : 4 ≤ R)
    (hlip : ∀ x y, |iteratedDeriv 3 h x - iteratedDeriv 3 h y| ≤ L * |x - y|)
    (hviolation : h 1 - h (-1) - 2 * deriv h (-1) ≤ -A)
    (hscale : L * R ^ 2 ≤ A / 2) :
    min (h (-R)) (h R) ≤ max (h (-1)) (h 1) - A * R ^ 2 / 6 := by
  have hR0 : 0 ≤ R := by linarith
  have hR2 : 16 ≤ R ^ 2 := by nlinarith
  have hRdiff : 0 ≤ R ^ 2 - 1 := by linarith
  have hcurv := mul_le_mul_of_nonneg_right (cubic_curvature_of_violation hh hlip hviolation) hRdiff
  have hc := cubic_symmetric_escape (h 0) (deriv h 0)
    (iteratedDeriv 2 h 0 / 2) (iteratedDeriv 3 h 0 / 6) R (by linarith)
  change min (cubicJet h (-R)) (cubicJet h R) ≤
    max (cubicJet h (-1)) (cubicJet h 1) +
      (iteratedDeriv 2 h 0 / 2 - iteratedDeriv 3 h 0 / 6) * (R ^ 2 - 1) at hc
  have hm : max (cubicJet h (-1)) (cubicJet h 1) ≤ max (h (-1)) (h 1) + L / 24 := by
    apply max_le
    · have he := (abs_le.mp (cubic_jet_error hh hlip (-1))).1
      norm_num at he
      linarith [le_max_left (h (-1)) (h 1)]
    · have he := (abs_le.mp (cubic_jet_error hh hlip 1)).1
      norm_num at he
      linarith [le_max_right (h (-1)) (h 1)]
  have hmout : min (h (-R)) (h R) ≤ min (cubicJet h (-R)) (cubicJet h R) + L / 24 * R ^ 4 := by
    have hl := (abs_le.mp (cubic_jet_error hh hlip (-R))).2
    have hr := (abs_le.mp (cubic_jet_error hh hlip R)).2
    rw [abs_neg, abs_of_nonneg hR0] at hl
    rw [abs_of_nonneg hR0] at hr
    by_cases hc' : cubicJet h (-R) ≤ cubicJet h R
    · rw [min_eq_left hc']
      linarith [min_le_left (h (-R)) (h R)]
    · rw [min_eq_right (le_of_not_ge hc')]
      linarith [min_le_right (h (-R)) (h R)]
  have hscaled := mul_le_mul_of_nonneg_right hscale (sq_nonneg R)
  have hAR := mul_le_mul_of_nonneg_left hR2 hA
  have herror : -A / 4 * (R ^ 2 - 1) + 5 * L / 48 * (R ^ 2 - 1) +
      L / 24 * (R ^ 4 + 1) ≤ -A * R ^ 2 / 6 := by
    nlinarith only [hscale, hscaled, hAR, hL, hA]
  nlinarith only [hcurv, hc, hm, hmout, herror]

end MatchingBounds1005.CUPG
