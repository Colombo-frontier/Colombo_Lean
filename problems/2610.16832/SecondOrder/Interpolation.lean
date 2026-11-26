import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

namespace SecondOrder

theorem min_le_interpolation {a b ν : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) : min a b ≤ a^(1-ν)*b^ν := by
  have hν' : 0 ≤ 1-ν := by linarith
  have hid (x : ℝ) (hx : 0 ≤ x) : x = x^(1-ν)*x^ν := by
    rw [← Real.rpow_add_of_nonneg hx hν' hν0, sub_add_cancel, Real.rpow_one]
  rcases le_total a b with h|h
  · rw [min_eq_left h]
    calc
      a = a^(1-ν)*a^ν := hid a ha
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha h hν0) (Real.rpow_nonneg ha _)
  · rw [min_eq_right h]
    calc
      b = b^(1-ν)*b^ν := hid b hb
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hb h hν') (Real.rpow_nonneg hb _)

/-- Appendix interpolation lemma, for any normed-space-valued map, hence also
for the population Hessian in its operator norm. -/
theorem holder_of_bounded_lipschitz {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (H : E → F) {M K ν : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hb : ∀ x, ‖H x‖ ≤ M)
    (hl : ∀ x y, ‖H x-H y‖ ≤ K*‖x-y‖) (x y : E) :
    ‖H x-H y‖ ≤ (2*M)^(1-ν)*K^ν*‖x-y‖^ν := by
  have hbound : ‖H x-H y‖ ≤ 2*M := (norm_sub_le _ _).trans (by linarith [hb x,hb y])
  have hmin := le_min hbound (hl x y)
  have hi := min_le_interpolation (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hM)
    (mul_nonneg hK (norm_nonneg (x-y))) hν0 hν1
  apply (hmin.trans hi).trans_eq
  rw [Real.mul_rpow hK (norm_nonneg _)]
  ring

end SecondOrder
