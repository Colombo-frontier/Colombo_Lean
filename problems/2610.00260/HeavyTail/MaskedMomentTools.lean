import HeavyTail.GaussianLowerMoments
import Mathlib.Analysis.MeanInequalitiesPow

/-! Finite-dimensional real-p moment estimates used by the coordinate oracle. -/

open scoped BigOperators NNReal
namespace HeavyTail.MaskedLower
noncomputable section

theorem nonneg_add_rpow_le_twice {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) : (a + b) ^ p ≤ 2 * (a ^ p + b ^ p) := by
  have h : (a + b) ^ p ≤ (2 : ℝ) ^ (p - 1) * (a ^ p + b ^ p) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow (⟨a, ha⟩ : ℝ≥0) (⟨b, hb⟩ : ℝ≥0) hp
  have htwo : (2 : ℝ) ^ (p - 1) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : p - 1 ≤ 1)
  exact h.trans (mul_le_mul_of_nonneg_right htwo (by positivity))

theorem norm_sub_rpow_le_twice {E : Type*} [NormedAddCommGroup E]
    (x y : E) {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ‖x - y‖ ^ p ≤ 2 * (‖x‖ ^ p + ‖y‖ ^ p) :=
  (Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le x y) (by linarith)).trans
    (nonneg_add_rpow_le_twice (norm_nonneg x) (norm_nonneg y) hp hp2)

theorem coordinate_lp_sum_bound {k : ℕ} (hk : 0 < k) {p : ℝ}
    (hp : 0 ≤ p) (hp2 : p ≤ 2) (w : HardSpace k) (hw : ‖w‖ = 1) :
    (∑ j : Fin k, |w j| ^ p) ≤ (k : ℝ) * (1 / Real.sqrt k) ^ p := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hweights : ∑ _j : Fin k, (1 / (k : ℝ)) = 1 := by simp [hkR.ne']
  have h := (Real.concaveOn_rpow (by linarith : 0 ≤ p / 2) (by linarith : p / 2 ≤ 1)).le_map_sum
    (t := Finset.univ) (w := fun _j : Fin k => 1 / (k : ℝ)) (p := fun j : Fin k => (w j) ^ 2)
    (fun _ _ => by positivity) hweights (fun j _ => sq_nonneg (w j))
  simp only [smul_eq_mul, gaussianLower_square_rpow, ← Finset.mul_sum] at h
  rw [← hardSpace_norm_sq, hw, one_pow, mul_one] at h
  have hsquare : (1 / Real.sqrt (k : ℝ)) ^ 2 = 1 / (k : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hkR.le]
  have hpower : (1 / (k : ℝ)) ^ (p / 2) = (1 / Real.sqrt (k : ℝ)) ^ p := by
    rw [← hsquare, gaussianLower_square_rpow, abs_of_nonneg (by positivity)]
  rw [hpower] at h
  have hm := mul_le_mul_of_nonneg_left h hkR.le
  simpa only [← mul_assoc, mul_one_div_cancel hkR.ne', one_mul] using hm

end
end HeavyTail.MaskedLower
