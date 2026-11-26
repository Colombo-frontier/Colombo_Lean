import LogBudget254

noncomputable section
namespace Paper254

theorem third_rpow_cube (x : ℝ) (hx : 0 ≤ x) : (x^(1/3 : ℝ))^3 = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

theorem two_thirds_rpow_cube (x : ℝ) (hx : 0 ≤ x) : (x^(2/3 : ℝ))^3 = x^2 := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

theorem four_thirds_rpow_cube (x : ℝ) (hx : 0 ≤ x) : (x^(4/3 : ℝ))^3 = x^4 := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

theorem nonneg_le_of_cube_le (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s^3 ≤ t^3) : s ≤ t := by
  by_contra hh
  have hst : t < s := lt_of_not_ge hh
  have hsp : 0 < s := lt_of_le_of_lt ht hst
  have hsum : 0 < s^2+s*t+t^2 := by
    nlinarith [sq_pos_of_pos hsp, mul_nonneg hs ht, sq_nonneg t]
  have hp := mul_pos (sub_pos.mpr hst) hsum
  nlinarith

theorem curvedRate_nonneg (d T : ℕ) (P : ℝ) (hP : 0 ≤ P) : 0 ≤ curvedRate d T P := by
  have hL : 0 ≤ logFactor T := by
    by_cases hz : T = 0
    · subst T
      simp [logFactor]
    · exact le_trans (by norm_num) (logFactor_ge_one T (Nat.pos_of_ne_zero hz))
  unfold curvedRate
  positivity

theorem curvedRate_cube (d T : ℕ) (hT : 0 < T) (P : ℝ) (hP : 0 ≤ P) :
    (curvedRate d T P)^3 = (d : ℝ)*(logFactor T)^4*T*P^2 := by
  unfold curvedRate
  simp only [mul_pow, third_rpow_cube _ (Nat.cast_nonneg _),
    four_thirds_rpow_cube _ (le_trans (by norm_num) (logFactor_ge_one T hT)),
    two_thirds_rpow_cube _ hP]

/-- Balancing at a clipped scale includes P=0 and the lower grid endpoint. -/
theorem clipped_balance_cost (A C P lo root : ℝ)
    (hA : 0 ≤ A) (hC : 0 < C) (hP : 0 ≤ P) (hlo : 0 < lo) (hr : 0 ≤ root)
    (hbal : A*P = C*root^3) :
    A*P/max lo root+C*(max lo root)^2 ≤ 3*C*root^2+2*C*lo^2 := by
  have hm : 0 < max lo root := lt_of_lt_of_le hlo (le_max_left _ _)
  have hmove : A*P/max lo root ≤ C*root^2 := by
    apply (div_le_iff₀ hm).mpr
    rw [hbal]
    have hh := mul_le_mul_of_nonneg_left (le_max_right lo root)
      (mul_nonneg hC.le (sq_nonneg root))
    nlinarith
  have hmax : max lo root ≤ lo+root := max_le (by linarith) (by linarith)
  have hsq : (max lo root)^2 ≤ 2*lo^2+2*root^2 := by
    nlinarith [sq_nonneg (lo-root)]
  have hh := mul_le_mul_of_nonneg_left hsq hC.le
  nlinarith

end Paper254
#print axioms Paper254.curvedRate_cube
#print axioms Paper254.clipped_balance_cost
