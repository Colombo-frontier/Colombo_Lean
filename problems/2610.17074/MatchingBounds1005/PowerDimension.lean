import MatchingBounds1005.AnalyticFamily

/-! The manuscript's concrete copy count K=ceil(ε^(-14)) and resulting
dimension O_p(ε^(-47/3)), for the actual copied chain. -/
noncomputable section

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration

def powerCopies (t : ℝ) : ℕ := Nat.ceil (1 / t ^ 42)

theorem powerCopies_lower {t : ℝ} : 1 / t ^ 42 ≤ (powerCopies t : ℝ) := Nat.le_ceil _

theorem powerCopies_upper {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ((powerCopies t + 1 : ℕ) : ℝ) ≤ 3 / t ^ 42 := by
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 1 / t ^ 42 by positivity)
  change (powerCopies t : ℝ) < 1 / t ^ 42 + 1 at hceil
  have hp : t ^ 42 ≤ 1 := pow_le_one₀ ht.le ht1
  have hone : (1 : ℝ) ≤ 1 / t ^ 42 := (le_div_iff₀ (pow_pos ht 42)).mpr (by linarith)
  push_cast
  rw [show (3 : ℝ) / t ^ 42 = 3 * (1 / t ^ 42) by ring]
  linarith

theorem parameterThreshold_le_one (p : ℕ) : parameterThreshold p ≤ 1 :=
  (min_le_right _ _).trans (RadialHigher.accuracyThreshold_le_one p)

theorem power_dimension_upper (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ parameterThreshold p) :
    (dimension p t (powerCopies t) : ℝ) ≤ 3 * horizonUpper p / t ^ 47 := by
  have hd := (dimension_bounds p t ht hsmall (powerCopies t)).2
  rw [cube_rate ht] at hd
  have hK := powerCopies_upper ht (hsmall.trans (parameterThreshold_le_one p))
  calc
    _ ≤ ((powerCopies t + 1 : ℕ) : ℝ) * (horizonUpper p * (1 / t ^ 5)) := hd
    _ ≤ (3 / t ^ 42) * (horizonUpper p * (1 / t ^ 5)) :=
      mul_le_mul_of_nonneg_right hK (by have h := horizonUpper_pos p; positivity)
    _ = _ := by rw [mul_one_div, div_mul_div_comm, ← pow_add]

theorem cube_dimension_rate {t : ℝ} (ht : 0 < t) :
    (t ^ 3) ^ (-(47 : ℝ) / 3) = 1 / t ^ 47 := by
  rw [← Real.rpow_natCast_mul ht.le]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_neg ht.le, show t ^ (47 : ℝ) = t ^ (47 : ℕ) from Real.rpow_natCast t 47]
  simp only [one_div]

theorem accuracy_dimension_upper (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold p) :
    (dimension p (accuracyParameter ε) (powerCopies (accuracyParameter ε)) : ℝ) ≤
      (3 * horizonUpper p) * ε ^ (-(47 : ℝ) / 3) := by
  obtain ⟨ht, htδ, he⟩ := accuracy_parameters p hε hsmall
  have hd := power_dimension_upper p (accuracyParameter ε) ht htδ
  have hr := cube_dimension_rate ht
  rw [he] at hr
  rw [hr, mul_one_div]
  exact hd

theorem accuracy_copy_count (ε : ℝ) (hε : 0 < ε) :
    powerCopies (accuracyParameter ε) = Nat.ceil (ε ^ (-(14 : ℝ))) := by
  unfold powerCopies
  congr 1
  have ht := accuracyParameter_pos hε
  conv => rhs; rw [← accuracyParameter_cube hε.le, ← Real.rpow_natCast_mul ht.le]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_neg ht.le,
    show accuracyParameter ε ^ (42 : ℝ) = accuracyParameter ε ^ (42 : ℕ) from Real.rpow_natCast _ 42]
  simp only [one_div]

end MatchingBounds1005.AnalyticFamily
