import Matvec.InversePower

/-! Parameter choices for any fixed positive random-start constant. -/

namespace Matvec

noncomputable section

def inversePowerLengthFor (ν : ℝ) (d : ℕ) : ℕ :=
  inversePowerLength d + ⌈2 * |Real.log (2 * ν)|⌉₊

theorem inversePowerLengthFor_bounds (ν : ℝ) (hν : 0 < ν) (d : ℕ) (hd : 2 ≤ d) :
    0 < inversePowerLengthFor ν d ∧
    (inversePowerLengthFor ν d : ℝ) <
      4 * Real.log ((d : ℝ) + 2) + 2 * |Real.log (2 * ν)| + 2 ∧
    4 * Real.sqrt (d : ℝ) / (3 * ν) ≤ (2 : ℝ) ^ inversePowerLengthFor ν d := by
  obtain ⟨hq, hqbound, hqpower⟩ := inversePowerLength_bounds d hd
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hceil := Nat.le_ceil (2 * |Real.log (2 * ν)|)
  have hceilbound := Nat.ceil_lt_add_one (show 0 ≤ 2 * |Real.log (2 * ν)| by positivity)
  refine ⟨by unfold inversePowerLengthFor; omega, ?_, ?_⟩
  · unfold inversePowerLengthFor
    push_cast
    linarith
  · have hmul := mul_le_mul_of_nonneg_right hceil (show 0 ≤ Real.log 2 by linarith)
    have hlogbound : -(Real.log (2 * ν)) ≤
        (⌈2 * |Real.log (2 * ν)|⌉₊ : ℝ) * Real.log 2 := by
      have hnonneg := abs_nonneg (Real.log (2 * ν))
      have habs := neg_le_abs (Real.log (2 * ν))
      nlinarith
    have hextra : (2 * ν)⁻¹ ≤ (2 : ℝ) ^ ⌈2 * |Real.log (2 * ν)|⌉₊ := by
      calc
        _ = Real.exp (-(Real.log (2 * ν))) := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
        _ ≤ Real.exp ((⌈2 * |Real.log (2 * ν)|⌉₊ : ℝ) * Real.log 2) :=
          Real.exp_le_exp.mpr hlogbound
        _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    calc
      _ = (4 * Real.sqrt (d : ℝ) / (3 * (1 / 2))) * (2 * ν)⁻¹ := by field_simp; ring
      _ ≤ (2 : ℝ) ^ inversePowerLength d * (2 : ℝ) ^ ⌈2 * |Real.log (2 * ν)|⌉₊ :=
        mul_le_mul hqpower hextra (by positivity) (by positivity)
      _ = _ := (pow_add _ _ _).symm

def inversePowerAccuracyFor (ν : ℝ) (d : ℕ) : ℝ :=
  min (ν / (8 * (inversePowerLengthFor ν d : ℝ) * Real.sqrt d))
    (1 / (2 * (inversePowerLengthFor ν d : ℝ)))

theorem inversePowerAccuracyFor_bounds (ν : ℝ) (hν : 0 < ν) (d : ℕ) (hd : 2 ≤ d) :
    0 < inversePowerAccuracyFor ν d ∧
    (inversePowerLengthFor ν d : ℝ) * inversePowerAccuracyFor ν d ≤ 1 / 2 ∧
    inversePowerAccuracyFor ν d ≤ ν /
      (8 * (inversePowerLengthFor ν d : ℝ) * Real.sqrt d) := by
  have hq : (0 : ℝ) < inversePowerLengthFor ν d := by
    exact_mod_cast (inversePowerLengthFor_bounds ν hν d hd).1
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd'
  refine ⟨lt_min (by positivity) (by positivity), ?_, min_le_left _ _⟩
  calc
    _ ≤ (inversePowerLengthFor ν d : ℝ) * (1 / (2 * (inversePowerLengthFor ν d : ℝ))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hq.le
    _ = 1 / 2 := by field_simp; ring

/-- A logarithmic refinement count for any positive requested accuracy. -/
def refinementLength (η : ℝ) : ℕ := ⌈2 * |Real.log η|⌉₊

theorem refinementLength_bounds (η : ℝ) (hη : 0 < η) :
    (refinementLength η : ℝ) < 2 * |Real.log η| + 1 ∧
    (1 / 2 : ℝ) ^ refinementLength η ≤ η := by
  refine ⟨Nat.ceil_lt_add_one (by positivity), ?_⟩
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hceil := Nat.le_ceil (2 * |Real.log η|)
  have hmul := mul_le_mul_of_nonneg_right hceil (show 0 ≤ Real.log 2 by linarith)
  have hlogbound : -((refinementLength η : ℝ) * Real.log 2) ≤ Real.log η := by
    have ha := neg_le_abs (Real.log η)
    have hb := abs_nonneg (Real.log η)
    change 2 * |Real.log η| * Real.log 2 ≤ (refinementLength η : ℝ) * Real.log 2 at hmul
    nlinarith
  calc
    _ = Real.exp (-((refinementLength η : ℝ) * Real.log 2)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      simp [one_div, inv_pow]
    _ ≤ Real.exp (Real.log η) := Real.exp_le_exp.mpr hlogbound
    _ = η := Real.exp_log hη

end
end Matvec
