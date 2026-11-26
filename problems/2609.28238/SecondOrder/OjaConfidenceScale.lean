import SecondOrder.RobustBatch

namespace SecondOrder
noncomputable section

def ojaRepeats (δ : ℝ) : ℕ := ⌈192*Real.log (2/δ)⌉₊+193
def ojaValidationFailure (δ : ℝ) : ℝ := δ/(2*(ojaRepeats δ : ℝ))

theorem ojaRepeats_lower (δ : ℝ) : 193 ≤ ojaRepeats δ := by unfold ojaRepeats; omega
theorem ojaRepeats_pos (δ : ℝ) : 0 < ojaRepeats δ := lt_of_lt_of_le (by norm_num) (ojaRepeats_lower δ)

theorem ojaRepeats_log_lower (δ : ℝ) : 192*Real.log (2/δ) ≤ (ojaRepeats δ : ℝ) := by
  have hn := Nat.le_ceil (192*Real.log (2/δ))
  unfold ojaRepeats
  push_cast
  linarith

theorem ojaRepeats_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (ojaRepeats δ : ℝ) ≤ 192*Real.log (2/δ)+194 := by
  have hl : 0 ≤ Real.log (2/δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 192*Real.log (2/δ) by positivity)
  unfold ojaRepeats
  push_cast
  linarith

theorem ojaValidationFailure_pos {δ : ℝ} (hδ : 0 < δ) : 0 < ojaValidationFailure δ := by
  have hn : (0:ℝ) < ojaRepeats δ := Nat.cast_pos.mpr (ojaRepeats_pos δ)
  exact div_pos hδ (by positivity)

theorem ojaValidationFailure_le {δ : ℝ} (hδ1 : δ ≤ 1) : ojaValidationFailure δ ≤ 1/192 := by
  have hn : (193:ℝ) ≤ ojaRepeats δ := by exact_mod_cast ojaRepeats_lower δ
  apply (div_le_iff₀ (show (0:ℝ) < 2*(ojaRepeats δ:ℝ) by linarith)).mpr
  linarith

theorem ojaValidationFailure_total (δ : ℝ) :
    (ojaRepeats δ : ℝ)*ojaValidationFailure δ = δ/2 := by
  have hn : (0:ℝ) < ojaRepeats δ := Nat.cast_pos.mpr (ojaRepeats_pos δ)
  unfold ojaValidationFailure
  field_simp
  ring

theorem ojaRepeats_sufficient {δ : ℝ} (hδ : 0 < δ) :
    (191/192 : ℝ)^(ojaRepeats δ) ≤ δ/2 := by
  have hn := ojaRepeats_log_lower δ
  have hl : Real.log (2/δ) = -Real.log (δ/2) := by
    rw [Real.log_div (by norm_num) hδ.ne', Real.log_div hδ.ne' (by norm_num)]
    ring
  rw [hl] at hn
  have he : (191/192:ℝ) ≤ Real.exp (-(1/192:ℝ)) := by
    linarith [Real.add_one_le_exp (-(1/192:ℝ))]
  calc
    _ ≤ Real.exp (-(1/192:ℝ))^(ojaRepeats δ) := pow_le_pow_left₀ (by norm_num) he _
    _ = Real.exp ((ojaRepeats δ:ℝ)*(-(1/192:ℝ))) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (Real.log (δ/2)) := Real.exp_le_exp.mpr (by linarith)
    _ = δ/2 := Real.exp_log (by positivity)

end
end SecondOrder
