import Nonsmooth.GaussianPosteriorEnergy

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def posteriorSupportProbabilityConstant (C : ℝ) : ℝ := 1 / (65536 * (C + 1))

theorem posteriorSupportProbabilityConstant_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < posteriorSupportProbabilityConstant C := by
  unfold posteriorSupportProbabilityConstant
  positivity

theorem support_log_ge_one {k : ℕ} (hk : 0 < k) : 1 ≤ Real.log (Real.exp 1 * k) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (by nlinarith [Real.exp_pos 1])

theorem posterior_budget_product {d k T : ℕ} (hk : 0 < k) {C : ℝ} (hC : 0 ≤ C)
    (hT : (T : ℝ) ≤ posteriorSupportProbabilityConstant C * d * k / Real.log (Real.exp 1 * k)) :
    (T : ℝ) * (65536 * (C + 1) * Real.log (Real.exp 1 * k)) ≤ (d : ℝ) * k := by
  have hlog : 0 < Real.log (Real.exp 1 * k) := lt_of_lt_of_le zero_lt_one (support_log_ge_one hk)
  have hcp : 0 < C + 1 := by linarith
  have he : posteriorSupportProbabilityConstant C * d * k / Real.log (Real.exp 1 * k) =
      (d : ℝ) * k / (65536 * (C + 1) * Real.log (Real.exp 1 * k)) := by
    unfold posteriorSupportProbabilityConstant
    field_simp
  rw [he] at hT
  exact (le_div_iff₀ (by positivity)).mp hT

theorem posterior_budget_energy_numeric {d k T : ℕ} (hd : 0 < d) (hk : 0 < k) {C : ℝ} (hC : 0 ≤ C)
    (hT : (T : ℝ) ≤ posteriorSupportProbabilityConstant C * d * k / Real.log (Real.exp 1 * k)) :
    C * (T : ℝ) * Real.log (Real.exp 1 * k) / d ≤ (k : ℝ) / 65536 := by
  have h := posterior_budget_product hk hC hT
  have hlog := support_log_ge_one hk
  have hnon : (0 : ℝ) ≤ (T : ℝ) * Real.log (Real.exp 1 * k) :=
    mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one hlog)
  apply (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr
  nlinarith

theorem posterior_budget_small_dimension_zero {d k T : ℕ} (hk : 0 < k) {C : ℝ} (hC : 0 ≤ C)
    (hd : d ≤ 4095) (hkd : (k : ℝ) ≤ (d : ℝ) / 512)
    (hT : (T : ℝ) ≤ posteriorSupportProbabilityConstant C * d * k / Real.log (Real.exp 1 * k)) : T = 0 := by
  have hd' : (d : ℝ) ≤ 4096 := by exact_mod_cast (show d ≤ 4096 by omega)
  have hk' : (k : ℝ) ≤ 8 := by linarith
  have hdk : (d : ℝ) * k ≤ 32768 :=
    (mul_le_mul hd' hk' (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) ≤ 4096)).trans_eq (by norm_num)
  have h := posterior_budget_product hk hC hT
  have hlog := support_log_ge_one hk
  have hclog : 1 ≤ (C + 1) * Real.log (Real.exp 1 * k) := by
    have hpos := mul_nonneg hC (le_trans zero_le_one hlog)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hclog (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
  have ht : (T : ℝ) < 1 := by nlinarith
  have ht' : T < 1 := by exact_mod_cast ht
  omega

end
end Nonsmooth
