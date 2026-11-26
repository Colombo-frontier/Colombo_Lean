import Bilevel.ChiExtensionCalibration

/-! The exact fine parameter pays its actual third-derivative weight,
with construction constants fixed independently of the public budgets. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

theorem fineParameter_cost_identity {ρ m ell d Cf : ℝ}
    (hm : 0 < m) (hell : 0 < ell) (hd : 0 < d) (hCf : 0 < Cf) (J : ℕ) :
    (ell/d)*fineParameter ρ m ell d Cf J = ρ/(Cf^(J+1)*((J:ℝ)+1)*m) := by
  unfold fineParameter
  have hJ : (0:ℝ) < (J:ℝ)+1 := by positivity
  field_simp
  ring

theorem fine_constant_absorption {P B M Cf : ℝ} (_hP : 0 ≤ P) (hB : 1 ≤ B)
    (hM : 1 ≤ M) (hCf : M*(max 1 P*B^2) ≤ Cf) (J : ℕ) :
    M*(P*B^(J+2)) ≤ Cf^(J+1)*((J:ℝ)+1) := by
  have hP1 : 1 ≤ max 1 P := le_max_left _ _
  have hB0 : 0 ≤ B := by linarith
  have hMp : 0 ≤ M := by linarith
  have hPpow : P ≤ (max 1 P)^(J+1) :=
    (le_max_right _ _).trans (le_self_pow₀ hP1 (by omega))
  have hBpow : B^(J+2) ≤ (B^2)^(J+1) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hB (by omega)
  have hab : P*B^(J+2) ≤ (max 1 P*B^2)^(J+1) := by
    rw [mul_pow]
    exact mul_le_mul hPpow hBpow (pow_nonneg hB0 _) (pow_nonneg (by positivity) _)
  have hpay := depth_power_absorption (A:=max 1 P*B^2) (by positivity) hM hCf J 1 0 (by norm_num)
  simp only [pow_zero,mul_one,pow_one] at hpay
  exact (mul_le_mul_of_nonneg_left hab hMp).trans hpay

theorem fine_third_budget {ρ m ell d Cf P B M : ℝ}
    (hρ : 0 ≤ ρ) (hm : 0 < m) (hell : 0 < ell) (hd : 0 < d)
    (hP : 0 ≤ P) (hB : 1 ≤ B) (hM : 1 ≤ M)
    (hCf : M*(max 1 P*B^2) ≤ Cf) (J : ℕ) :
    P*B^(J+2)*(ell/d)*fineParameter ρ m ell d Cf J ≤ ρ/(M*m) := by
  have hBpos : 0 < B := by linarith
  have hMpos : 0 < M := by linarith
  have hCfpos : 0 < Cf := lt_of_lt_of_le (by positivity) hCf
  have hc := fine_constant_absorption hP hB hM hCf J
  have he : P*B^(J+2)*(ell/d)*fineParameter ρ m ell d Cf J =
      (P*B^(J+2))*ρ/(Cf^(J+1)*((J:ℝ)+1)*m) := by
    rw [mul_assoc (P*B^(J+2)),fineParameter_cost_identity hm hell hd hCfpos]
    ring
  rw [he]
  have hden : 0 < Cf^(J+1)*((J:ℝ)+1)*m := by positivity
  apply (div_le_iff₀ hden).mpr
  have hcρ := mul_le_mul_of_nonneg_right hc hρ
  have ht : P*B^(J+2)*ρ ≤ ρ*(Cf^(J+1)*((J:ℝ)+1))/M :=
    (le_div_iff₀ hMpos).mpr (by nlinarith only [hcρ])
  apply ht.trans_eq
  field_simp
  ring

end Bilevel.ChiExtensionCalibration
