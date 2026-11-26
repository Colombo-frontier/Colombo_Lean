import Bilevel.ChiFineParameterBudget
import Bilevel.ChiAccuracyConstants

/-! Absorption of the proved extension ledgers by constants chosen before
all dimensions, public budgets, and depths. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

theorem coefficient_power_absorption {P B : ℝ} (_hP : 0 ≤ P) (hB : 1 ≤ B) (J : ℕ) :
    P*B^(J+2) ≤ (max 1 P*B^2)^(J+1) := by
  have hP1 : 1 ≤ max 1 P := le_max_left _ _
  have hB0 : 0 ≤ B := by linarith
  have hPpow : P ≤ (max 1 P)^(J+1) :=
    (le_max_right _ _).trans (le_self_pow₀ hP1 (by omega))
  have hBpow : B^(J+2) ≤ (B^2)^(J+1) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hB (by omega)
  rw [mul_pow]
  exact mul_le_mul hPpow hBpow (pow_nonneg hB0 _) (pow_nonneg (by positivity) _)

theorem three_coefficients_absorption {P Q R B C : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hB : 1 ≤ B) (hC : 1 ≤ C) (J : ℕ) :
    P*B^(J+2)+Q*C^(J+2)+R ≤
      (max 1 (P+Q+R)*(B+C)^2)^(J+1) := by
  have hBp : 0 ≤ B := by linarith
  have hCp : 0 ≤ C := by linarith
  have hBC : 1 ≤ B+C := by linarith
  have h1 := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hBp (show B ≤ B+C by linarith) (J+2)) hP
  have h2 := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hCp (show C ≤ B+C by linarith) (J+2)) hQ
  have h3 := mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=J+2) hBC) hR
  have hm : P*B^(J+2)+Q*C^(J+2)+R ≤ (P+Q+R)*(B+C)^(J+2) := by nlinarith only [h1,h2,h3]
  exact hm.trans (coefficient_power_absorption (by positivity) hBC J)

theorem three_coefficients_constant_ge_one {P Q R B C : ℝ} (hB : 1 ≤ B) (hC : 1 ≤ C) :
    1 ≤ max 1 (P+Q+R)*(B+C)^2 := by
  apply one_le_mul_of_one_le_of_one_le (le_max_left _ _)
  exact one_le_pow₀ (by linarith)

theorem source_extension_second_absorption {P Q R B C b : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hb : 0 ≤ b) (J : ℕ) :
    P*B^(J+2)*((J:ℝ)+1)^2*b+Q*C^(J+2)*b+R*((J:ℝ)+1)^2*b ≤
      (max 1 (P+Q+R)*(B+C)^2)^(J+1)*((J:ℝ)+1)^2*b := by
  have hJ : 1 ≤ ((J:ℝ)+1)^2 := one_le_pow₀ (by have := Nat.cast_nonneg (α:=ℝ) J; linarith)
  have hQdepth := mul_le_mul_of_nonneg_left hJ (show 0 ≤ Q*C^(J+2)*b by positivity)
  have hh := mul_le_mul_of_nonneg_right (three_coefficients_absorption hP hQ hR hB hC J)
    (show 0 ≤ ((J:ℝ)+1)^2*b by positivity)
  nlinarith only [hQdepth,hh]

theorem source_extension_third_absorption {P R B θ CT M : ℝ}
    (hP : 0 ≤ P) (hR : 0 ≤ R) (hB : 1 ≤ B) (hθ : 0 ≤ θ) (hM : 1 ≤ M)
    (hCTpos : 0 < CT) (hCT : M*(max 1 (P+R)*(B+1)^2) ≤ CT)
    (p : ℕ) (hp : 2 ≤ p) :
    let J := ChiIndependentWidths.chosenDepth θ
    (P*B^(J+2)+R)*((J:ℝ)+1)^2*ChiCurvatureSchedule.scale θ CT p ≤ θ/M := by
  dsimp only
  have ha := three_coefficients_absorption hP (show (0:ℝ) ≤ 0 by norm_num) hR hB (show (1:ℝ) ≤ 1 by norm_num)
    (ChiIndependentWidths.chosenDepth θ)
  simp only [zero_mul,add_zero] at ha
  have ht := scale_pays_ledger hθ (show 0 ≤ max 1 (P+R)*(B+1)^2 by positivity) hM hCTpos hCT p 2 hp
  apply le_trans _ ht
  have hscale : 0 ≤ ChiCurvatureSchedule.scale θ CT p := by unfold ChiCurvatureSchedule.scale; positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (sq_nonneg _)) hscale

end Bilevel.ChiExtensionCalibration
