import Bilevel.ChiExtensionLedgerAbsorption

/-! The uniform source accuracy ratio pays the hidden gradient relative
to the finest normal scale. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

theorem hidden_gradient_from_accuracy_ratio {A η₀ η b K θ γ : ℝ}
    (hA : 0 ≤ A) (hη₀ : 0 ≤ η₀) (hη : 0 < η) (hb : 0 ≤ b)
    (hK : 0 < K) (hθ : 0 < θ) (J : ℕ)
    (hratio : A^(J+1)*((J:ℝ)+1)^6*b*θ/(K*η^J) ≤ γ) :
    A^(J+1)*η₀*Real.sqrt (2*(J:ℝ))*b^2/K^2 ≤ 2*η₀*γ*η^J*b/(K*θ) := by
  have hdepth : (J:ℝ)+1 ≤ ((J:ℝ)+1)^6 :=
    le_self_pow₀ (by have := Nat.cast_nonneg (α:=ℝ) J; linarith) (by norm_num)
  have hs := (sqrt_two_depth_le J).trans (mul_le_mul_of_nonneg_left hdepth (by norm_num : (0:ℝ) ≤ 2))
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ A^(J+1)*η₀*b^2/K^2 by positivity)
  have hm := mul_le_mul_of_nonneg_right hratio (show 0 ≤ 2*η₀*η^J*b/(K*θ) by positivity)
  have he : (A^(J+1)*((J:ℝ)+1)^6*b*θ/(K*η^J))*(2*η₀*η^J*b/(K*θ)) =
      2*A^(J+1)*η₀*((J:ℝ)+1)^6*b^2/K^2 := by field_simp; ring
  rw [he] at hm
  apply le_trans _ (hm.trans_eq (by ring))
  convert hs' using 1 <;> ring

end Bilevel.ChiExtensionCalibration
