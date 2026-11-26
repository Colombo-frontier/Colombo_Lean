import Bilevel.ChiFineParameterBudget

/-! Physical source scales in the fine extension. The second-jet estimate
is deliberately conservative and is paid by the same source accuracy window
as the inverse-locality ratio. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

theorem fine_source_energy_scale {L η₀ η b K a : ℝ}
    (hL : 0 < L) (hη₀ : 0 ≤ η₀) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hK : 0 < K) (ha : 1 ≤ a) (J : ℕ) :
    (η₀*L*a)*(η^J*b/(K*a))^2/normalCoefficient L J ≤
      4*η₀*Real.sqrt (2*(J:ℝ))*b^2/K^2 := by
  have hap : 0 < a := by linarith
  have hp := pow_le_one₀ hη hη1 (n:=J)
  have hp0 := pow_nonneg hη J
  have hs : (η^J)^2 ≤ a := by nlinarith
  have he : (η₀*L*a)*(η^J*b/(K*a))^2/normalCoefficient L J =
      (4*η₀*Real.sqrt (2*(J:ℝ))*b^2/K^2)*((η^J)^2/a) := by
    unfold normalCoefficient
    field_simp
    ring
  rw [he]
  apply mul_le_of_le_one_right
  · positivity
  · exact (div_le_one hap).mpr hs

theorem fine_source_width_le {η b K a : ℝ}
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hb : 0 ≤ b) (hK : 0 < K) (ha : 1 ≤ a) (J : ℕ) :
    η^J*b/(K*a) ≤ b/K := by
  have hap : 0 < a := by linarith
  apply (div_le_iff₀ (mul_pos hK hap)).mpr
  have hp := mul_le_mul_of_nonneg_right (pow_le_one₀ hη hη1 (n:=J)) hb
  have hab := mul_le_mul_of_nonneg_left ha hb
  have he : b/K*(K*a) = b*a := by field_simp; ring
  rw [he]
  nlinarith only [hp,hab]

theorem fine_source_second_scale {θ μ L η₀ η b K a Cf : ℝ}
    (hθ : 0 ≤ θ) (hμ : 0 < μ) (hL : 0 < L) (hη₀ : 0 < η₀)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hb : 0 ≤ b) (hK : 0 < K) (ha : 1 ≤ a)
    (hCf : 1 ≤ Cf) (J : ℕ) (hJ : 1 ≤ J)
    (hv : 1 ≤ fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J) :
    (η₀*L*a)*(η^J*b/(K*a))*
      Real.sqrt (fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J)/
      normalCoefficient L J ≤ 2*θ*b/(3*K) := by
  let v := fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J
  have hap : 0 < a := by linarith
  have hdp := normalCoefficient_pos hL hJ
  have hCfp : 0 < Cf := by linarith
  have hwidth0 : 0 ≤ η^J*b/(K*a) := by positivity
  have hs : Real.sqrt v ≤ v := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [sq_nonneg (v-1)]
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (η₀*L*a)*(η^J*b/(K*a))/normalCoefficient L J by positivity)
  have he : (η₀*L*a)*(η^J*b/(K*a))*v/normalCoefficient L J =
      (η^J*b/(K*a))*((2*θ/3)/(Cf^(J+1)*((J:ℝ)+1))) := by
    calc
      _ = (η^J*b/(K*a))*((η₀*L*a)/normalCoefficient L J*v) := by ring
      _ = _ := by
        rw [fineParameter_cost_identity (by positivity) (by positivity) hdp hCfp]
        field_simp
        ring
  have hden : 1 ≤ Cf^(J+1)*((J:ℝ)+1) := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hCf) (by have := Nat.cast_nonneg (α:=ℝ) J; linarith)
  have hfrac : (2*θ/3)/(Cf^(J+1)*((J:ℝ)+1)) ≤ 2*θ/3 :=
    div_le_self (by positivity) hden
  have hwidth := fine_source_width_le hη hη1 hb hK ha J
  have hprod := mul_le_mul hwidth hfrac (by positivity) (div_nonneg hb hK.le)
  calc
    _ ≤ (η₀*L*a)*(η^J*b/(K*a))*v/normalCoefficient L J := by
      convert hm using 1 <;> ring
    _ = _ := he
    _ ≤ (b/K)*(2*θ/3) := hprod
    _ = _ := by ring

end Bilevel.ChiExtensionCalibration
