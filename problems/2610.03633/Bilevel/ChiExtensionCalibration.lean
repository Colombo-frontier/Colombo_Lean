import Bilevel.ChiCurvatureThreshold

/-! Scalar calibration of the actual nonuniform source schedule. These
theorems pay finite-sum derivative ledgers; they do not assume or assert
analytic extension estimates without a corresponding proved ledger. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiCurvatureSchedule

def normalCoefficient (L : ℝ) (J : ℕ) : ℝ := L/(4*Real.sqrt (2*(J:ℝ)))

def fineParameter (ρ m ell d Cfine : ℝ) (J : ℕ) : ℝ :=
  ρ/(Cfine^(J+1)*((J:ℝ)+1)*m*(ell/d))

theorem normalCoefficient_pos {L : ℝ} (hL : 0 < L) {J : ℕ} (hJ : 1 ≤ J) :
    0 < normalCoefficient L J := by
  have hJpos : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  unfold normalCoefficient
  positivity

theorem normalCoefficient_norm {L : ℝ} (J : ℕ) (hJ : 1 ≤ J) :
    normalCoefficient L J*Real.sqrt (2*(J:ℝ)) = L/4 := by
  have hJpos : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hs : Real.sqrt (2*(J:ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  unfold normalCoefficient
  field_simp
  ring

theorem normalCoefficient_ratio {L η a : ℝ} (hL : 0 < L) (J : ℕ) :
    (η*L*a)/normalCoefficient L J = 4*η*a*Real.sqrt (2*(J:ℝ)) := by
  unfold normalCoefficient
  field_simp
  ring

theorem sqrt_two_depth_le (J : ℕ) : Real.sqrt (2*(J:ℝ)) ≤ 2*((J:ℝ)+1) := by
  have hJ : (0:ℝ) ≤ J := Nat.cast_nonneg _
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (J:ℝ)]

theorem depth_power_absorption {A M CT : ℝ} (hA : 0 ≤ A) (hM : 1 ≤ M)
    (hCT : M*A ≤ CT) (J p q : ℕ) (hqp : q ≤ p) :
    M*(A^(J+1)*((J:ℝ)+1)^q) ≤ CT^(J+1)*((J:ℝ)+1)^p := by
  have hM0 : 0 ≤ M := by linarith
  have hJ : 1 ≤ (J:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) J; linarith
  have hpow : M*A^(J+1) ≤ CT^(J+1) := by
    calc
      _ ≤ M^(J+1)*A^(J+1) := mul_le_mul_of_nonneg_right
        (le_self_pow₀ hM (by omega)) (pow_nonneg hA _)
      _ = (M*A)^(J+1) := (mul_pow ..).symm
      _ ≤ CT^(J+1) := pow_le_pow_left₀ (mul_nonneg hM0 hA) hCT _
  have hdepth : ((J:ℝ)+1)^q ≤ ((J:ℝ)+1)^p := pow_le_pow_right₀ hJ hqp
  have hCT0 : 0 ≤ CT := (mul_nonneg hM0 hA).trans hCT
  have hm := mul_le_mul hpow hdepth (by positivity : 0 ≤ ((J:ℝ)+1)^q) (pow_nonneg hCT0 _)
  nlinarith only [hm]

theorem scale_pays_ledger {θ A M CT : ℝ} (hθ : 0 ≤ θ) (hA : 0 ≤ A)
    (hM : 1 ≤ M) (hCTpos : 0 < CT) (hCT : M*A ≤ CT) (p q : ℕ) (hqp : q ≤ p) :
    A^(ChiIndependentWidths.chosenDepth θ+1)*
      ((ChiIndependentWidths.chosenDepth θ:ℝ)+1)^q*scale θ CT p ≤ θ/M := by
  let J := ChiIndependentWidths.chosenDepth θ
  have hden : 0 < CT^(J+1)*((J:ℝ)+1)^p := by positivity
  have hMpos : 0 < M := by linarith
  have hb := depth_power_absorption hA hM hCT J p q hqp
  unfold scale
  apply (le_div_iff₀ hMpos).mpr
  apply (le_of_eq (by ring : A^(J+1)*((J:ℝ)+1)^q*
    (θ/(CT^(J+1)*((J:ℝ)+1)^p))*M =
    (M*(A^(J+1)*((J:ℝ)+1)^q))*(θ/(CT^(J+1)*((J:ℝ)+1)^p)))).trans
  have hm := mul_le_mul_of_nonneg_right hb (div_nonneg hθ hden.le)
  simpa only [mul_div_cancel₀ _ hden.ne'] using hm

theorem fineParameter_source_formula {θ μ L η a Cfine : ℝ}
    (hμ : 0 < μ) (hL : 0 < L) (J : ℕ) :
    fineParameter (θ*μ) (3*μ/2) (η*L*a) (normalCoefficient L J) Cfine J =
      θ/(6*η*Cfine^(J+1)*((J:ℝ)+1)*Real.sqrt (2*(J:ℝ))*a) := by
  unfold fineParameter
  rw [normalCoefficient_ratio hL]
  rw [show Cfine^(J+1)*((J:ℝ)+1)*(3*μ/2)*(4*η*a*Real.sqrt (2*(J:ℝ))) =
    μ*(6*η*Cfine^(J+1)*((J:ℝ)+1)*Real.sqrt (2*(J:ℝ))*a) by ring]
  rw [mul_comm θ μ, mul_div_mul_left _ _ hμ.ne']

theorem fineParameter_ge_one {θ μ L η a Cfine CT : ℝ}
    (hθ : 0 < θ) (hμ : 0 < μ) (hL : 0 < L) (hη : 0 < η) (ha : 0 < a)
    (hC : 1 ≤ Cfine) (hCTpos : 0 < CT)
    (hCT : max 1 (12*η)*Cfine ≤ CT) (p : ℕ) (hp : 2 ≤ p)
    (hJ : 1 ≤ ChiIndependentWidths.chosenDepth θ)
    (haT : a ≤ scale θ CT p) :
    1 ≤ fineParameter (θ*μ) (3*μ/2) (η*L*a) (normalCoefficient L (ChiIndependentWidths.chosenDepth θ))
      Cfine (ChiIndependentWidths.chosenDepth θ) := by
  let J := ChiIndependentWidths.chosenDepth θ
  have hCp : 0 < Cfine := by linarith
  have hJ0 : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hs : 0 < Real.sqrt (2*(J:ℝ)) := Real.sqrt_pos.mpr (by positivity)
  rw [fineParameter_source_formula hμ hL]
  apply (le_div_iff₀ (show 0 < 6*η*Cfine^(J+1)*((J:ℝ)+1)*Real.sqrt (2*(J:ℝ))*a by positivity)).mpr
  have ht := scale_pays_ledger hθ.le (show 0 ≤ Cfine by linarith)
    (show 1 ≤ max 1 (12*η) from le_max_left _ _) hCTpos hCT p 2 hp
  have hfactor := sqrt_two_depth_le J
  have hbound : 6*η*Cfine^(J+1)*((J:ℝ)+1)*Real.sqrt (2*(J:ℝ))*a ≤
      12*η*(Cfine^(J+1)*((J:ℝ)+1)^2*scale θ CT p) := by
    have hh := mul_le_mul hfactor haT ha.le (by positivity : 0 ≤ 2*((J:ℝ)+1))
    have hm := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ 6*η*Cfine^(J+1)*((J:ℝ)+1) by positivity)
    nlinarith only [hm]
  have hpay : max 1 (12*η)*(Cfine^(J+1)*((J:ℝ)+1)^2*scale θ CT p) ≤ θ := by
    simpa only [mul_comm] using (le_div_iff₀ (show 0 < max 1 (12*η) by positivity)).mp ht
  have hnon : 0 ≤ Cfine^(J+1)*((J:ℝ)+1)^2*scale θ CT p :=
    mul_nonneg (by positivity) (scale_pos hθ hCTpos p).le
  have hcompare := mul_le_mul_of_nonneg_right (le_max_right 1 (12*η)) hnon
  nlinarith only [hbound,hpay,hcompare]

end Bilevel.ChiExtensionCalibration
