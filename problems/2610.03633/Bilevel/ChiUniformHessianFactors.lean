import Bilevel.ChiUniformDepthCancellation
import Bilevel.ChiUniformWidthCalibration

/-! The explicit geometric cancellations in W4--W6. In particular no
unquantified logarithmic loss is inserted at theta=kappa squared. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiCurvatureSchedule ChiIndependentWidths

theorem geometric_coefficient_absorption {C ω : ℝ} (hC : 1≤C)
    (hω : 0<ω) (hω1 : ω≤1) (J : ℕ) :
    C^(J+2)/ω^J≤(C^2/ω)^(J+1) := by
  have hn : C^(J+2)≤(C^2)^(J+1) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hC (by omega)
  have hd : ω^(J+1)≤ω^J := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hω.le _) hω1
  rw [div_pow]
  exact div_le_div₀ (pow_nonneg (sq_nonneg C) _) hn (pow_pos hω _) hd

theorem geometric_sqrt_scale_factor {θ C ω CT : ℝ} (hθ : 0≤θ) (hC : 1≤C)
    (hω : 0<ω) (hω1 : ω≤1) (hCT : 0<CT) (hpay : (C^2/ω)^2≤CT) :
    C^(chosenDepth θ+2)/ω^chosenDepth θ*((chosenDepth θ:ℝ)+1)^2*
      Real.sqrt (scale θ CT 6)≤Real.sqrt θ := by
  have hg := geometric_coefficient_absorption hC hω hω1 (chosenDepth θ)
  have hs := sqrt_scale_pays_ledger hθ (show 0≤C^2/ω by positivity) hCT hpay 6 2 (by norm_num)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg (sq_nonneg _))
    (Real.sqrt_nonneg _)).trans hs

theorem geometric_fine_factor {θ μ L η₀ a Cf B t : ℝ}
    (hθ : 0≤θ) (hμ : 0<μ) (hL : 0<L) (hη₀ : 0<η₀) (ha : 1≤a)
    (hCf : 0<Cf) (hB : 1≤B) (ht : 0<t) (ht1 : t≤1)
    (hpay : 4*(B^2/t)^2≤Cf) (J : ℕ) (hJ : 1≤J) :
    B^(J+2)/t^J*((J:ℝ)+1)*
      Real.sqrt (fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J)≤
        Real.sqrt θ/Real.sqrt (6*η₀) := by
  have hg := geometric_coefficient_absorption hB ht ht1 J
  have hs := fine_sqrt_depth_cancellation hθ hμ hL hη₀ ha hCf
    (show 0≤B^2/t by positivity) hpay J hJ
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg
    (show 0≤(J:ℝ)+1 by positivity))
    (Real.sqrt_nonneg (fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J))
  exact (hh.trans hs).trans_eq (Real.sqrt_div hθ (6*η₀))

theorem conditioning_sqrt_ratio {κ θ : ℝ} (hκ : 0<κ) (hθκ : θ≤κ^2) :
    Real.sqrt θ/(κ/6)≤6 := by
  apply (div_le_iff₀ (by positivity : 0<κ/6)).mpr
  have hs : Real.sqrt θ≤κ := Real.sqrt_le_iff.mpr ⟨hκ.le,hθκ⟩
  linarith only [hs]

end Bilevel.ChiExtensionCalibration
