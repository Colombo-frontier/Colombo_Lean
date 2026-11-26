import Smoothness2601.BoundaryLower
import Smoothness2601.BoundaryHorizon
import Smoothness2601.AccuracyDimension

/-! The boundary hard instance obeys the same ambient-dimension convention. -/
noncomputable section
namespace Smoothness2601.BoundaryInstance
open ExtensiveChain DeferredPrefix
variable (b : Budgets)

def dimensionCoefficient : ℝ := max 1 (chainScale b)+2+
  (8*(4096*HardProfiles.radiusConstant^2)*(max 1 (chainScale b))/(1/16:ℝ)^2)*
    (Real.log (16*(finalRateConstant b+1)*(max 1 (chainScale b)))+8)

theorem dimensionCoefficient_pos : 0 < dimensionCoefficient b := by
  have hA : (1:ℝ) ≤ max 1 (chainScale b) := le_max_left _ _
  have hC := finalRateConstant_pos b
  have hc : 1 ≤ 16*(finalRateConstant b+1)*(max 1 (chainScale b)) := by nlinarith
  have hl := Real.log_nonneg hc
  unfold dimensionCoefficient
  positivity

theorem hardDimension_rate {ε : ℝ} {N n : ℕ} (hε : 0 < ε) (hsmall : ε ≤ Real.exp (-1))
    (hN : (N:ℝ) ≤ finalRateConstant b*ε^(-4:ℝ))
    (hT : (n+1:ℝ) ≤ chainScale b/(8*ε)^2) :
    (HardProfiles.hardDimension N n:ℝ) ≤ dimensionCoefficient b*(ε⁻¹)^2*Real.log ε⁻¹ := by
  have hε1 : ε ≤ 1 := hsmall.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hl : Real.log ε ≤ -1 := (Real.log_le_iff_le_exp hε).mpr hsmall
  have hlog : 1 ≤ Real.log ε⁻¹ := by rw [Real.log_inv]; linarith
  have ht : ((n+1:ℕ):ℝ) ≤ chainScale b*(ε⁻¹)^2 := by
    have hb : chainScale b/(8*ε)^2 ≤ chainScale b/ε^2 :=
      div_le_div_of_nonneg_left (chainScale_pos b).le (sq_pos_of_pos hε) (by nlinarith [sq_nonneg ε])
    have he : chainScale b/ε^2 = chainScale b*(ε⁻¹)^2 := by rw [div_eq_mul_inv,inv_pow]
    have ht' : ((n+1:ℕ):ℝ) ≤ chainScale b/(8*ε)^2 := by simpa using hT
    exact ht'.trans (hb.trans_eq he)
  have hr : (chainRadius HardProfiles.radiusConstant n)^2 ≤
      (4096*HardProfiles.radiusConstant^2)*((n+1:ℕ):ℝ) := by
    simpa using (chainRadius_sq HardProfiles.radiusConstant n).le
  have hN' : (N:ℝ) ≤ finalRateConstant b*ε^(-4:ℝ)*(orderTradeoff ⊤ 0 ε)^2 := by
    simpa only [orderTradeoff_infinite_zero hε hε1,one_pow,mul_one] using hN
  exact ambientDimension_accuracy_rate (p := ⊤) le_top (le_refl (0:ℝ)) hε hε1 hlog
    (finalRateConstant_pos b).le (by positivity) (by omega) (by norm_num) (HardProfiles.radius_pos n) hN' ht hr

end Smoothness2601.BoundaryInstance
