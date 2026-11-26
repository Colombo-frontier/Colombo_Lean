import Smoothness2601.HardLower
import Smoothness2601.HardHorizon
import Smoothness2601.AccuracyDimension

/-! The constructed hard instance has the source ambient dimension rate.
The coefficient is fixed before the order cap and accuracy. -/
noncomputable section
namespace Smoothness2601.HardProfiles
open ExtensiveChain DeferredPrefix
variable {b : Budgets} {M Λ β : ℝ} (W : WidthConstants b M Λ β)

def dimensionCoefficient : ℝ :=
  max 1 W.chainScale+2+
    (8*(4096*radiusConstant^2)*(max 1 W.chainScale)/(1/16 : ℝ)^2)*
      (Real.log (16*(W.finalRateConstant+1)*(max 1 W.chainScale))+8)

theorem dimensionCoefficient_pos : 0 < dimensionCoefficient W := by
  have hA : (1:ℝ) ≤ max 1 W.chainScale := le_max_left _ _
  have hC := W.finalRateConstant_pos
  have hc : 1 ≤ 16*(W.finalRateConstant+1)*(max 1 W.chainScale) := by nlinarith
  have hl := Real.log_nonneg hc
  unfold dimensionCoefficient
  positivity

theorem hardDimension_rate {p : WithTop ℕ} {ε : ℝ} {N n : ℕ}
    (hp : 1 ≤ p) (hβ : 0 ≤ β) (hε : 0 < ε) (hsmall : ε ≤ Real.exp (-1))
    (hN : (N : ℝ) ≤ W.finalRateConstant*ε^(-4 : ℝ)*(orderTradeoff p β ε)^2)
    (hT : (n+1 : ℝ) ≤ W.chainScale/(16*ε)^2) :
    (hardDimension N n : ℝ) ≤ dimensionCoefficient W*(ε⁻¹)^2*Real.log ε⁻¹ := by
  have hε1 : ε ≤ 1 := hsmall.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hl : Real.log ε ≤ -1 := (Real.log_le_iff_le_exp hε).mpr hsmall
  have hlog : 1 ≤ Real.log ε⁻¹ := by rw [Real.log_inv]; linarith
  have ht : ((n+1 : ℕ) : ℝ) ≤ W.chainScale*(ε⁻¹)^2 := by
    have hb : W.chainScale/(16*ε)^2 ≤ W.chainScale/ε^2 :=
      div_le_div_of_nonneg_left W.chainScale_pos.le (sq_pos_of_pos hε) (by nlinarith [sq_nonneg ε])
    have he : W.chainScale/ε^2 = W.chainScale*(ε⁻¹)^2 := by rw [div_eq_mul_inv,inv_pow]
    have hT' : ((n+1 : ℕ) : ℝ) ≤ W.chainScale/(16*ε)^2 := by simpa using hT
    exact hT'.trans (hb.trans_eq he)
  have hr : (chainRadius radiusConstant n)^2 ≤ (4096*radiusConstant^2)*((n+1 : ℕ) : ℝ) := by
    simpa using (chainRadius_sq radiusConstant n).le
  exact ambientDimension_accuracy_rate hp hβ hε hε1 hlog W.finalRateConstant_pos.le
    (by positivity) (by omega) (by norm_num) (radius_pos n) hN ht hr

end Smoothness2601.HardProfiles
