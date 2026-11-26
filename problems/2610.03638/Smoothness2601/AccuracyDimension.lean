import Smoothness2601.DimensionRate
import Smoothness2601.OrderTradeoff

/-! The actual uniform rate budget implies a polynomial call bound, yielding
the ambient epsilon^-2 log(1/epsilon) clause with fixed constants. -/
noncomputable section
namespace Smoothness2601.DeferredPrefix

theorem uniform_budget_polynomial {p : WithTop ℕ} {β ε C : ℝ} {N : ℕ}
    (hp : 1 ≤ p) (hβ : 0 ≤ β) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    (hN : (N : ℝ) ≤ C*ε^(-4 : ℝ)*(orderTradeoff p β ε)^2) :
    ((N+1 : ℕ) : ℝ) ≤ (C+1)*(ε⁻¹)^6 := by
  have hu : 1 ≤ ε⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hε).mpr (by simpa using hε1)
  have hu6 : 1 ≤ (ε⁻¹)^6 := one_le_pow₀ hu
  have hD0 : 0 ≤ orderTradeoff p β ε := (zero_le_one.trans (orderTradeoff_one_le hp hβ hε hε1))
  have hD := (sq_le_sq₀ hD0 (inv_nonneg.mpr hε.le)).mpr (orderTradeoff_le_inv hp hε)
  have he : ε^(-4 : ℝ) = (ε⁻¹)^4 := by
    rw [Real.rpow_neg hε.le]
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl,Real.rpow_natCast,inv_pow]
  rw [he] at hN
  have hb := mul_le_mul_of_nonneg_left hD (mul_nonneg hC (pow_nonneg (inv_nonneg.mpr hε.le) 4))
  have hn : (N : ℝ) ≤ C*(ε⁻¹)^6 := hN.trans (hb.trans_eq (by ring))
  push_cast
  nlinarith

theorem ambientDimension_accuracy_rate {p : WithTop ℕ} {β ε C A CR δ R : ℝ} {N T : ℕ}
    (hp : 1 ≤ p) (hβ : 0 ≤ β) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlogε : 1 ≤ Real.log ε⁻¹) (hC : 0 ≤ C) (hCR : 0 ≤ CR)
    (hT : 1 ≤ T) (hδ : 0 < δ) (hR : 0 < R)
    (hN : (N : ℝ) ≤ C*ε^(-4 : ℝ)*(orderTradeoff p β ε)^2)
    (hTb : (T : ℝ) ≤ A*(ε⁻¹)^2) (hRb : R^2 ≤ CR*T) :
    (ambientDimension (N+1) T δ R : ℝ) ≤
      (max 1 A+2+(8*CR*(max 1 A)/δ^2)*(Real.log (16*(C+1)*(max 1 A))+8))*
        (ε⁻¹)^2*Real.log ε⁻¹ := by
  apply ambientDimension_polynomial_rate (N+1) T (by omega) hT hδ hR
  · rw [inv_eq_one_div]
    exact (le_div_iff₀ hε).mpr (by simpa using hε1)
  · exact hlogε
  · linarith
  · exact le_max_left _ _
  · exact hCR
  · exact uniform_budget_polynomial hp hβ hε hε1 hC hN
  · exact hTb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
  · exact hRb

end Smoothness2601.DeferredPrefix
