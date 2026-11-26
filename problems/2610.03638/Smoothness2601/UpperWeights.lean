import Smoothness2601.UpperOrder
import Smoothness2601.HypergradientSource

/-! Uniform weight bound for the actual finite selected stencil. -/
noncomputable section
namespace Smoothness2601.UpperBudget
open Population ChebyshevDifferentiation

def weightConstant (b : Budgets) (M Λ β c : ℝ) : ℝ :=
  (2*Real.exp 1/c)*weightGrowthConstant (normalizedAmplitude b M)
    (normalizedFrequency Λ*AdjointGeometry.ballRadius b) β

theorem weightConstant_pos (b : Budgets) (M Λ β : ℝ) {c : ℝ} (hc : 0 < c) :
    0 < weightConstant b M Λ β c := by
  exact mul_pos (div_pos (mul_pos (by norm_num) (Real.exp_pos _)) hc)
    (weightGrowthConstant_pos (normalizedAmplitude_one_le M)
      (Population.normalizedFrequency_mul_one_le (AdjointGeometry.ballRadius_one b)) β)

theorem scaled_orderTerm {β ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1)
    (r : ℕ) (hr : 1 ≤ r) : orderTerm β (c*ε) r ≤ (1/c)*orderTerm β ε r := by
  have hci : 1 ≤ 1/c := (le_div_iff₀ hc).mpr (by simpa using hc1)
  have hh := orderTerm_scale_lower (β := β) (mul_pos hc hε) hci hr
  have he : (1/c)*(c*ε) = ε := by field_simp
  rw [he] at hh
  have hi : (1/c)⁻¹ = c := by simp
  rw [hi] at hh
  calc
    _ ≤ orderTerm β ε r/c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by ring

theorem selected_weight (b : Budgets) {p : WithTop ℕ} {M Λ β c ε : ℝ}
    (_hp : 1 ≤ p) (_hβ : 0 ≤ β) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (r : ℕ) (hr : 1 ≤ r)
    (hscore : orderTerm β ε r ≤ (2*Real.exp 1)*orderTradeoff p β ε) :
    ((2*Population.stencilHalfOrder r+1:ℕ):ℝ)/
      HypergradientSource.differenceRadius b M Λ β c ε r ≤
      weightConstant b M Λ β c*orderTradeoff p β ε := by
  let C := weightGrowthConstant (normalizedAmplitude b M)
    (normalizedFrequency Λ*AdjointGeometry.ballRadius b) β
  have hC : 0 ≤ C := (weightGrowthConstant_pos (normalizedAmplitude_one_le M)
    (Population.normalizedFrequency_mul_one_le (AdjointGeometry.ballRadius_one b)) β).le
  have hw := Population.populationRadius_weight_bound (b := b) (M := M) (Λ := Λ) (β := β)
    (AdjointGeometry.ballRadius_one b) (mul_pos hc hε) r hr
  rw [explicit_weights_abs_sum _
    (Population.populationRadius_pos (AdjointGeometry.ballRadius_one b) (mul_pos hc hε) r)] at hw
  have hw' : ((2*Population.stencilHalfOrder r+1:ℕ):ℝ)/
      HypergradientSource.differenceRadius b M Λ β c ε r ≤ C*orderTerm β (c*ε) r :=
    hw.trans_eq (by unfold C orderTerm; ring)
  have hs := (scaled_orderTerm hε hc hc1 r hr).trans
    (mul_le_mul_of_nonneg_left hscore (by positivity))
  exact hw'.trans ((mul_le_mul_of_nonneg_left hs hC).trans_eq (by
    unfold C weightConstant
    ring))

end Smoothness2601.UpperBudget
