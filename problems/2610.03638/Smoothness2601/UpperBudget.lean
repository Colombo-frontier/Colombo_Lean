import Smoothness2601.UpperWeights
import Smoothness2601.OuterSchedule
import Smoothness2601.HypergradientCost

/-! Uniform absorption of every integer-batch and restart overhead. The finite
near-minimizing stencil has size O(log(1/ε)), including infinite smoothness. -/
noncomputable section
namespace Smoothness2601.UpperBudget
open HypergradientGeometry OuterSchedule

def constant (b : Budgets) (M Λ β c : ℝ) : ℝ :=
  countConstant b*HypergradientCost.constant b*
    (10+weightConstant b M Λ β c ^ 2+radiusConstant b)

theorem constant_pos (b : Budgets) (hgap : b.μ < b.L₁) (M Λ β c : ℝ) :
    0 < constant b M Λ β c := by
  have hC := HypergradientCost.constant_pos b hgap
  have hK := countConstant_pos b
  have hR := radiusConstant_pos b
  unfold constant
  positivity

theorem rounding_bound (b : Budgets) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (r : ℕ) (hr : (r:ℝ) ≤ 2*Real.log (1/ε)) :
    ((2*Population.stencilHalfOrder r+2:ℕ):ℝ)*Real.log (2/ε)+
      Real.log (2+radius b ε/ε) ≤ (9+radiusConstant b)*(1/ε ^ 2) := by
  have hi : 1 ≤ 1/ε := (le_div_iff₀ hε).mpr (by simpa using hε1)
  have hi2 : 1 ≤ 1/ε ^ 2 := (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by nlinarith)
  have ht : Real.log (1/ε) ≤ 1/ε := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hl : Real.log (2/ε) ≤ 2/ε := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hn : ((2*Population.stencilHalfOrder r+2:ℕ):ℝ) ≤ 4/ε := by
    have hs : 2*Population.stencilHalfOrder r+2 ≤ r+2 := by
      unfold Population.stencilHalfOrder
      omega
    have hs' : ((2*Population.stencilHalfOrder r+2:ℕ):ℝ) ≤ (r:ℝ)+2 := by exact_mod_cast hs
    calc
      _ ≤ (r:ℝ)+2 := hs'
      _ ≤ 2*(1/ε)+2 := by linarith
      _ ≤ 4*(1/ε) := by linarith
      _ = _ := by ring
  have hn0 : 0 ≤ ((2*Population.stencilHalfOrder r+2:ℕ):ℝ) := Nat.cast_nonneg _
  have hp := mul_le_mul hn hl (Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith))) (by positivity : 0 ≤ 4/ε)
  have hpe : (4/ε)*(2/ε) = 8*(1/ε ^ 2) := by ring
  rw [hpe] at hp
  have hR := div_le_div_of_nonneg_right (radius_bound b hε hε1) hε.le
  have hRl : Real.log (2+radius b ε/ε) ≤ 1+radius b ε/ε := by
    have hn := radius_nonneg b hε
    have hh := Real.log_le_sub_one_of_pos (show 0 < 2+radius b ε/ε by positivity)
    linarith
  have hRe : radiusConstant b/ε/ε = radiusConstant b*(1/ε ^ 2) := by ring
  rw [hRe] at hR
  nlinarith

theorem bracket_bound (b : Budgets) {p : WithTop ℕ} {M Λ β c ε : ℝ}
    (hp : 1 ≤ p) (hβ : 0 ≤ β) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (r : ℕ) (hr : 1 ≤ r)
    (hrlog : (r:ℝ) ≤ 2*Real.log (1/ε))
    (hscore : orderTerm β ε r ≤ (2*Real.exp 1)*orderTradeoff p β ε) :
    let W := ((2*Population.stencilHalfOrder r+1:ℕ):ℝ)/
      HypergradientSource.differenceRadius b M Λ β c ε r
    (1+W ^ 2)*(1/ε ^ 2)+((2*Population.stencilHalfOrder r+2:ℕ):ℝ)*Real.log (2/ε)+
      Real.log (2+radius b ε/ε) ≤
      (10+weightConstant b M Λ β c ^ 2+radiusConstant b)*(1/ε ^ 2)*orderTradeoff p β ε ^ 2 := by
  dsimp only
  have hw := selected_weight b (M := M) (Λ := Λ) hp hβ hε hε1 hc hc1 r hr hscore
  have hW0 : 0 ≤ ((2*Population.stencilHalfOrder r+1:ℕ):ℝ)/
      HypergradientSource.differenceRadius b M Λ β c ε r := by
    exact div_nonneg (Nat.cast_nonneg _) (Population.populationRadius_pos
      (AdjointGeometry.ballRadius_one b) (mul_pos hc hε) r).le
  have hD := orderTradeoff_one_le hp hβ hε hε1
  have hD2 : 1 ≤ orderTradeoff p β ε ^ 2 := by nlinarith
  have hC := weightConstant_pos b M Λ β hc
  have hw2 := (sq_le_sq₀ hW0 (mul_nonneg hC.le (by linarith))).mpr hw
  have hh := rounding_bound b hε hε1 r hrlog
  have hR := radiusConstant_pos b
  have hi : 0 ≤ 1/ε ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hw2 hi
  have hrest := mul_le_mul_of_nonneg_left hD2
    (show 0 ≤ (10+radiusConstant b)*(1/ε ^ 2) by positivity)
  nlinarith

end Smoothness2601.UpperBudget
