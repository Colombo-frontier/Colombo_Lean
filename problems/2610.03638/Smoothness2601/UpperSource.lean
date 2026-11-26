import Smoothness2601.OuterSource
import Smoothness2601.UpperBudget

/-! A single public finite order, deterministic sample budget, and constants
uniform in finite/infinite smoothness order and ambient dimension. -/
noncomputable section
namespace Smoothness2601.UpperSource
open HypergradientGeometry OuterSchedule

def biasCoefficient (b : Budgets) : ℝ := b.μ/(512*b.L₁)

def accuracyThreshold (b : Budgets) : ℝ :=
  min (min 1 (Real.exp (-1))) (min (32*innerSensitivity b) (32*b.L₁))

def constant (b : Budgets) (M Λ β : ℝ) : ℝ :=
  UpperBudget.constant b M Λ β (biasCoefficient b)

theorem biasCoefficient_pos (b : Budgets) : 0 < biasCoefficient b :=
  div_pos b.μ_pos (mul_pos (by norm_num) b.L₁_pos)

theorem biasCoefficient_small (b : Budgets) : biasCoefficient b ≤ b.μ/(256*b.L₁) := by
  apply div_le_div_of_nonneg_left b.μ_pos.le (mul_pos (by norm_num) b.L₁_pos)
  nlinarith [b.L₁_pos]

theorem biasCoefficient_le_one (b : Budgets) (hgap : b.μ < b.L₁) : biasCoefficient b ≤ 1 := by
  apply (div_le_iff₀ (mul_pos (by norm_num) b.L₁_pos)).mpr
  nlinarith [b.L₁_pos]

theorem accuracyThreshold_pos (b : Budgets) : 0 < accuracyThreshold b := by
  have hC := innerSensitivity_pos b
  have hL := b.L₁_pos
  unfold accuracyThreshold
  positivity

theorem threshold_conditions (b : Budgets) {ε : ℝ} (hε : 0 < ε) (hs : ε ≤ accuracyThreshold b) :
    ε ≤ 1 ∧ ε ≤ 32*innerSensitivity b ∧ ε ≤ 32*b.L₁ ∧ 1 ≤ Real.log (1/ε) := by
  have hs₁ := (le_min_iff.mp hs).1
  have hs₂ := (le_min_iff.mp hs).2
  refine ⟨(le_min_iff.mp hs₁).1,(le_min_iff.mp hs₂).1,(le_min_iff.mp hs₂).2,?_⟩
  have hh := Real.log_le_log hε (le_min_iff.mp hs₁).2
  rw [Real.log_exp] at hh
  rw [one_div,Real.log_inv]
  linarith

theorem constant_pos (b : Budgets) (hgap : b.μ < b.L₁) (M Λ β : ℝ) :
    0 < constant b M Λ β := UpperBudget.constant_pos b hgap M Λ β _

theorem count_bound (b : Budgets) (hgap : b.μ < b.L₁)
    {p : WithTop ℕ} {M Λ β ε : ℝ} (hp : 1 ≤ p) (hβ : 0 ≤ β)
    (hε : 0 < ε) (hs : ε ≤ accuracyThreshold b) (r : ℕ) (hr : 1 ≤ r)
    (hrlog : (r:ℝ) ≤ 2*Real.log (1/ε))
    (hscore : orderTerm β ε r ≤ (2*Real.exp 1)*orderTradeoff p β ε) :
    (OuterSource.callCount b M Λ β (biasCoefficient b) r ε:ℝ) ≤
      constant b M Λ β*ε ^ (-4:ℝ)*orderTradeoff p β ε ^ 2 := by
  obtain ⟨hε1,hεC,hεL,_⟩ := threshold_conditions b hε hs
  have hc := biasCoefficient_pos b
  have hb := OuterSource.total_sample_budget b hgap (M := M) (Λ := Λ) (β := β)
    hc hε hε1 hεC hεL r
  have hbr := UpperBudget.bracket_bound b (M := M) (Λ := Λ) hp hβ hε hε1 hc (biasCoefficient_le_one b hgap)
    r hr hrlog hscore
  have hK := iterations_power_bound b hε hε1
  have hC := (HypergradientCost.constant_pos b hgap).le
  have hR := radiusConstant_pos b
  have hB : 0 ≤ (10+UpperBudget.weightConstant b M Λ β (biasCoefficient b) ^ 2+radiusConstant b)*
      (1/ε ^ 2)*orderTradeoff p β ε ^ 2 := by positivity
  have he : (1/ε ^ 2)*(1/ε ^ 2) = ε ^ (-4:ℝ) := by
    rw [Real.rpow_neg hε.le,show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast]
    field_simp
    ring
  calc
    _ ≤ (iterations b ε:ℝ)*HypergradientCost.constant b*
        ((10+UpperBudget.weightConstant b M Λ β (biasCoefficient b) ^ 2+radiusConstant b)*
          (1/ε ^ 2)*orderTradeoff p β ε ^ 2) :=
      hb.trans (mul_le_mul_of_nonneg_left hbr (mul_nonneg (Nat.cast_nonneg _) hC))
    _ ≤ (countConstant b*(1/ε ^ 2))*HypergradientCost.constant b*
        ((10+UpperBudget.weightConstant b M Λ β (biasCoefficient b) ^ 2+radiusConstant b)*
          (1/ε ^ 2)*orderTradeoff p β ε ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hC) hB
    _ = _ := by unfold constant UpperBudget.constant; rw [← he]; ring

/-- This chooses an actual finite stencil, even when p=∞. The constants do
not depend on p, ε, dimensions, population, or oracle law. -/
theorem finite_order_budget (b : Budgets) (hgap : b.μ < b.L₁)
    {p : WithTop ℕ} {M Λ β ε : ℝ} (hp : 1 ≤ p) (hβ : 0 ≤ β)
    (hε : 0 < ε) (hs : ε ≤ accuracyThreshold b) :
    ∃ r : ℕ, 1 ≤ r ∧ (r:WithTop ℕ) ≤ p ∧
      (OuterSource.callCount b M Λ β (biasCoefficient b) r ε:ℝ) ≤
        constant b M Λ β*ε ^ (-4:ℝ)*orderTradeoff p β ε ^ 2 := by
  obtain ⟨hε1,_,_,ht⟩ := threshold_conditions b hε hs
  obtain ⟨r,hr,hrp,hrlog,hscore⟩ := UpperOrder.finite_near_minimizer hp hβ hε hε1 ht
  exact ⟨r,hr,hrp,count_bound b hgap hp hβ hε hs r hr hrlog hscore⟩

end Smoothness2601.UpperSource
