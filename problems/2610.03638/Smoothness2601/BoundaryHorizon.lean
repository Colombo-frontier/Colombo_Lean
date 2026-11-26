import Smoothness2601.BoundaryOracle
import Smoothness2601.LowerBudget

/-! Dimension/order-independent chain length and sample threshold at L1=μ. -/
noncomputable section
namespace Smoothness2601.BoundaryInstance
open ExtensiveChain
variable (b : Budgets)

def chainScale : ℝ := b.Δ*spatialConstant b/(HardProfiles.gapConstant+1)
def chainThreshold : ℝ := min 1 (min (chainScale b/2) (b.σ/(Cutoffs.frontierGradientBound+1)))
def rateConstant : ℝ := chainScale b*b.σ^2/(16*(Cutoffs.frontierGradientBound+1)^2)
def finalRateConstant : ℝ := rateConstant b/8^4

theorem chainScale_pos : 0 < chainScale b := div_pos (mul_pos b.Δ_pos (spatialConstant_pos b))
  (by linarith [HardProfiles.gapConstant_pos])

theorem chainThreshold_pos : 0 < chainThreshold b :=
  lt_min zero_lt_one (lt_min (div_pos (chainScale_pos b) (by norm_num))
    (div_pos b.σ_pos (by linarith [frontierGradientBound_nonneg])))

theorem rateConstant_pos : 0 < rateConstant b := by
  unfold rateConstant
  have := chainScale_pos b
  have := b.σ_pos
  have := frontierGradientBound_nonneg
  positivity

theorem finalRateConstant_pos : 0 < finalRateConstant b := div_pos (rateConstant_pos b) (by norm_num)

theorem threshold_conditions {s : ℝ} (hs : 0 < s) (hsδ : s ≤ chainThreshold b) :
    s ≤ 1 ∧ 2*s^2 ≤ chainScale b ∧ s ≤ b.σ/(Cutoffs.frontierGradientBound+1) := by
  have h1 : s ≤ 1 := hsδ.trans (min_le_left _ _)
  have hA : s ≤ chainScale b/2 := hsδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  exact ⟨h1,by nlinarith,hsδ.trans ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem choose_chain {s : ℝ} (hs : 0 < s) (hsδ : s ≤ chainThreshold b) :
    ∃ n : ℕ, chainScale b/(2*s^2) ≤ (n+1:ℝ) ∧ (n+1:ℝ) ≤ chainScale b/s^2 ∧
      (s^2/spatialConstant b)*HardProfiles.gapConstant*(n+1) ≤ b.Δ := by
  obtain ⟨n,hl,hu⟩ := LowerBudget.integer_chain hs (threshold_conditions b hs hsδ).2.1
  have hg := LowerBudget.initial_gap b.Δ_pos (spatialConstant_pos b) HardProfiles.gapConstant_pos.le hs hu
  have ha : 0 ≤ s^2/spatialConstant b := by have := spatialConstant_pos b; positivity
  exact ⟨n,hl,hu,by nlinarith⟩

theorem budget_reveal {s : ℝ} {N n : ℕ} (hs : 0 < s)
    (hT : chainScale b/(2*s^2) ≤ (n+1:ℝ))
    (hN : (N:ℝ) ≤ rateConstant b/s^4) :
    (N:ℝ)*BernoulliOracle.revealProbability (s*(Cutoffs.frontierGradientBound+1)) b.σ ≤ (n+1:ℝ)/8 := by
  have hC : 0 < Cutoffs.frontierGradientBound+1 := by linarith [frontierGradientBound_nonneg]
  have hσ := b.σ_pos
  have hq : 0 ≤ BernoulliOracle.revealProbability (s*(Cutoffs.frontierGradientBound+1)) b.σ := by
    unfold BernoulliOracle.revealProbability
    positivity
  have hb := mul_le_mul_of_nonneg_right hN hq
  have he : (rateConstant b/s^4)*BernoulliOracle.revealProbability (s*(Cutoffs.frontierGradientBound+1)) b.σ =
      chainScale b/(16*s^2) := by
    unfold rateConstant BernoulliOracle.revealProbability
    field_simp
    ring
  rw [he] at hb
  apply hb.trans
  rw [show chainScale b/(16*s^2) = (chainScale b/(2*s^2))/8 by ring]
  exact div_le_div_of_nonneg_right hT (by norm_num)

theorem scaled_budget {ε : ℝ} {N : ℕ} (hε : 0 < ε)
    (hN : (N:ℝ) ≤ finalRateConstant b*ε^(-4:ℝ)) : (N:ℝ) ≤ rateConstant b/(8*ε)^4 := by
  have he : ε^(-4:ℝ) = 1/ε^4 := by
    rw [Real.rpow_neg hε.le]
    rw [show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast,one_div]
  rw [he] at hN
  convert hN using 1
  unfold finalRateConstant
  ring

end Smoothness2601.BoundaryInstance
