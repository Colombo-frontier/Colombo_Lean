import Smoothness2601.HardParameters
import Smoothness2601.LowerBudget

/-! All integer and probability thresholds for the actual hard family, with
constants fixed before the regularity cap. -/
noncomputable section
namespace Smoothness2601.HardProfiles.WidthConstants
variable {b : Budgets} {M Λ β : ℝ} (W : WidthConstants b M Λ β)

def chainScale : ℝ := b.Δ*W.τ/(gapConstant+1)
def chainThreshold : ℝ := min W.threshold (min 1 (W.chainScale/2))
def rateConstant : ℝ := W.chainScale*b.σ^2/(16*W.signalConstant^2*W.K^2)
def finalRateConstant : ℝ := W.rateConstant/16^6

theorem chainScale_pos : 0 < W.chainScale :=
  div_pos (mul_pos b.Δ_pos W.τ_pos) (by linarith [gapConstant_pos])

theorem chainThreshold_pos : 0 < W.chainThreshold :=
  lt_min W.threshold_pos (lt_min zero_lt_one (div_pos W.chainScale_pos (by norm_num)))

theorem rateConstant_pos : 0 < W.rateConstant := by
  unfold rateConstant
  have := W.chainScale_pos
  have := W.signalConstant_pos
  have := W.K_pos
  have := b.σ_pos
  positivity

theorem finalRateConstant_pos : 0 < W.finalRateConstant := div_pos W.rateConstant_pos (by norm_num)

theorem chainThreshold_conditions {s : ℝ} (hs : 0 < s) (hsδ : s ≤ W.chainThreshold) :
    s ≤ W.threshold ∧ 2*s^2 ≤ W.chainScale := by
  have h1 : s ≤ 1 := hsδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hA : s ≤ W.chainScale/2 := hsδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨hsδ.trans (min_le_left _ _),by nlinarith⟩

theorem choose_chain {s : ℝ} (hs : 0 < s) (hsδ : s ≤ W.chainThreshold) :
    ∃ n : ℕ, W.chainScale/(2*s^2) ≤ (n+1:ℝ) ∧ (n+1:ℝ) ≤ W.chainScale/s^2 ∧
      (s^2/W.τ)*(gapConstant*(n+1)+1/2) ≤ b.Δ := by
  obtain ⟨n,hl,hu⟩ := LowerBudget.integer_chain hs (W.chainThreshold_conditions hs hsδ).2
  exact ⟨n,hl,hu,LowerBudget.initial_gap b.Δ_pos W.τ_pos gapConstant_pos.le hs hu⟩

theorem budget_reveal {p : WithTop ℕ} {s : ℝ} {N n : ℕ}
    (hp : 1 ≤ p) (hβ : 0 ≤ β) (hs : 0 < s) (hsδ : s ≤ W.chainThreshold)
    (hT : W.chainScale/(2*s^2) ≤ (n+1:ℝ))
    (hN : (N:ℝ) ≤ W.rateConstant*(orderTradeoff p β s)^2/s^4) :
    (N:ℝ)*BernoulliOracle.revealProbability (W.signalConstant*s*sineWidth p β s W.K) b.σ ≤
      (n+1:ℝ)/8 := by
  have hs1 := (W.threshold_conditions (W.chainThreshold_conditions hs hsδ).1).2.1
  simpa only [Nat.cast_add,Nat.cast_one] using
    LowerBudget.budget_reveal_bound hp hβ hs hs1 W.chainScale_pos.le W.signalConstant_pos W.K_pos
      b.σ_pos (T := n+1) (by simpa using hT) hN

theorem scaled_budget {p : WithTop ℕ} {ε : ℝ} {N : ℕ}
    (hp : 1 ≤ p) (hβ : 0 ≤ β) (hε : 0 < ε) (hεs : 16*ε ≤ W.chainThreshold)
    (hN : (N:ℝ) ≤ W.finalRateConstant*ε^(-4:ℝ)*(orderTradeoff p β ε)^2) :
    (N:ℝ) ≤ W.rateConstant*(orderTradeoff p β (16*ε))^2/(16*ε)^4 := by
  have hs : 0 < 16*ε := by positivity
  have hs1 := (W.threshold_conditions (W.chainThreshold_conditions hs hεs).1).2.1
  have hb := LowerBudget.accuracy_scale_rate hp hβ hε (by norm_num : (1:ℝ) ≤ 16) hs1
  have he : ε^(-4:ℝ) = 1/ε^4 := by
    rw [Real.rpow_neg hε.le]
    rw [show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast,one_div]
  rw [he] at hN
  apply hN.trans
  have hm := mul_le_mul_of_nonneg_left hb W.rateConstant_pos.le
  convert hm using 1 <;> dsimp [finalRateConstant] <;> ring

end Smoothness2601.HardProfiles.WidthConstants
