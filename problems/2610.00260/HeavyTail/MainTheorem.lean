import HeavyTail.MainLower
import HeavyTail.MainUpper

/-! The manuscript's unified all-budget theorem in the full oracle model.
The lower constant is universal, the upper constant depends only on p,
and the risk is that of arbitrary randomized policies stopping a.s. by T. -/
noncomputable section
open scoped ENNReal
namespace HeavyTail

theorem unified_all_budget {d : ℕ} (θ : OracleParameters) (hT : 0 < θ.T)
    (hdim : Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d) :
    ENNReal.ofReal ((1 / 147456 : ℝ) * envelope θ.μ θ.D
      (min θ.G (statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T))) ≤
        atMostCallMinimax (HardSpace d) θ ∧
    atMostCallMinimax (HardSpace d) θ ≤ ENNReal.ofReal (unifiedUpperConstant θ.p *
      envelope θ.μ θ.D (min θ.G (optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ θ.T))) :=
  ⟨unified_atMostCallMinimax_lower θ hT hdim, unified_atMostCallMinimax_upper θ hT⟩

theorem unified_all_budget_constants :
    ∃ c C : ℝ → ℝ, (∀ p : ℝ, 0 < c p ∧ 0 < C p) ∧
      ∀ (d : ℕ) (θ : OracleParameters), 0 < θ.T → Nat.ceil (θ.L ^ 2 / θ.s ^ 2) ≤ d →
        ENNReal.ofReal (c θ.p * envelope θ.μ θ.D
          (min θ.G (statisticalAmplitude θ.L θ.s θ.p θ.δ θ.T))) ≤
            atMostCallMinimax (HardSpace d) θ ∧
        atMostCallMinimax (HardSpace d) θ ≤ ENNReal.ofReal (C θ.p * envelope θ.μ θ.D
          (min θ.G (optimizationAmplitude θ.G θ.L θ.s θ.p θ.δ θ.T))) := by
  refine ⟨fun _ => 1 / 147456, unifiedUpperConstant, ?_, ?_⟩
  · intro p
    exact ⟨by norm_num, unifiedUpperConstant_pos p⟩
  · intro d θ hT hdim
    exact unified_all_budget θ hT hdim

end HeavyTail
