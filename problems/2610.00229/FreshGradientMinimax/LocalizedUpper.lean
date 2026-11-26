import FreshGradientMinimax.OuterBudget
import FreshGradientMinimax.OuterWorkBounds

/-! Theorem G.1 / the upper-bound half of Theorem 3.4: an actual fixed
integer budget, a dimensionwise algorithm chosen before the instance,
and the displayed G-independent tenth-power logarithmic multiplier.
The lower-bound half of Theorem 3.4 is not asserted here. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
noncomputable section
namespace FreshGradientMinimax

theorem refinedOuterBudget_rate (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) :
    (refinedOuterBudget p.L p.σ p.μ p.gap p.G p.ε : ℝ) ≤
      10 ^ 200 * logarithmicEnvelope p ^ 10 * upperRate p := by
  let V := logarithmicEnvelope p ^ 10 * upperRate p
  have hΛ := (logarithmicEnvelope_bounds p).1
  have hr := upperRate_one p hreg
  have hpow : 1 ≤ logarithmicEnvelope p ^ 10 := one_le_pow₀ hΛ
  have hV : 1 ≤ V := by
    dsimp only [V]
    have h := mul_le_mul hpow hr (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ logarithmicEnvelope p ^ 10)
    simpa only [one_mul] using h
  have hw : refinedOuterWork p.L p.σ p.μ p.gap p.G p.ε ≤ 10 ^ 190 * V := by
    simpa only [V, mul_assoc] using refinedOuterWork_rate p hreg
  have hc : refinedOuterBudget p.L p.σ p.μ p.gap p.G p.ε ≤ ⌈12 * (1 + 10 ^ 190 * V)⌉₊ :=
    Nat.ceil_mono (by linarith only [hw])
  have hc' : (refinedOuterBudget p.L p.σ p.μ p.gap p.G p.ε : ℝ) ≤
      (⌈12 * (1 + 10 ^ 190 * V)⌉₊ : ℝ) := by exact_mod_cast hc
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 12 * (1 + 10 ^ 190 * V) by linarith only [hV])
  have hb : 12 * (1 + 10 ^ 190 * V) + 1 ≤ 10 ^ 200 * V := by nlinarith only [hV]
  change _ ≤ 10 ^ 200 * logarithmicEnvelope p ^ 10 * upperRate p
  have h := hc'.trans (hceil.le.trans hb)
  simpa only [V, mul_assoc] using h

theorem localized_upper_bound (p : Parameters) (hreg : p.ε ^ 2 ≤ p.L * p.gap) :
    ∃ N : ℕ, BudgetSuffices p (some p.G) N ∧
      (N : ℝ) ≤ 10 ^ 200 * logarithmicEnvelope p ^ 10 * upperRate p :=
  ⟨refinedOuterBudget p.L p.σ p.μ p.gap p.G p.ε,
    localized_budget_explicit p hreg, refinedOuterBudget_rate p hreg⟩

theorem localized_upper_statement : LocalizedUpperStatement :=
  ⟨10 ^ 200, by norm_num, localized_upper_bound⟩

end FreshGradientMinimax
