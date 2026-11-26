import Smoothness2601.ExactUpperLower
import Smoothness2601.ExactUpperFinite
import Smoothness2601.OrderRates

/-! Consequences for arbitrary fixed finite lists and exponential envelopes.
All algorithms remain unrestricted; the actual oracle class requires exact upper full gradients. -/
noncomputable section
open scoped ENNReal
namespace Smoothness2601.ExactUpper

theorem finite_exponential_minimax (b : Budgets) {M Λ : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ p : ℕ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε < δ →
        ENNReal.ofReal (c*ε^(-4-2/(p:ℝ))) ≤
          minimaxComplexity b p (derivativeEnvelope b M Λ 0) ε ∧
        minimaxComplexity b p (derivativeEnvelope b M Λ 0) ε ≤
          ENNReal.ofReal (C*ε^(-4-2/(p:ℝ))) := by
  obtain ⟨c,C,δ,hc,hC,hδ,h⟩ := uniform_minimax b hgap hM hΛ (le_refl (0:ℝ))
  refine ⟨c,C,min δ 1,hc,hC,lt_min hδ zero_lt_one,?_⟩
  intro p hp ε hε hs
  have hε1 : ε ≤ 1 := hs.le.trans (min_le_right _ _)
  have hh := h p (by exact_mod_cast hp) ε hε (hs.trans_le (min_le_left _ _))
  simpa only [mul_assoc,orderTradeoff_finite_zero_rate hp hε hε1] using hh

theorem infinite_exponential_minimax (b : Budgets) {M Λ : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ENNReal.ofReal (c*ε^(-4:ℝ)) ≤
          minimaxComplexity b ⊤ (derivativeEnvelope b M Λ 0) ε ∧
        minimaxComplexity b ⊤ (derivativeEnvelope b M Λ 0) ε ≤
          ENNReal.ofReal (C*ε^(-4:ℝ)) := by
  obtain ⟨c,C,δ,hc,hC,hδ,h⟩ := uniform_minimax b hgap hM hΛ (le_refl (0:ℝ))
  refine ⟨c,C,min δ 1,hc,hC,lt_min hδ zero_lt_one,?_⟩
  intro ε hε hs
  have hε1 : ε ≤ 1 := hs.le.trans (min_le_right _ _)
  simpa only [orderTradeoff_infinite_zero hε hε1,one_pow,mul_one] using
    h ⊤ le_top ε hε (hs.trans_le (min_le_left _ _))

/-- Corollary thm:fixed, including p=1, whose additional list is empty. -/
theorem finite_list_minimax (b : Budgets) (hgap : b.μ < b.L₁)
    (p : ℕ) (hp : 1 ≤ p) (L : ℕ → ℝ)
    (hL : ∀ j, 3 ≤ j → j ≤ p+1 → 0 < L j) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ENNReal.ofReal (c*ε^(-4-2/(p:ℝ))) ≤ minimaxComplexity b p (finiteListBudget b L) ε ∧
        minimaxComplexity b p (finiteListBudget b L) ε ≤ ENNReal.ofReal (C*ε^(-4-2/(p:ℝ))) := by
  obtain ⟨m,M,hm,hM,hsand⟩ := finite_list_sandwich b p L hL
  obtain ⟨c,_C,δ,hc,_hC,hδ,hl⟩ := finite_exponential_minimax b hgap hm (by norm_num : (0:ℝ) < 1)
  obtain ⟨_c,C,η,_hc,hC,hη,hu⟩ := finite_exponential_minimax b hgap hM (by norm_num : (0:ℝ) < 1)
  refine ⟨c,C,min δ η,hc,hC,lt_min hδ hη,?_⟩
  intro ε hε hs
  exact ⟨((hl p hp ε hε (hs.trans_le (min_le_left _ _))).1).trans (hsand ε).1,
    (hsand ε).2.trans ((hu p hp ε hε (hs.trans_le (min_le_right _ _))).2)⟩

/-- The unsaturated growing-order phase, with constants uniform in finite p. -/
theorem growing_order_before_phase (b : Budgets) {M Λ β : ℝ}
    (hgap : b.μ < b.L₁) (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ p : ℕ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε < δ →
        β*p ≤ Real.log (1/ε) →
        ENNReal.ofReal (c*(p:ℝ)^(2*β)*ε^(-4-2/(p:ℝ))) ≤
          minimaxComplexity b p (derivativeEnvelope b M Λ β) ε ∧
        minimaxComplexity b p (derivativeEnvelope b M Λ β) ε ≤
          ENNReal.ofReal (C*(p:ℝ)^(2*β)*ε^(-4-2/(p:ℝ))) := by
  obtain ⟨c,C,δ,hc,hC,hδ,h⟩ := uniform_minimax b hgap hM hΛ hβ
  refine ⟨c,C,δ,hc,hC,hδ,?_⟩
  intro p hp ε hε hs hphase
  have hh := h p (by exact_mod_cast hp) ε hε hs
  rw [orderTradeoff_finite_before_minimum hp hβ hε hphase] at hh
  simpa only [mul_assoc,orderTerm_rate_identity hp hε] using hh

end Smoothness2601.ExactUpper
