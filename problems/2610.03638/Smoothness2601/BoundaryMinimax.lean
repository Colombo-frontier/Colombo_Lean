import Smoothness2601.BoundaryLower
import Smoothness2601.BoundaryHorizon
import Smoothness2601.BoundaryUpper
import Smoothness2601.CoordinateMinimax
import Smoothness2601.MinimaxLower
import Smoothness2601.FiniteBudgets

/-! Source prop:boundary-rate, with actual public algorithms and genuinely
fresh fixed-two-loss hard instances, for all finite and infinite caps. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Smoothness2601

theorem boundary_budget_obstruction (b : Budgets) (hμL : b.μ ≤ b.L₁)
    (p : WithTop ℕ) (L : ℕ → ℝ) (hL : ∀ j, 0 ≤ L j) {ε : ℝ} (hε : 0 < ε)
    (hεs : 8*ε ≤ BoundaryInstance.chainThreshold b) (N : ℕ)
    (hN : (N:ℝ) ≤ BoundaryInstance.finalRateConstant b*ε^(-4:ℝ)) :
    ¬BudgetWorks b p L ε N := by
  have hs : 0 < 8*ε := by positivity
  have hsmall := (BoundaryInstance.threshold_conditions b hs hεs).2.2
  obtain ⟨n,hlo,_hhi,hgap⟩ := BoundaryInstance.choose_chain b hs hεs
  have hbudget := BoundaryInstance.budget_reveal b hs hlo (BoundaryInstance.scaled_budget b hε hN)
  intro hworks
  obtain ⟨A,hA⟩ := CoordinateMinimax.budgetWorks_scalar hworks (HardProfiles.hardDimension N n)
  obtain ⟨U,hU,hfail⟩ := BoundaryInstance.fixed_frame_expected_norm hs hμL hsmall n N hbudget A
  let I := FrameTruncation.frameIsometry U hU
  have hsuccess := hA (BoundaryInstance.population I hs hμL)
    (BoundaryInstance.higherRegularity I hs hμL p L hL)
    0 0 (BoundaryInstance.initialized I hs hμL hgap) Unit inferInstance
    (BoundaryInstance.oracle I hs hμL hsmall) ()
  have hbad := hfail.trans hsuccess
  have hreal := (ENNReal.ofReal_le_ofReal_iff hε.le).mp hbad
  linarith

theorem boundary_minimax (b : Budgets) (heq : b.L₁ = b.μ) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ (p : WithTop ℕ) (L : ℕ → ℝ), (∀ j, 0 ≤ L j) →
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ENNReal.ofReal (c*ε^(-4:ℝ)) ≤ minimaxComplexity b p L ε ∧
        minimaxComplexity b p L ε ≤ ENNReal.ofReal (C*ε^(-4:ℝ)) := by
  obtain ⟨C,η,hC,hη,hu⟩ := boundary_minimax_upper b heq
  refine ⟨BoundaryInstance.finalRateConstant b,C,min (BoundaryInstance.chainThreshold b/8) η,
    BoundaryInstance.finalRateConstant_pos b,hC,
    lt_min (div_pos (BoundaryInstance.chainThreshold_pos b) (by norm_num)) hη,?_⟩
  intro p L hL ε hε hεδ
  have hεs : 8*ε ≤ BoundaryInstance.chainThreshold b := by
    have hh := hεδ.le.trans (min_le_left _ _)
    linarith
  refine ⟨?_,hu p L ε hε (hεδ.trans_le (min_le_right _ _))⟩
  apply minimax_lower_of_budget_obstruction
  intro N hN
  exact boundary_budget_obstruction b (by rw [heq]) p L hL hε hεs N hN.le

theorem boundary_envelope_minimax (b : Budgets) (heq : b.L₁ = b.μ) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ (p : WithTop ℕ) (M Λ β : ℝ), 0 < M → 0 < Λ →
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ENNReal.ofReal (c*ε^(-4:ℝ)) ≤ minimaxComplexity b p (derivativeEnvelope b M Λ β) ε ∧
        minimaxComplexity b p (derivativeEnvelope b M Λ β) ε ≤ ENNReal.ofReal (C*ε^(-4:ℝ)) := by
  obtain ⟨c,C,δ,hc,hC,hδ,h⟩ := boundary_minimax b heq
  refine ⟨c,C,δ,hc,hC,hδ,?_⟩
  intro p M Λ β hM hΛ ε hε hs
  apply h p (derivativeEnvelope b M Λ β) _ ε hε hs
  intro j
  unfold derivativeEnvelope
  split_ifs
  · exact b.L₂_pos.le
  · positivity

theorem boundary_finite_list_minimax (b : Budgets) (heq : b.L₁ = b.μ) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ (p : ℕ) (L : ℕ → ℝ), 1 ≤ p → (∀ j, 3 ≤ j → j ≤ p+1 → 0 < L j) →
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ENNReal.ofReal (c*ε^(-4:ℝ)) ≤ minimaxComplexity b p (finiteListBudget b L) ε ∧
        minimaxComplexity b p (finiteListBudget b L) ε ≤ ENNReal.ofReal (C*ε^(-4:ℝ)) := by
  obtain ⟨c,C,δ,hc,hC,hδ,h⟩ := boundary_envelope_minimax b heq
  refine ⟨c,C,δ,hc,hC,hδ,?_⟩
  intro p L _hp hL ε hε hs
  obtain ⟨m,M,hm,hM,hsand⟩ := finite_list_sandwich b p L hL
  exact ⟨((h p m 1 0 hm (by norm_num) ε hε hs).1).trans (hsand ε).1,
    (hsand ε).2.trans ((h p M 1 0 hM (by norm_num) ε hε hs).2)⟩

end Smoothness2601
