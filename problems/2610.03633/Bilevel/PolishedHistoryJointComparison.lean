import Bilevel.PolishedHistoryUpperTheorem
import Bilevel.PolishedHistoryMinimaxLower
import Bilevel.ChiUniformModelTheorem

/-! The complete joint-noise bracket in the same positive-dimensional,
arbitrary-public-initialization, history-kernel minimax model. Lower and
upper inequalities use one common numerical accuracy constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
set_option autoImplicit false

/-- Both conservative and unrestricted positive-dimensional classes obey
the source uniform bracket, with constants fixed before all public budgets. -/
theorem uniform_positive_history_comparison :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ^2 → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      (ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (positiveClass (conservativeClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg))) ε ∧
       Complexity (positiveClass (conservativeClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg))) ε≤
        ENNReal.ofReal (ChiUniformModel.upperBound L κ θ σf σg Δ ε R₀)) ∧
      (ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (positiveClass (unrestrictedClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg))) ε ∧
       Complexity (positiveClass (unrestrictedClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg))) ε≤
        ENNReal.ofReal (ChiUniformModel.upperBound L κ θ σf σg Δ ε R₀)) := by
  obtain ⟨c,cq,hc,hc1,hcq,q,hlower⟩ := uniform_positive_history_both_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc
  have hκ0 : 0<κ := by linarith only [hκ]
  have hμ : 0<L/κ := div_pos hL hκ0
  have hκeq : L/(L/κ)=κ := by field_simp
  have hθeq : θ*(L/κ)/(L/κ)=θ := mul_div_cancel_right₀ θ hμ.ne'
  have hκ' : 1≤L/(L/κ) := by rw [hκeq];linarith only [hκ]
  have hθ' : 1≤θ*(L/κ)/(L/κ) := by rw [hθeq];exact hθ
  have hacc' : ε≤min L (Real.sqrt (L*Δ)) :=
    hacc.trans (mul_le_of_le_one_left (le_min hL.le (Real.sqrt_nonneg _)) hc1)
  have hl := hlower L (L/κ) κ θ Δ ε R₀ σf σg
    hL hμ hκ hκeq.symm hθ hθκ hΔ hε hR₀ hacc
  exact ⟨⟨hl.1,three_term_complexity_upper _ hL hΔ hε hθ' hκ' hacc'⟩,
    hl.2,three_term_complexity_upper _ hL hΔ hε hθ' hκ' hacc'⟩

end Bilevel.PolishedHistory
