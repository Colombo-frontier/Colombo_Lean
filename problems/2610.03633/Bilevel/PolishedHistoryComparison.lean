import Bilevel.PolishedFrozenCurvatureUpper
import Bilevel.PolishedHistoryCurvatureLower
import Bilevel.ChiUniformModelTheorem

/-! Same-class comparisons for actual arbitrary-history kernel experiments.
The upper witnesses are the literal source algorithm. Stationary hard
families supply the lower bounds via the proved actual stopping bridge.
Abstract conditional-probability-space upper semantics are proved separately. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.PolishedHistory
set_option autoImplicit false

theorem uniform_history_comparison :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ^2 → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      (ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (positiveClass (conservativeClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ))
          (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg))) ε ∧
       Complexity (positiveClass (conservativeClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ))
          (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg))) ε≤
        ENNReal.ofReal (ChiUniformModel.upperBound L κ θ σf σg Δ ε R₀)) ∧
      (ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (positiveClass (unrestrictedClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ))
          (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg))) ε ∧
       Complexity (positiveClass (unrestrictedClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ))
          (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg))) ε≤
        ENNReal.ofReal (ChiUniformModel.upperBound L κ θ σf σg Δ ε R₀)) := by
  obtain ⟨c,cq,hc,hc1,hcq,q,hlower⟩ := uniform_positive_history_both_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc
  have hκ0 : 0<κ := by linarith
  have hμ : 0<L/κ := div_pos hL hκ0
  have hκeq : L/(L/κ)=κ := by field_simp
  have hθeq : θ*(L/κ)/(L/κ)=θ := mul_div_cancel_right₀ θ hμ.ne'
  have hκ' : 1≤L/(L/κ) := by rw [hκeq];linarith
  have hθ' : 1≤θ*(L/κ)/(L/κ) := by rw [hθeq];exact hθ
  have hacc' : ε≤min L (Real.sqrt (L*Δ)) :=
    hacc.trans (mul_le_of_le_one_left (le_min hL.le (Real.sqrt_nonneg _)) hc1)
  have hl := hlower L (L/κ) κ θ Δ ε R₀ σf σg hL hμ hκ hκeq.symm hθ hθκ hΔ hε hR₀ hacc
  exact ⟨⟨hl.1,source_frozen_three_term_complexity_upper _ hL hΔ hε hθ' hκ' hacc'⟩,
    hl.2,source_frozen_three_term_complexity_upper _ hL hΔ hε hθ' hκ' hacc'⟩

def curvatureUpperBound (L κ θ σf σg Δ ε R₀ C_F : ℝ) : ℝ :=
  CachedUpper.controlledThreeRateBound L (L/κ) L L L (θ*(L/κ)) σf σg
    (CachedUpper.controlledCurvature L (L/κ) L L (C_F*L*κ^2))
    (CachedUpper.controlledConstant C_F) Δ ε R₀

theorem curvature_history_comparison :
    ∃ C₀ c cq : ℝ,4≤C₀ ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ C_F : ℝ,C₀≤C_F →
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      (ENNReal.ofReal (cq*ChiCurvatureLower.curvatureBracket L κ θ σf σg Δ ε)≤
        Complexity (positiveClass (conservativeCurvatureClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ))
          (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) (C_F*L*κ^2))) ε ∧
       Complexity (positiveClass (conservativeCurvatureClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ))
          (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) (C_F*L*κ^2))) ε≤
        ENNReal.ofReal (curvatureUpperBound L κ θ σf σg Δ ε R₀ C_F)) ∧
      (ENNReal.ofReal (cq*ChiCurvatureLower.curvatureBracket L κ θ σf σg Δ ε)≤
        Complexity (positiveClass (curvatureClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ))
          (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) (C_F*L*κ^2))) ε ∧
       Complexity (positiveClass (curvatureClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ))
          (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) (C_F*L*κ^2))) ε≤
        ENNReal.ofReal (curvatureUpperBound L κ θ σf σg Δ ε R₀ C_F)) := by
  obtain ⟨C₀,c,cq,hC,hc,hc1,hcq,hlower⟩ := positive_history_curvature_three_term_lower
  refine ⟨C₀,c,cq,hC,hc,hc1,hcq,?_⟩
  intro C_F hCF L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc
  have hκ0 : 0<κ := by linarith
  have hμ : 0<L/κ := div_pos hL hκ0
  have hκeq : L/(L/κ)=κ := by field_simp
  have hθeq : θ*(L/κ)/(L/κ)=θ := mul_div_cancel_right₀ θ hμ.ne'
  have hκ' : 1≤L/(L/κ) := by rw [hκeq];linarith
  have hθ' : 1≤θ*(L/κ)/(L/κ) := by rw [hθeq];exact hθ
  have hacc' : ε≤min L (Real.sqrt (L*Δ)) :=
    hacc.trans (mul_le_of_le_one_left (le_min hL.le (Real.sqrt_nonneg _)) hc1)
  have hcert : C_F*L*κ^2≤C_F*L*(L/(L/κ))^2 := by rw [hκeq]
  have hl := hlower C_F hCF L (L/κ) (θ*(L/κ)) Δ κ θ ε R₀ σf σg
    hL hμ hκeq.symm hΔ hκ hθ hθκ le_rfl hε hR₀ hacc
  have hmono := complexity_mono_class
    (positiveClass (conservativeCurvatureClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ))
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) (C_F*L*κ^2)))
    (positiveClass (curvatureClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ))
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) (C_F*L*κ^2))) ε
    (fun _ _ h => ⟨h.1.2,h.2⟩)
  exact ⟨⟨hl,source_frozen_curvature_complexity_upper _ hL hΔ hε hκ' hθ' hacc' hcert
    (fun _ _ h => h.1.2)⟩,
    hl.trans hmono,source_frozen_curvature_complexity_upper _ hL hΔ hε hκ' hθ' hacc' hcert
      (fun _ _ h => h.1)⟩

end Bilevel.PolishedHistory
