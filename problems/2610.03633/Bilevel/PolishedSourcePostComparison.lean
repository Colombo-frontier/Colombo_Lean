import Bilevel.PolishedSourcePostCurvatureUpper
import Bilevel.PolishedHistorySourcePostCurvatureLower

/-! Final source-probability comparisons. Both bounds use the SAME minimax
value over actual conditional-moment experiments, positive finite dimensions,
arbitrary randomized query bodies and independent terminal selection. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.PolishedHistory
set_option autoImplicit false

theorem uniform_source_comparison :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ^2 → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) → ∀ conservative : Bool,
      (ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        restrictedPostComplexity (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)
          (positiveSourceClass (fun _ _ => True)) conservative ε) ∧
      (restrictedPostComplexity (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)
          (positiveSourceClass (fun _ _ => True)) conservative ε≤
        ENNReal.ofReal (CachedUpper.threeRateBound L (L/κ) L L L (θ*(L/κ)) σf σg Δ ε R₀)) := by
  obtain ⟨c,cq,hc,hc1,hcq,q,hlower⟩ := uniform_positive_post_source_classes_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc conservative
  have hκ0 : 0<κ := by linarith
  have hμ : 0<L/κ := div_pos hL hκ0
  have hκeq : L/(L/κ)=κ := by field_simp
  have hθeq : θ*(L/κ)/(L/κ)=θ := mul_div_cancel_right₀ θ hμ.ne'
  have hκ' : 1≤L/(L/κ) := by rw [hκeq];linarith
  have hθ' : 1≤θ*(L/κ)/(L/κ) := by rw [hθeq];exact hθ
  have hacc' : ε≤min L (Real.sqrt (L*Δ)) :=
    hacc.trans (mul_le_of_le_one_left (le_min hL.le (Real.sqrt_nonneg _)) hc1)
  exact ⟨hlower L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc conservative,
    source_post_restricted_three_term_upper _ conservative hL hΔ hε hθ' hκ' hacc'⟩

theorem curvature_source_comparison :
    ∃ C₀ c cq : ℝ,4≤C₀ ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ CF : ℝ,C₀≤CF →
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) → ∀ conservative : Bool,
      (ENNReal.ofReal (cq*ChiCurvatureLower.curvatureBracket L κ θ σf σg Δ ε)≤
        restrictedPostComplexity (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)
          (positiveSourceClass (sourceCurvatureClass (CF*L*κ^2))) conservative ε) ∧
      (restrictedPostComplexity (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)
          (positiveSourceClass (sourceCurvatureClass (CF*L*κ^2))) conservative ε≤
        ENNReal.ofReal (curvatureUpperBound L κ θ σf σg Δ ε R₀ CF)) := by
  obtain ⟨C₀,c,cq,hC,hc,hc1,hcq,hlower⟩ := positive_post_source_curvature_three_term_lower
  refine ⟨C₀,c,cq,hC,hc,hc1,hcq,?_⟩
  intro CF hCF L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc conservative
  have hκ0 : 0<κ := by linarith
  have hμ : 0<L/κ := div_pos hL hκ0
  have hκeq : L/(L/κ)=κ := by field_simp
  have hθeq : θ*(L/κ)/(L/κ)=θ := mul_div_cancel_right₀ θ hμ.ne'
  have hκ' : 1≤L/(L/κ) := by rw [hκeq];linarith
  have hθ' : 1≤θ*(L/κ)/(L/κ) := by rw [hθeq];exact hθ
  have hacc' : ε≤min L (Real.sqrt (L*Δ)) :=
    hacc.trans (mul_le_of_le_one_left (le_min hL.le (Real.sqrt_nonneg _)) hc1)
  have hcert : CF*L*κ^2≤CF*L*(L/(L/κ))^2 := by rw [hκeq]
  exact ⟨hlower CF hCF L (L/κ) (θ*(L/κ)) Δ κ θ ε R₀ σf σg
      hL hμ hκeq.symm hΔ hκ hθ hθκ le_rfl hε hR₀ hacc conservative,
    source_post_curvature_complexity_upper _ conservative hL hΔ hε hκ' hθ' hacc' hcert
      (fun _ _ h => h.1)⟩

end Bilevel.PolishedHistory
