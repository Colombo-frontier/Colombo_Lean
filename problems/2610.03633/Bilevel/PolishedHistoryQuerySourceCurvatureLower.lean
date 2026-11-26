import Bilevel.PolishedHistoryQuerySourceLower
import Bilevel.ChiCurvatureThreeTermLower

/-! Concrete curvature and all-gap lower bounds on the same query-adapted source
postselection model used by its upper bound, with positive source dimensions. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.PolishedHistory
set_option autoImplicit false

theorem positive_query_source_curvature_three_term_lower : ∃ C₀ c cq : ℝ,
    4≤C₀ ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ C_F : ℝ,C₀≤C_F →
    ∀ L μ ρ Δ κ θ ε R₀ σf σg : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ →
      1≤θ → θ≤κ → θ*μ≤ρ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      ∀ conservative : Bool,
      ENNReal.ofReal (cq*ChiCurvatureLower.curvatureBracket L κ θ σf σg Δ ε)≤
        queryPostComplexity (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)
          (positiveSourceClass (sourceCurvatureClass (C_F*L*κ^2))) conservative ε := by
  obtain ⟨C₀,c,cq,hC,hc,hc1,hcq,h⟩ := ChiCurvatureLower.curvature_three_term_conservative_minimax
  refine ⟨C₀,c,cq,hC,hc,hc1,hcq,?_⟩
  intro C_F hCF L μ ρ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hθρ hε hR₀ hacc conservative
  exact (h C_F hCF L μ ρ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hθρ hε hR₀ hacc).trans
    (stationary_curvature_le_positive_query_source _ conservative ε)

theorem positive_query_source_all_gap_curvature_lower : ∃ C₀ c cq : ℝ,
    1≤C₀ ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ C_F : ℝ,C₀≤C_F →
    ∀ L μ ρ Δ κ ε R₀ σf σg : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ → μ≤ρ →
      0<ε → 0≤R₀ → ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      ∀ conservative : Bool,
      let θ := min (ρ/μ) κ
      ENNReal.ofReal (cq*(L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σg^2*Δ/ε^6))≤
        queryPostComplexity (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)
          (positiveSourceClass (sourceCurvatureClass (C_F*L*κ^2))) conservative ε := by
  obtain ⟨C₀,c,cq,hC,hc,hc1,hcq,h⟩ := ChiCurvatureLower.all_gap_curvature_class_minimax
  refine ⟨C₀,c,cq,hC,hc,hc1,hcq,?_⟩
  intro C_F hCF L μ ρ Δ κ ε R₀ σf σg hL hμ hκeq hΔ hκ hρ hε hR₀ hacc conservative
  exact (h C_F hCF L μ ρ Δ κ ε R₀ σf σg hL hμ hκeq hΔ hκ hρ hε hR₀ hacc).trans
    (stationary_curvature_le_positive_query_source _ conservative ε)

end Bilevel.PolishedHistory
