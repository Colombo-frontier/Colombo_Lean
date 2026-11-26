import Bilevel.PolishedHistoryMinimaxLower
import Bilevel.ChiCurvatureThreeTermLower

/-! Source-positive dimensional curvature-class lower bounds in the actual
history-kernel model, with arbitrary supplied initialization. All concrete
stationary families, their curvature budgets and uniform numerical constants
are inherited through the proved operational stopping bridge. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery
set_option autoImplicit false
variable {μ L ρ Δ R₀ σf σg : ℝ}

theorem stationary_conservative_curvature_le_positive_history (Λ ε : ℝ) :
    PrimitiveQuery.Complexity (PrimitiveQuery.conservativeCurvatureClass
      (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) Λ) ε≤
    Complexity (positiveClass (conservativeCurvatureClass
      (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) Λ)) ε := by
  apply (stationary_complexity_le_positive _ ε).trans
  exact stationary_complexity_le_history _ _ ε
    (fun _ I hI => ⟨⟨ofStationary_isConservative I hI.1.1,
      (ofStationary_curvature_iff I Λ).mpr hI.1.2⟩,hI.2⟩)

theorem positive_history_curvature_three_term_lower : ∃ C₀ c cq : ℝ,
    4≤C₀ ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ C_F : ℝ,C₀≤C_F →
    ∀ L μ ρ Δ κ θ ε R₀ σf σg : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ →
      1≤θ → θ≤κ → θ*μ≤ρ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      ENNReal.ofReal (cq*ChiCurvatureLower.curvatureBracket L κ θ σf σg Δ ε)≤
        Complexity (positiveClass (conservativeCurvatureClass
          (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) (C_F*L*κ^2))) ε := by
  obtain ⟨C₀,c,cq,hC,hc,hc1,hcq,h⟩ := ChiCurvatureLower.curvature_three_term_conservative_minimax
  refine ⟨C₀,c,cq,hC,hc,hc1,hcq,?_⟩
  intro C_F hCF L μ ρ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hθρ hε hR₀ hacc
  exact (h C_F hCF L μ ρ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hθρ hε hR₀ hacc).trans
    (stationary_conservative_curvature_le_positive_history _ ε)

theorem positive_history_all_gap_curvature_lower : ∃ C₀ c cq : ℝ,
    1≤C₀ ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ C_F : ℝ,C₀≤C_F →
    ∀ L μ ρ Δ κ ε R₀ σf σg : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ → μ≤ρ →
      0<ε → 0≤R₀ → ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      let θ := min (ρ/μ) κ
      ENNReal.ofReal (cq*(L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σg^2*Δ/ε^6))≤
        Complexity (positiveClass (conservativeCurvatureClass
          (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg) (C_F*L*κ^2))) ε := by
  obtain ⟨C₀,c,cq,hC,hc,hc1,hcq,h⟩ := ChiCurvatureLower.all_gap_curvature_class_minimax
  refine ⟨C₀,c,cq,hC,hc,hc1,hcq,?_⟩
  intro C_F hCF L μ ρ Δ κ ε R₀ σf σg hL hμ hκeq hΔ hκ hρ hε hR₀ hacc
  exact (h C_F hCF L μ ρ Δ κ ε R₀ σf σg hL hμ hκeq hΔ hκ hρ hε hR₀ hacc).trans
    (stationary_conservative_curvature_le_positive_history _ ε)

end Bilevel.PolishedHistory
