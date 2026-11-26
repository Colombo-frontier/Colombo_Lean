import Bilevel.ChiCurvatureLowerTheorem
import Bilevel.PrimitiveQueryVariation

/-! The same all-gap hard instances fit any prescribed variation budget
above theta*mu. In particular theta=min(rho/mu,kappa) is admissible. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.ChiCurvatureLower
open PrimitiveQuery

theorem all_gap_prescribed_variation_hardness : ∃ C c cq : ℝ,
    1≤C ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ L μ ρ Δ κ θ ε R₀ σf σg : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ →
      1≤θ → θ≤κ → θ*μ≤ρ → 0<ε → 0≤R₀ → ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
        (R₀:=R₀) (σf:=σf) (σg:=σg) (C*L*κ^2)) ε
        (cq*(L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σg^2*Δ/ε^6)) := by
  obtain ⟨C,c,cq,hC,hc,hc1,hcq,hmain⟩ := all_gap_curvature_hardness
  refine ⟨C,c,cq,hC,hc,hc1,hcq,?_⟩
  intro L μ ρ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hθρ hε hR₀ hacc
  exact (hmain L μ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hε hR₀ hacc).enlargeVariation_conservativeCurvature hθρ

theorem all_gap_capped_theta_minimax : ∃ C c cq : ℝ,
    1≤C ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ L μ ρ Δ κ ε R₀ σf σg : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ → μ≤ρ →
      0<ε → 0≤R₀ → ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      let θ := min (ρ/μ) κ
      ENNReal.ofReal (cq*(L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σg^2*Δ/ε^6))≤
        Complexity (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg) (C*L*κ^2)) ε := by
  obtain ⟨C,c,cq,hC,hc,hc1,hcq,hmain⟩ := all_gap_prescribed_variation_hardness
  refine ⟨C,c,cq,hC,hc,hc1,hcq,?_⟩
  intro L μ ρ Δ κ ε R₀ σf σg hL hμ hκeq hΔ hκ hρ hε hR₀ hacc
  dsimp only
  have hθ : 1≤min (ρ/μ) κ := le_min ((one_le_div hμ).mpr hρ) (by linarith)
  have hθρ : min (ρ/μ) κ*μ≤ρ := by
    calc
      min (ρ/μ) κ*μ≤(ρ/μ)*μ := mul_le_mul_of_nonneg_right (min_le_left _ _) hμ.le
      _=ρ := div_mul_cancel₀ _ hμ.ne'
  exact (hmain L μ ρ Δ κ (min (ρ/μ) κ) ε R₀ σf σg hL hμ hκeq hΔ hκ hθ
    (min_le_right _ _) hθρ hε hR₀ hacc).minimax

end Bilevel.ChiCurvatureLower
