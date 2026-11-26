import Bilevel.ChiCurvatureAllGap
import Bilevel.ChiCurvatureInnerModel
import Bilevel.ChiCurvatureCanonicalModel

/-! All-gap curvature-class lower bound in the actual original-SFO model.
Every lower sample is conservative; upper and lower full gradients use
one fresh original call. The geometry is public and fixed before the
algorithm, and the construction has zero lower initialization error. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.ChiCurvatureLower
open PrimitiveQuery

theorem family_hardness {μ L ρ Δ C κ ε σg cost R₀ σf : ℝ}
    (hR₀ : 0≤R₀) (h : Family.{0,0} μ L ρ Δ C κ ε σg cost) :
    Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
      (R₀:=R₀) (σf:=σf) (σg:=σg) (C*L*κ^2)) ε cost :=
  h.elim (innerFamily_hardness hR₀) (canonicalFamily_hardness hR₀)

theorem all_gap_curvature_hardness : ∃ C c cq : ℝ,
    1≤C ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ L μ Δ κ θ ε R₀ σf σg : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ →
      1≤θ → θ≤κ → 0<ε → 0≤R₀ → ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ)
        (R₀:=R₀) (σf:=σf) (σg:=σg) (C*L*κ^2)) ε
        (cq*(L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σg^2*Δ/ε^6)) := by
  obtain ⟨C,c,cq,hC,hc,hc1,hcq,hfamily⟩ := all_gap_curvature_family.{0,0}
  refine ⟨C,c,cq,hC,hc,hc1,hcq,?_⟩
  intro L μ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hε hR₀ hacc
  exact family_hardness hR₀ (hfamily L μ Δ κ θ ε σg hL hμ hκeq hΔ hκ hθ hθκ hε hacc)

theorem all_gap_curvature_minimax : ∃ C c cq : ℝ,
    1≤C ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ L μ Δ κ θ ε R₀ σf σg : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ →
      1≤θ → θ≤κ → 0<ε → 0≤R₀ → ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      ENNReal.ofReal (cq*(L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σg^2*Δ/ε^6))≤
        Complexity (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg) (C*L*κ^2)) ε := by
  obtain ⟨C,c,cq,hC,hc,hc1,hcq,hfamily⟩ := all_gap_curvature_hardness
  refine ⟨C,c,cq,hC,hc,hc1,hcq,?_⟩
  intro L μ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hε hR₀ hacc
  exact (hfamily L μ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hε hR₀ hacc).minimax

end Bilevel.ChiCurvatureLower
