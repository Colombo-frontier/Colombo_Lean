import Bilevel.ChiCurvatureBranches

/-! All-gap coverage of the curvature-class deterministic/lower-noise
hard family. Constants are selected before every problem budget and the
accuracy window is the manuscript's min(L,kappa sqrt(L Delta)). -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.ChiCurvatureLower
open MultiscaleMean
universe u v

theorem all_gap_curvature_family : ∃ C c cq : ℝ,
    1≤C ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ L μ Δ κ θ ε σ : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ →
      1≤θ → θ≤κ → 0<ε → ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      Family.{u,v} μ L (θ*μ) Δ C κ ε σ
        (cq*(L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σ^2*Δ/ε^6)) := by
  obtain ⟨A,C₁,c₁,q₁,hA,hC₁,hc₁,hc₁1,hq₁,hsmall⟩ := bounded_gap_family.{u,v}
  let Θ := max (2*A) 3200
  have hΘ : 2≤Θ := le_trans (by norm_num) (le_max_right _ _)
  obtain ⟨C₂,c₂,q₂,hC₂,hc₂,hc₂1,hq₂,hbounded⟩ := bounded_kappa_family.{u,v} Θ hΘ
  obtain ⟨C₃,c₃,q₃,hC₃,hc₃,hc₃1,hq₃,hlarge⟩ := large_gap_family.{u,v}
  let C := max C₁ (max C₂ C₃)
  let c := min c₁ (min c₂ c₃)
  let cq := min q₁ (min q₂ q₃)
  have hC1 : C₁≤C := le_max_left _ _
  have hC2 : C₂≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : C₃≤C := (le_max_right _ _).trans (le_max_right _ _)
  have hc1 : c≤c₁ := min_le_left _ _
  have hc2 : c≤c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hc3 : c≤c₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hq1 : cq≤q₁ := min_le_left _ _
  have hq2 : cq≤q₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hq3 : cq≤q₃ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C,c,cq,hC₁.trans hC1,lt_min hc₁ (lt_min hc₂ hc₃),hc1.trans hc₁1,
    lt_min hq₁ (lt_min hq₂ hq₃),?_⟩
  intro L μ Δ κ θ ε σ hL hμ hκeq hΔ hκ hθ hθκ hε hacc
  have hwindow : 0≤min L (κ*Real.sqrt (L*Δ)) := by positivity
  have hrate : 0≤ innerRate L Δ κ θ ε σ := by dsimp [innerRate];positivity
  change Family μ L (θ*μ) Δ C κ ε σ (cq*innerRate L Δ κ θ ε σ)
  by_cases hboundedκ : κ≤Θ
  · exact family_mono hL.le hC2 (mul_le_mul_of_nonneg_right hq2 hrate)
      (hbounded L μ Δ κ θ ε σ hL hμ hκeq hΔ hκ hboundedκ hθ hθκ hε
        (hacc.trans (mul_le_mul_of_nonneg_right hc2 hwindow)))
  · have hlargeκ : 2*A≤κ := (le_max_left _ _).trans (le_of_not_ge hboundedκ)
    by_cases hsmallΔ : Δ≤L
    · exact family_mono hL.le hC1 (mul_le_mul_of_nonneg_right hq1 hrate)
        (hsmall L μ Δ κ θ ε σ hL hμ hκeq hΔ hsmallΔ hlargeκ hθ hθκ hε
          (hacc.trans (mul_le_mul_of_nonneg_right hc1 hwindow)))
    · have haccL : ε≤c₃*L :=
        (hacc.trans (mul_le_mul_of_nonneg_right hc3 hwindow)).trans
          (mul_le_mul_of_nonneg_left (min_le_left _ _) hc₃.le)
      exact family_mono hL.le hC3 (mul_le_mul_of_nonneg_right hq3 hrate)
        (hlarge L μ Δ κ θ ε σ hL hμ hκeq (le_of_not_ge hsmallΔ) hκ hθ hθκ hε haccL)

end Bilevel.ChiCurvatureLower
