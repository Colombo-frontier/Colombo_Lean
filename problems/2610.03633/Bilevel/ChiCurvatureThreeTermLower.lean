import Bilevel.ChiCurvatureClassTheorem
import Bilevel.ChiUpperNoiseModelTheorem
import Bilevel.TransportQuadraticUniformModel
import Bilevel.PrimitiveQueryAssembly
import Bilevel.PrimitiveQueryClassMonotonicity

/-! The three-family lower half of cor:curvature-controlled in the actual
original-SFO minimax model. One fixed sufficiently large curvature constant
contains all three families; no execution or information premise remains. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.ChiCurvatureLower
open PrimitiveQuery

def curvatureBracket (L κ θ σf σg Δ ε : ℝ) : ℝ :=
  L*κ^2*Real.sqrt κ*Δ/ε^2+L*κ^4*σf^2*Δ/ε^4+L^3*θ^2*κ^8*σg^2*Δ/ε^6

theorem curvature_three_term_conservative_minimax : ∃ C₀ c cq : ℝ,
    4≤C₀ ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ C_F : ℝ,C₀≤C_F →
    ∀ L μ ρ Δ κ θ ε R₀ σf σg : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ →
      1≤θ → θ≤κ → θ*μ≤ρ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      ENNReal.ofReal (cq*curvatureBracket L κ θ σf σg Δ ε)≤
        Complexity (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg) (C_F*L*κ^2)) ε := by
  obtain ⟨CG,cG,qG,hCG,hcG,hcG1,hqG,hG⟩ := all_gap_curvature_class_hardness
  obtain ⟨cD,qD,hcD,hcD1,hqD,hD⟩ := TransportHierarchy.quadratic_model_hardness
  obtain ⟨cU,qU,hcU,hcU1,hqU,hU⟩ := ChiUpperNoise.upper_noise_curvature_hardness
  let C₀ := max CG 4
  let c := min cD (min cU cG)
  let cq := min qD (min qU qG)/3
  have hcD' : c≤cD := min_le_left _ _
  have hcU' : c≤cU := (min_le_right _ _).trans (min_le_left _ _)
  have hcG' : c≤cG := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C₀,c,cq,le_max_right _ _,lt_min hcD (lt_min hcU hcG),hcD'.trans hcD1,
    div_pos (lt_min hqD (lt_min hqU hqG)) (by norm_num),?_⟩
  intro C_F hCF L μ ρ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hθρ hε hR₀ hacc
  have hρ : 0≤ρ := (mul_nonneg (by linarith only [hθ]) hμ.le).trans hθρ
  have hCF4 : 4≤C_F := (le_max_right _ _).trans hCF
  have hCF1 : 1≤C_F := by linarith only [hCF4]
  have hCFg : CG≤C_F := (le_max_left _ _).trans hCF
  have hw : 0≤min L (Real.sqrt (L*Δ)) := le_min hL.le (Real.sqrt_nonneg _)
  have haccD := hacc.trans (mul_le_mul_of_nonneg_right hcD' hw)
  have haccU := hacc.trans (mul_le_mul_of_nonneg_right hcU' hw)
  have haccG : ε≤cG*min L (κ*Real.sqrt (L*Δ)) := by
    apply (hacc.trans (mul_le_mul_of_nonneg_right hcG' hw)).trans
    apply mul_le_mul_of_nonneg_left _ hcG.le
    exact min_le_min (le_refl _) (le_mul_of_one_le_left (Real.sqrt_nonneg _) (by linarith only [hκ]))
  have hd := (hD L μ κ ρ Δ ε R₀ σf σg hL hμ hκ hκeq hρ hΔ hε hR₀ haccD).enlargeConservativeCurvature (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCF4 hL.le) (sq_nonneg κ))
  have hu := (hU L μ κ ρ Δ ε R₀ σf σg hL hμ hκ hκeq hρ hΔ hε hR₀ haccU).enlargeConservativeCurvature (mul_le_mul_of_nonneg_right
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hCF1 hL.le)) (sq_nonneg κ))
  have hg := (hG C_F hCFg L μ ρ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hθρ hε hR₀ haccG).mono (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left
      (by positivity : 0≤L*κ^2*Δ/ε^2)) hqG.le)
  exact three_family_minimax_no_log _ ε
    (by positivity : 0≤L*κ^2*Real.sqrt κ*Δ/ε^2)
    (by positivity : 0≤L*κ^4*σf^2*Δ/ε^4)
    (by positivity : 0≤L^3*θ^2*κ^8*σg^2*Δ/ε^6)
    hqD hqU hqG hd hu hg

theorem curvature_three_term_minimax : ∃ C₀ c cq : ℝ,
    4≤C₀ ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ C_F : ℝ,C₀≤C_F →
    ∀ L μ ρ Δ κ θ ε R₀ σf σg : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ →
      1≤θ → θ≤κ → θ*μ≤ρ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      ENNReal.ofReal (cq*curvatureBracket L κ θ σf σg Δ ε)≤
        Complexity (curvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg) (C_F*L*κ^2)) ε := by
  obtain ⟨C₀,c,cq,hC,hc,hc1,hcq,hmain⟩ := curvature_three_term_conservative_minimax
  refine ⟨C₀,c,cq,hC,hc,hc1,hcq,?_⟩
  intro C_F hCF L μ ρ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hθρ hε hR₀ hacc
  exact (hmain C_F hCF L μ ρ Δ κ θ ε R₀ σf σg hL hμ hκeq hΔ hκ hθ hθκ hθρ hε hR₀ hacc).trans (conservative_curvature_complexity_le _ _)

theorem curvature_three_term_capped_theta_minimax : ∃ C₀ c cq : ℝ,
    4≤C₀ ∧ 0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ C_F : ℝ,C₀≤C_F →
    ∀ L μ ρ Δ κ ε R₀ σf σg : ℝ,0<L → 0<μ → κ=L/μ → 0<Δ → 2≤κ → μ≤ρ →
      0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      ENNReal.ofReal (cq*curvatureBracket L κ (min (ρ/μ) κ) σf σg Δ ε)≤
        Complexity (curvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg) (C_F*L*κ^2)) ε := by
  obtain ⟨C₀,c,cq,hC,hc,hc1,hcq,hmain⟩ := curvature_three_term_minimax
  refine ⟨C₀,c,cq,hC,hc,hc1,hcq,?_⟩
  intro C_F hCF L μ ρ Δ κ ε R₀ σf σg hL hμ hκeq hΔ hκ hρ hε hR₀ hacc
  have hθ : 1≤min (ρ/μ) κ := le_min ((one_le_div hμ).mpr hρ) (by linarith only [hκ])
  have hθρ : min (ρ/μ) κ*μ≤ρ := by
    calc
      min (ρ/μ) κ*μ≤(ρ/μ)*μ := mul_le_mul_of_nonneg_right (min_le_left _ _) hμ.le
      _=ρ := div_mul_cancel₀ _ hμ.ne'
  exact hmain C_F hCF L μ ρ Δ κ (min (ρ/μ) κ) ε R₀ σf σg hL hμ hκeq hΔ hκ
    hθ (min_le_right _ _) hθρ hε hR₀ hacc

end Bilevel.ChiCurvatureLower
