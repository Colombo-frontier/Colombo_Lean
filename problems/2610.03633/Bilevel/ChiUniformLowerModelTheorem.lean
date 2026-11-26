import Bilevel.ChiDeterministicModelTheorem
import Bilevel.ChiLowerNoiseModelTheorem
import Bilevel.ChiUpperNoiseModelTheorem
import Bilevel.PrimitiveQueryAssembly
import Bilevel.PrimitiveQueryClassMonotonicity

/-! The lower half of thm:joint-noise-comparison in one actual original-SFO
minimax model. All three numerical family theorems are discharged, including
the positive-depth deterministic transport factor. Constants and the finite
logarithmic exponent precede all public budgets and both noise bounds. -/
noncomputable section
namespace Bilevel.ChiUniformLower
open PrimitiveQuery ChiRefinementRates ChiExtensionCalibration
set_option autoImplicit false

def lowerBracket (q : ℕ) (L κ θ σf σg Δ ε : ℝ) : ℝ :=
  upperNoise L κ σf Δ ε+
    (deterministic L θ κ Δ ε+lowerNoise L θ κ σg Δ ε)/(Real.log (2+θ))^q

theorem uniform_conservative_minimax_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L μ κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 1≤θ → θ≤κ^2 →
      0<Δ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      ENNReal.ofReal (cq*lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (conservativeClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg)) ε := by
  obtain ⟨cD,cqD,hcD,hcD1,hcqD,qD,hD⟩ := deterministic_model_hardness
  obtain ⟨cU,cqU,hcU,hcU1,hcqU,hU⟩ := ChiUpperNoise.upper_noise_model_hardness
  obtain ⟨cG,cqG,hcG,hcG1,hcqG,qG,hG⟩ := lower_noise_model_hardness
  let c := min cD (min cU cG)
  have hcD' : c≤cD := min_le_left _ _
  have hcU' : c≤cU := (min_le_right _ _).trans (min_le_left _ _)
  have hcG' : c≤cG := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c,min cqD (min cqU cqG)/3,lt_min hcD (lt_min hcU hcG),hcD'.trans hcD1,
    div_pos (lt_min hcqD (lt_min hcqU hcqG)) (by norm_num),max qD qG,?_⟩
  intro L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc
  have hw : 0≤min L (Real.sqrt (L*Δ)) := le_min hL.le (Real.sqrt_nonneg _)
  have hθ0 : 0≤θ := by linarith only [hθ]
  have hd := hD L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀
    (hacc.trans (mul_le_mul_of_nonneg_right hcD' hw))
  have hu := hU L μ κ (θ*μ) Δ ε R₀ σf σg hL hμ hκ hκeq
    (mul_nonneg hθ0 hμ.le) hΔ hε hR₀ (hacc.trans (mul_le_mul_of_nonneg_right hcU' hw))
  have hg := hG L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀
    (hacc.trans (mul_le_mul_of_nonneg_right hcG' hw))
  exact three_family_minimax _ ε
    (deterministic_nonneg hL.le hθ0 hΔ.le) (upperNoise_nonneg hL.le hΔ.le)
    (lowerNoise_nonneg hL.le hθ0 hΔ.le) hcqD hcqU hcqG
    (ChiMinimax.logarithm_ge_one hθ) hd hu hg

theorem uniform_minimax_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L μ κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 1≤θ → θ≤κ^2 →
      0<Δ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      ENNReal.ofReal (cq*lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (unrestrictedClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg)) ε := by
  obtain ⟨c,cq,hc,hc1,hcq,q,h⟩ := uniform_conservative_minimax_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc
  exact (h L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc).trans
    (complexity_mono_class _ _ ε (fun _ _ _ => True.intro))

/-- Literal normalization mu=L/kappa, with both source classes in the same
conclusion and the same universal constants and accuracy window. -/
theorem uniform_both_classes_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ^2 → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      ENNReal.ofReal (cq*lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (conservativeClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg)) ε ∧
      ENNReal.ofReal (cq*lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (unrestrictedClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg)) ε := by
  obtain ⟨c,cq,hc,hc1,hcq,q,h⟩ := uniform_conservative_minimax_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc
  have hκ0 : 0<κ := by linarith only [hκ]
  have hκeq : κ=L/(L/κ) := by field_simp
  have hc := h L (L/κ) κ θ Δ ε R₀ σf σg hL (div_pos hL hκ0) hκ hκeq hθ hθκ hΔ hε hR₀ hacc
  exact ⟨hc,hc.trans (complexity_mono_class _ _ ε (fun _ _ _ => True.intro))⟩

end Bilevel.ChiUniformLower
