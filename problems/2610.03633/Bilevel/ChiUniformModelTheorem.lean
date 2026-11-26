import Bilevel.ChiUniformLowerModelTheorem
import Bilevel.PrimitiveQueryUpperTheorem

/-! Two-sided uniform complexity comparison in the stationary fresh-law
`PrimitiveQuery` model. The upper bound is witnessed by one public causal
solver independent of the hidden primitive and its seed law. Both exact
executed logarithmic factors remain visible in `upperBound_eq_rates`.

This theorem does not identify this stationary model with the manuscript's
broader history-dependent conditional-SFO interface. That additional bridge
is a separate obligation.
-/
noncomputable section
namespace Bilevel.ChiUniformModel
open PrimitiveQuery ChiRefinementRates ChiUniformLower
set_option autoImplicit false

def upperBound (L κ θ σf σg Δ ε R₀ : ℝ) : ℝ :=
  CachedUpper.threeRateBound L (L/κ) L L L (θ*(L/κ)) σf σg Δ ε R₀

/-- Exact D+U+G expansion with the public confidence count and initialization
logarithm used by the actual upper solver; no asymptotic premise is assumed. -/
theorem upperBound_eq_rates {L κ : ℝ} (hL : 0<L) (hκ : 0<κ)
    (θ σf σg Δ ε R₀ : ℝ) :
    upperBound L κ θ σf σg Δ ε R₀=
      (100000000000000*98304)*
        CachedUpper.repetitions (CachedUpper.universalCurvature L (L/κ) L L L (θ*(L/κ))) Δ ε*
        max 1 (CachedUpper.normalizedLog L (L/κ) L L L (θ*(L/κ)) Δ ε R₀)*
        (deterministic L θ κ Δ ε+upperNoise L κ σf Δ ε+lowerNoise L θ κ σg Δ ε) := by
  have hμ : L/κ≠0 := (div_pos hL hκ).ne'
  have hθeq : θ*(L/κ)/(L/κ)=θ := mul_div_cancel_right₀ θ hμ
  have hκeq : L/(L/κ)=κ := by field_simp
  simp only [upperBound,CachedUpper.threeRateBound,hθeq,hκeq]

/-- Same numerical constants and accuracy window for both stationary
fresh-law classes, at the source normalization mu=L/kappa, rho=theta*mu. -/
theorem uniform_stationary_comparison :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 2≤κ → 1≤θ → θ≤κ^2 → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      (ENNReal.ofReal (cq*lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (conservativeClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg)) ε ∧
       Complexity (conservativeClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg)) ε≤
        ENNReal.ofReal (upperBound L κ θ σf σg Δ ε R₀)) ∧
      (ENNReal.ofReal (cq*lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (unrestrictedClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg)) ε ∧
       Complexity (unrestrictedClass (μ:=L/κ) (L:=L) (ρ:=θ*(L/κ)) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg)) ε≤
        ENNReal.ofReal (upperBound L κ θ σf σg Δ ε R₀)) := by
  obtain ⟨c,cq,hc,hc1,hcq,q,hlower⟩ := uniform_both_classes_lower
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
  have hl := hlower L κ θ Δ ε R₀ σf σg hL hκ hθ hθκ hΔ hε hR₀ hacc
  exact ⟨⟨hl.1,three_term_complexity_upper _ hL hΔ hε hθ' hκ' hacc'⟩,
    hl.2,three_term_complexity_upper _ hL hΔ hε hθ' hκ' hacc'⟩

end Bilevel.ChiUniformModel
