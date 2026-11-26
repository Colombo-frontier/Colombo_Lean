import Bilevel.ChiWideQueryHardness
import Bilevel.ChiBoundedThetaQueryHardness

/-! The complete lower-noise family theorem in the common original-query
model. Constants and the logarithmic exponent precede all public budgets;
the wide and bounded theta branches both use actual conservative SFOs. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open PrimitiveQuery ChiRefinementRates
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem lower_noise_model_hardness :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L μ κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 1≤θ → θ≤κ^2 →
      0<Δ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      Hardness (conservativeClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε
        (cq*lowerNoise L θ κ σg Δ ε/(Real.log (2+θ))^q) := by
  obtain ⟨CT,cw,qw,hCT,hcw,hcw1,hqw,q,hw⟩ := wide_query_hardness
  obtain ⟨cb,qb,hcb,hcb1,hqb,hb⟩ := bounded_theta_query_hardness
    (max 1 (wideBranchThreshold CT)) (le_max_left _ _)
  refine ⟨min cw cb,min qw qb,lt_min hcw hcb,(min_le_left _ _).trans hcw1,lt_min hqw hqb,q,?_⟩
  intro L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc
  have haccw := hacc.trans (mul_le_mul_of_nonneg_right (min_le_left cw cb)
    (le_min hL.le (Real.sqrt_nonneg _)))
  have haccb := hacc.trans (mul_le_mul_of_nonneg_right (min_le_right cw cb)
    (le_min hL.le (Real.sqrt_nonneg _)))
  have hG : 0≤lowerNoise L θ κ σg Δ ε := lowerNoise_nonneg hL.le (by linarith) hΔ.le
  have hD : 0≤L*(1+θ)*κ^2*Δ/ε^2 := by positivity
  have hl : 1≤Real.log (2+θ) := ChiMinimax.logarithm_ge_one hθ
  have hp : 1≤(Real.log (2+θ))^q := one_le_pow₀ hl
  by_cases hwide : wideBranchThreshold CT≤θ
  · apply (hw L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθκ hwide hΔ hε hR₀ haccw).mono
    apply div_le_div_of_nonneg_right _ (by linarith only [hp])
    exact (mul_le_mul_of_nonneg_right (min_le_left qw qb) hG).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hD) hqw.le)
  · have hθb : θ≤max 1 (wideBranchThreshold CT) :=
      (le_of_lt (lt_of_not_ge hwide)).trans (le_max_right _ _)
    apply (hb L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθb hΔ hε hR₀ haccb).mono
    apply le_trans (div_le_self (mul_nonneg (lt_min hqw hqb).le hG) hp)
    exact (mul_le_mul_of_nonneg_right (min_le_right qw qb) hG).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hD) hqb.le)

end Bilevel.ChiExtensionCalibration
