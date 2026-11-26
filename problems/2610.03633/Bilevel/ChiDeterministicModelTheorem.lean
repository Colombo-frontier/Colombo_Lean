import Bilevel.TransportPhysicalModelTheorem
import Bilevel.TransportQuadraticUniformModel
import Bilevel.ChiDeterministicBranchArithmetic

/-! Uniform deterministic hardness in the actual original-SFO model.
Below one fixed numerical theta threshold the exact-quadratic family pays
the bounded factor 1+theta. Above that threshold theta<=kappa^2 forces the
conditioning needed by the positive-depth physical transport family. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open PrimitiveQuery ChiRefinementRates
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem deterministic_model_hardness :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L μ κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 1≤θ → θ≤κ^2 →
      0<Δ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      Hardness (conservativeClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ)
        (R₀:=R₀) (σf:=σf) (σg:=σg)) ε
        (cq*deterministic L θ κ Δ ε/(Real.log (2+θ))^q) := by
  obtain ⟨CT,cw,qw,hCT,hcw,hcw1,hqw,q,hw⟩ := TransportHierarchy.physical_wide_model_hardness
  obtain ⟨cb,qb,hcb,hcb1,hqb,hb⟩ := TransportHierarchy.quadratic_conservative_hardness
  let Θ := max (wideBranchThreshold CT) ((3200:ℝ)^2)
  have hΘ : 0<1+Θ := by
    have hh : (3200:ℝ)^2≤Θ := le_max_right _ _
    nlinarith only [hh]
  let cq := min qw (qb/(1+Θ))
  have hcq : 0<cq := lt_min hqw (div_pos hqb hΘ)
  refine ⟨min cw cb,cq,lt_min hcw hcb,(min_le_left _ _).trans hcw1,hcq,q,?_⟩
  intro L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc
  have hw0 : 0≤min L (Real.sqrt (L*Δ)) := le_min hL.le (Real.sqrt_nonneg _)
  have haccw := hacc.trans (mul_le_mul_of_nonneg_right (min_le_left cw cb) hw0)
  have haccb := hacc.trans (mul_le_mul_of_nonneg_right (min_le_right cw cb) hw0)
  have hD : 0≤deterministic L θ κ Δ ε := deterministic_nonneg hL.le (by linarith only [hθ]) hΔ.le
  have hl : 1≤Real.log (2+θ) := ChiMinimax.logarithm_ge_one hθ
  have hp : 1≤(Real.log (2+θ))^q := one_le_pow₀ hl
  by_cases hsmall : θ≤Θ
  · have hHard := hb L μ κ (θ*μ) Δ ε R₀ σf σg hL hμ hκ hκeq
      (mul_nonneg (by linarith only [hθ]) hμ.le) hΔ hε hR₀ haccb
    apply hHard.mono
    exact fixed_factor_log_absorption hD hΘ hcq.le hqb.le (min_le_right _ _)
      (deterministic_bounded_theta hL.le hΔ.le hsmall) hp
  · have hlarge : Θ<θ := lt_of_not_ge hsmall
    have hκbig : 3200≤κ := by
      have hh : (3200:ℝ)^2<κ^2 := (lt_of_le_of_lt (le_max_right _ _) hlarge).trans_le hθκ
      nlinarith only [hh,hκ]
    have hbranch : wideBranchThreshold CT≤θ := (le_max_left _ _).trans hlarge.le
    have hrel : κ*μ=L := (eq_div_iff hμ.ne').mp hκeq
    have hμeq : L/κ=μ := (div_eq_iff (by linarith only [hκ] : κ≠0)).mpr (by nlinarith only [hrel])
    have hHard := hw L κ θ Δ ε R₀ σf σg hL hκbig hθκ hbranch hΔ hε hR₀ haccw
    rw [hμeq] at hHard
    apply hHard.mono
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hD) (by linarith only [hp])

end Bilevel.ChiExtensionCalibration
