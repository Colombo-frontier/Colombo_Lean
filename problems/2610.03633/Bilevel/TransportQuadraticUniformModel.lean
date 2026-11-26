import Bilevel.TransportQuadraticModelTheorem
import Bilevel.ChiBoundedKappaQuadraticModel

/-! The complete exact-quadratic deterministic hardness theorem in the
actual common query model, including every conditioning level kappa>=2. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open PrimitiveQuery
set_option autoImplicit false

theorem quadratic_model_hardness :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ (L μ κ ρ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 0≤ρ → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      Hardness (conservativeCurvatureClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
        (R₀:=R₀) (σf:=σf) (σg:=σg) (4*L*κ^2)) ε
        (cq*(L*κ^2*Real.sqrt κ*Δ/ε^2)) := by
  obtain ⟨ch,qh,hch,hch1,hqh,hh⟩ := quadratic_high_kappa_model_hardness
  obtain ⟨cl,ql,hcl,hcl1,hql,hl⟩ := ChiUpperNoise.bounded_kappa_quadratic_model_hardness
  refine ⟨min ch cl,min qh ql,lt_min hch hcl,(min_le_left _ _).trans hch1,lt_min hqh hql,?_⟩
  intro L μ κ ρ Δ ε R₀ σf σg hL hμ hκ hκeq hρ hΔ hε hR₀ hacc
  have hnonneg : 0≤L*κ^2*Real.sqrt κ*Δ/ε^2 := by positivity
  by_cases hsmall : κ≤3200
  · have hacc' := hacc.trans (mul_le_mul_of_nonneg_right (min_le_right ch cl)
      (le_min hL.le (Real.sqrt_nonneg _)))
    apply (hl L μ κ ρ Δ ε R₀ σf σg hL hμ hκ hsmall hκeq hρ hΔ hε hR₀ hacc').mono
    calc
      min qh ql*(L*κ^2*Real.sqrt κ*Δ/ε^2)≤ql*(L*κ^2*Real.sqrt κ*Δ/ε^2) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hnonneg
      _=ql*L*κ^2*Real.sqrt κ*Δ/ε^2 := by ring
  · have hacc' := hacc.trans (mul_le_mul_of_nonneg_right (min_le_left ch cl)
      (le_min hL.le (Real.sqrt_nonneg _)))
    have hbig : 3200≤κ := (lt_of_not_ge hsmall).le
    have hrel : κ*μ=L := (eq_div_iff hμ.ne').mp hκeq
    have hμeq : L/κ=μ := (div_eq_iff (by linarith only [hκ] : κ≠0)).mpr (by nlinarith only [hrel])
    have hHard := hh L κ ρ Δ ε R₀ σf σg hL hbig hρ hΔ hε hR₀ hacc'
    rw [hμeq] at hHard
    exact hHard.mono (mul_le_mul_of_nonneg_right (min_le_left _ _) hnonneg)

theorem quadratic_conservative_hardness :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧
    ∀ (L μ κ ρ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 0≤ρ → 0<Δ → 0<ε → 0≤R₀ →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      Hardness (conservativeClass (μ:=μ) (L:=L) (ρ:=ρ) (Δ:=Δ)
        (R₀:=R₀) (σf:=σf) (σg:=σg)) ε
        (cq*(L*κ^2*Real.sqrt κ*Δ/ε^2)) := by
  obtain ⟨c,cq,hc,hc1,hcq,h⟩ := quadratic_model_hardness
  refine ⟨c,cq,hc,hc1,hcq,?_⟩
  intro L μ κ ρ Δ ε R₀ σf σg hL hμ hκ hκeq hρ hΔ hε hR₀ hacc
  exact (h L μ κ ρ Δ ε R₀ σf σg hL hμ hκ hκeq hρ hΔ hε hR₀ hacc).enlarge_class
    (fun _ _ hI => hI.1)

end Bilevel.TransportHierarchy
