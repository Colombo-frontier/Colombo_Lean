import Bilevel.ChiBoundedChainLocalBudgets

/-! A constructed weighted local certificate under explicit scalar budget
inequalities. All analytic norm/sign/radial premises are discharged from the
actual chain and receivers. Uniform source parameter calibration is separate. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem radialCoefficient_bounds_from_budgets {n : ℕ} (ρ radius G D : ℝ)
    (hR : 0<radius) (_hG : 0≤G) (hD : 0≤D) (U : Space n →ₗᵢ[ℝ] E) (u : E) (p : Space n)
    (hp : ‖p‖≤G) (hinner : ⟪WrappedChain.coordinates n radius U u,p⟫≤D)
    (hDbudget : 2*D≤ρ*radius^2) (hGbudget : 4*G≤ρ*radius) :
    ρ/2≤radialCoefficient ρ radius U u p ∧ radialCoefficient ρ radius U u p≤5*ρ/4 := by
  let z := WrappedChain.coordinates n radius U u
  let q := scale radius u
  have hq0 : 0≤q := (scale_pos radius u).le
  have hq1 : q≤1 := scale_le_one radius u
  have hz : ‖z‖≤radius := (frame_adjoint_norm_le U _).trans (compress_norm_le_radius radius hR u)
  have ha : |⟪z,p⟫|≤radius*G := (abs_real_inner_le_norm z p).trans
    (mul_le_mul hz hp (norm_nonneg p) hR.le)
  have hlo : q*⟪z,p⟫≤D := (mul_le_mul_of_nonneg_left hinner hq0).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hq1 hD)
  have hlowdiv : q*⟪z,p⟫/radius^2≤ρ/2 := (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by nlinarith only [hlo,hDbudget])
  have hneg : -(q*⟪z,p⟫)≤radius*G := by
    have h₀ := mul_le_mul_of_nonneg_left (neg_le_abs ⟪z,p⟫) hq0
    have h₁ := mul_le_mul_of_nonneg_right hq1 (abs_nonneg ⟪z,p⟫)
    nlinarith only [h₀,h₁,ha]
  have hhighdiv : -(q*⟪z,p⟫)/radius^2≤ρ/4 := (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by
    nlinarith only [hneg,mul_le_mul_of_nonneg_right hGbudget hR.le])
  rw [radialCoefficient_source_formula]
  change ρ/2≤ρ-q*⟪z,p⟫/radius^2 ∧ ρ-q*⟪z,p⟫/radius^2≤5*ρ/4
  rw [neg_div] at hhighdiv
  constructor <;> linarith only [hlowdiv,hhighdiv]

theorem weightedLocal_global_from_budgets (Cg Cr J : ℝ) (hCg : 0≤Cg) (hCr : 0≤Cr) (hJ : 0≤J)
    (n : ℕ) (ℓ h A ν g hp T w b Rp radius K : ℝ)
    (hℓ : 0≤ℓ) (hA : 3≤A) (hν : 0<ν) (hg : g=ℓ*h) (hh : 0<h) (hhp : 0<hp)
    (hT : 0<T) (hb : 0≤b) (hbw : b≤w) (hRp : Rp≤0) (hK : 1≤K)
    (hTscale : ν*T=K*g) (hR : 0<radius) (hsmall : ν*h≤2*g/15)
    (hbudgetD : 2*radialBudget Cr n ℓ h A g T w≤(b*ν)*radius^2)
    (hbudgetG : 4*normBudget Cg J n ℓ h A ν g hp w Rp≤(b*ν)*radius)
    (hexterior : b*g/2≤2*(b*ν)*radius/3-normBudget Cg J n ℓ h A ν g hp w Rp)
    (hactual : ∀ z : Space n,
      ‖gradient (weightedLatent n ℓ h A ν g hp T w Rp) z‖≤normBudget Cg J n ℓ h A ν g hp w Rp ∧
      ⟪z,gradient (weightedLatent n ℓ h A ν g hp T w Rp) z⟫≤radialBudget Cr n ℓ h A g T w)
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hQ : releaseGate (WrappedChain.coordinates n radius U u (Fin.last n)/hp)<1) :
    b*g/2≤‖gradient (weightedLocal n ℓ h A ν g hp T w Rp (b*ν) radius U) u‖ := by
  have hw : 0≤w := hb.trans hbw
  have hg0 : 0≤g := by rw [hg];positivity
  have hA0 : 0≤A := by linarith
  have hG0 : 0≤normBudget Cg J n ℓ h A ν g hp w Rp := by unfold normBudget;positivity
  have hD0 : 0≤radialBudget Cr n ℓ h A g T w := by unfold radialBudget;positivity
  let z := WrappedChain.coordinates n radius U u
  let p := gradient (weightedLatent n ℓ h A ν g hp T w Rp) z
  have hactualz := hactual z
  rcases le_total ‖u‖ radius with hu|hu
  · obtain ⟨hclow,hcup⟩ := radialCoefficient_bounds_from_budgets (b*ν) radius _ _ hR hG0 hD0
      U u p hactualz.1 hactualz.2 hbudgetD hbudgetG
    have hwidth : radialCoefficient (b*ν) radius U u p*h≤w*g/6 := by
      have h₀ := mul_le_mul_of_nonneg_right hcup hh.le
      have h₁ := mul_le_mul_of_nonneg_left hsmall hb
      have h₂ := mul_le_mul_of_nonneg_right hbw hg0
      nlinarith only [h₀,h₁,h₂]
    exact weightedLocal_interior_global_margin n ℓ h A ν g hp T w b Rp radius K hℓ hA hν hg hh hhp
      hT hb hbw hRp hK hTscale hR U u hu hclow (by simpa only [mul_assoc] using hcup) hwidth hQ
  · rw [(weightedLocal_hasGradientAt n ℓ h A ν g hp T w Rp (b*ν) radius hR U u).gradient]
    apply exterior_endgame (b*ν) radius _ (b*g) (mul_nonneg hb hν.le) hR hG0 hexterior u _ hu
    simpa only [U.norm_map] using hactualz.1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Every analytic budget premise in the previous assembly theorem is now
instantiated by proved bounds for the constructed functions. The remaining
premises are explicit scalar calibration inequalities on the source parameters. -/
theorem exists_constructed_weighted_certificate : ∃ Cg Cr J : ℝ,0≤Cg ∧ 0≤Cr ∧ 0≤J ∧
    ∀ (n : ℕ) (ℓ h A ν g hp T w b Rp radius K : ℝ),
      0≤ℓ → 3≤A → 0<ν → g=ℓ*h → 0<h → 0<hp → 0<T → 0≤b → b≤w → Rp≤0 → 1≤K →
      ν*T=K*g → 0<radius → ν*h≤2*g/15 →
      2*radialBudget Cr n ℓ h A g T w≤(b*ν)*radius^2 →
      4*normBudget Cg J n ℓ h A ν g hp w Rp≤(b*ν)*radius →
      b*g/2≤2*(b*ν)*radius/3-normBudget Cg J n ℓ h A ν g hp w Rp →
      ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
        (U : Space n →ₗᵢ[ℝ] F) (u : F),
        releaseGate (WrappedChain.coordinates n radius U u (Fin.last n)/hp)<1 →
        b*g/2≤‖gradient (weightedLocal n ℓ h A ν g hp T w Rp (b*ν) radius U) u‖ := by
  obtain ⟨Cg,Cr,J,hCg,hCr,hJ,hactual⟩ := actual_local_budgets
  refine ⟨Cg,Cr,J,hCg,hCr,hJ,fun n ℓ h A ν g hp T w b Rp radius K hℓ hA hν hg hh hhp hT hb hbw hRp hK
    hTscale hR hsmall hD hG hext F _ _ _ U u hQ => ?_⟩
  exact weightedLocal_global_from_budgets Cg Cr J hCg hCr hJ n ℓ h A ν g hp T w b Rp radius K
    hℓ hA hν hg hh hhp hT hb hbw hRp hK hTscale hR hsmall hD hG hext
    (hactual n ℓ h A ν g hp T w Rp hℓ (by linarith) hν.le (by rw [hg];positivity)
      hh hhp hT (hb.trans hbw) hRp) U u hQ

end Bilevel.ChiBoundedChain
