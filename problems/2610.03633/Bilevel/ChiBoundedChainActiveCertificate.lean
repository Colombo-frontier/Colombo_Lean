import Bilevel.ChiBoundedChainLocalCertificate

/-! Both weighted margins for the actual local objective. Analytic budgets
are derived from the construction; the explicit scalar calibration conditions
are left visible until the manuscript's fixed parameters are instantiated. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem weightedLocal_active_from_budgets (Cg Cr J : ℝ) (hCg : 0≤Cg) (hCr : 0≤Cr) (hJ : 0≤J)
    (n : ℕ) (ℓ h A ν g hp T w b Rp radius : ℝ)
    (hℓ : 0≤ℓ) (hA : 0≤A) (hν : 0<ν) (hg : g=ℓ*h) (hh : 0<h) (hhp : 0<hp)
    (hT : 0<T) (hb : 0≤b) (hbw : b≤w) (hw1 : w≤1) (hRp : Rp≤0)
    (hR : 0<radius) (hsmall : ν*h≤2*g/15)
    (hbudgetD : 2*radialBudget Cr n ℓ h A g T w≤(b*ν)*radius^2)
    (hbudgetG : 4*normBudget Cg J n ℓ h A ν g hp w Rp≤(b*ν)*radius)
    (hexterior : g/2≤2*(b*ν)*radius/3-normBudget Cg J n ℓ h A ν g hp w Rp)
    (hactual : ∀ z : Space n,
      ‖gradient (weightedLatent n ℓ h A ν g hp T w Rp) z‖≤normBudget Cg J n ℓ h A ν g hp w Rp ∧
      ⟪z,gradient (weightedLatent n ℓ h A ν g hp T w Rp) z⟫≤radialBudget Cr n ℓ h A g T w)
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hterminal : |WrappedChain.coordinates n radius U u (Fin.last n)|<h/2) :
    w*g/2≤‖gradient (weightedLocal n ℓ h A ν g hp T w Rp (b*ν) radius U) u‖ := by
  have hw : 0≤w := hb.trans hbw
  have hg0 : 0≤g := by rw [hg];positivity
  have hG0 : 0≤normBudget Cg J n ℓ h A ν g hp w Rp := by unfold normBudget;positivity
  have hD0 : 0≤radialBudget Cr n ℓ h A g T w := by unfold radialBudget;positivity
  let z := WrappedChain.coordinates n radius U u
  let p := gradient (weightedLatent n ℓ h A ν g hp T w Rp) z
  have hactualz := hactual z
  rcases le_total ‖u‖ radius with hu|hu
  · obtain ⟨hclow,hcup⟩ := radialCoefficient_bounds_from_budgets (b*ν) radius _ _ hR hG0 hD0
      U u p hactualz.1 hactualz.2 hbudgetD hbudgetG
    have hc0 : 0≤radialCoefficient (b*ν) radius U u p := le_trans (by positivity) hclow
    have hwidth : radialCoefficient (b*ν) radius U u p*h≤w*g/6 := by
      have h₀ := mul_le_mul_of_nonneg_right hcup hh.le
      have h₁ := mul_le_mul_of_nonneg_left hsmall hb
      have h₂ := mul_le_mul_of_nonneg_right hbw hg0
      nlinarith only [h₀,h₁,h₂]
    have hgeom := weighted_interior_active_margin n ℓ h A ν g hp T w Rp _ _ hℓ hA hν.le hg hh hhp
      hw hRp hc0 (scale_interior_lower radius hR u hu) hwidth z (by
        change |WrappedChain.coordinates n radius U u (Fin.last n)|<h
        linarith only [hterminal,hh])
    rw [← weightedLocal_projected_gradient n ℓ h A ν g hp T w Rp (b*ν) radius hR U u] at hgeom
    exact hgeom.trans (frame_adjoint_norm_le U _)
  · have hext : w*g/2≤2*(b*ν)*radius/3-normBudget Cg J n ℓ h A ν g hp w Rp :=
      (by nlinarith only [mul_le_mul_of_nonneg_right hw1 hg0] : w*g/2≤g/2).trans hexterior
    rw [(weightedLocal_hasGradientAt n ℓ h A ν g hp T w Rp (b*ν) radius hR U u).gradient]
    apply exterior_endgame (b*ν) radius _ (w*g) (mul_nonneg hb hν.le) hR hG0 hext u _ hu
    simpa only [U.norm_map] using hactualz.1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The two source margins, with dimension-independent numerical analytic
constants and only explicit scalar calibration premises. -/
theorem exists_constructed_weighted_margins : ∃ Cg Cr J : ℝ,0≤Cg ∧ 0≤Cr ∧ 0≤J ∧
    ∀ (n : ℕ) (ℓ h A ν g hp T w b Rp radius K : ℝ),
      0≤ℓ → 3≤A → 0<ν → g=ℓ*h → 0<h → 0<hp → 0<T → 0≤b → b≤w → w≤1 → Rp≤0 → 1≤K →
      ν*T=K*g → 0<radius → ν*h≤2*g/15 →
      2*radialBudget Cr n ℓ h A g T w≤(b*ν)*radius^2 →
      4*normBudget Cg J n ℓ h A ν g hp w Rp≤(b*ν)*radius →
      g/2≤2*(b*ν)*radius/3-normBudget Cg J n ℓ h A ν g hp w Rp →
      ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
        (U : Space n →ₗᵢ[ℝ] F) (u : F),
        (releaseGate (WrappedChain.coordinates n radius U u (Fin.last n)/hp)<1 →
          b*g/2≤‖gradient (weightedLocal n ℓ h A ν g hp T w Rp (b*ν) radius U) u‖) ∧
        (|WrappedChain.coordinates n radius U u (Fin.last n)|<h/2 →
          w*g/2≤‖gradient (weightedLocal n ℓ h A ν g hp T w Rp (b*ν) radius U) u‖) := by
  obtain ⟨Cg,Cr,J,hCg,hCr,hJ,hactual⟩ := actual_local_budgets
  refine ⟨Cg,Cr,J,hCg,hCr,hJ,fun n ℓ h A ν g hp T w b Rp radius K hℓ hA hν hg hh hhp hT hb hbw hw1 hRp hK
    hTscale hR hsmall hD hG hext F _ _ _ U u => ?_⟩
  have hA0 : 0≤A := by linarith
  have hg0 : 0≤g := by rw [hg];positivity
  have ha := hactual n ℓ h A ν g hp T w Rp hℓ hA0 hν.le hg0 hh hhp hT (hb.trans hbw) hRp
  refine ⟨fun hQ => ?_,fun ht => ?_⟩
  · have hext' : b*g/2≤2*(b*ν)*radius/3-normBudget Cg J n ℓ h A ν g hp w Rp :=
      (by nlinarith only [mul_le_mul_of_nonneg_right (hbw.trans hw1) hg0] : b*g/2≤g/2).trans hext
    exact weightedLocal_global_from_budgets Cg Cr J hCg hCr hJ n ℓ h A ν g hp T w b Rp radius K
      hℓ hA hν hg hh hhp hT hb hbw hRp hK hTscale hR hsmall hD hG hext' ha U u hQ
  · exact weightedLocal_active_from_budgets Cg Cr J hCg hCr hJ n ℓ h A ν g hp T w b Rp radius
      hℓ hA0 hν hg hh hhp hT hb hbw hw1 hRp hR hsmall hD hG hext ha U u ht

end Bilevel.ChiBoundedChain
