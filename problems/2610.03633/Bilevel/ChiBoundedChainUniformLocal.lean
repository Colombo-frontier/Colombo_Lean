import Bilevel.ChiBoundedChainSourceCalibration

/-! The source weighted local margins with all scalar radius premises
discharged. The fixed constants are uniform in the lower weight and ratio. -/
noncomputable section
namespace Bilevel.ChiBoundedChain

def sourceWeightedLocal {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (A K ζ cn η CR lp hp r b w Rp : ℝ)
    (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] F) : F → ℝ :=
  weightedLocal (sourceChainIndex cn r η) (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp
    (K*(η*(lp*hp))/(ζ*lp)) w Rp (b*(ζ*lp)) (sourceLocalRadius CR lp hp r b ζ) U

/-- For any fixed source smallness parameters, a single explicit radius
constant gives both source margins, in every ambient Hilbert space. -/
theorem source_uniform_weighted_margins (A K ζ cn η Cp : ℝ)
    (hA : 3≤A) (hK : 1≤K) (hζ : 0<ζ) (hζsmall : ζ≤2/15)
    (hcn : 0<cn) (hη : 0<η) (hlen : 128≤cn/η^2) (hCp : 0≤Cp) :
    ∃ CR : ℝ,0<CR ∧ ∀ (lp hp r b w Rp : ℝ),
      0<lp → 0<hp → 1≤r → 0<b → b≤w → w≤1 → Rp≤0 → |Rp|≤Cp*lp*hp^2 →
      ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
        (U : Space (sourceChainIndex cn r η) →ₗᵢ[ℝ] F) (u : F),
        (releaseGate (WrappedChain.coordinates (sourceChainIndex cn r η)
            (sourceLocalRadius CR lp hp r b ζ) U u (Fin.last (sourceChainIndex cn r η))/hp)<1 →
          b*(η*(lp*hp))/2≤‖gradient (sourceWeightedLocal A K ζ cn η CR lp hp r b w Rp U) u‖) ∧
        (|WrappedChain.coordinates (sourceChainIndex cn r η)
            (sourceLocalRadius CR lp hp r b ζ) U u (Fin.last (sourceChainIndex cn r η))|<(η*hp/r)/2 →
          w*(η*(lp*hp))/2≤‖gradient (sourceWeightedLocal A K ζ cn η CR lp hp r b w Rp U) u‖) := by
  obtain ⟨Cg,Cr,J,hCg,hCr,hJ,hcertificate⟩ := exists_constructed_weighted_margins
  have hA0 : 0≤A := by linarith
  have hK0 : 0≤K := by linarith
  let CR := sourceRadiusConstant Cg Cr J A K ζ cn η Cp
  have hconstants := sourceRadiusConstant_bounds Cg Cr J A K ζ cn η Cp hCg hCr hJ hA0 hK0 hζ hcn.le hη.le hCp
  have hN0 : 0≤sourceNormConstant Cg J A ζ cn η Cp := by unfold sourceNormConstant;positivity
  have hD0 : 0≤sourceRadialConstant Cr A K ζ cn η := by unfold sourceRadialConstant;positivity
  refine ⟨CR,hconstants.1,?_⟩
  intro lp hp r b w Rp hlp hhp hr hb hbw hw1 hRp0 hRp F _ _ _ U u
  let n := sourceChainIndex cn r η
  have hr0 : 0<r := by linarith
  have hw0 : 0≤w := hb.le.trans hbw
  have hn : (n:ℝ)+1≤cn*r/η^2 := (sourceChainIndex_length hcn hr hη hlen).2
  have hnorm := source_normBudget_bound Cg J A ζ cn η Cp lp hp r w Rp n
    hCg hJ hA0 hζ hcn hη hCp hlp hhp hr hw0 hw1 hRp hn
  have hradial := source_radialBudget_bound Cr A K ζ cn η lp hp r w n
    hCr hA0 hK0 hζ hcn hη hlp hhp hr hw0 hw1 hn
  have hscalar := scalar_radius_calibration hN0 hD0 hη.le hconstants.1
    hlp hhp hr hb (hbw.trans hw1) hζ hconstants.2.1 hconstants.2.2.1 hconstants.2.2.2
  have hscale : η*(lp*hp)=(r*lp)*(η*hp/r) := by field_simp;ring
  have hT : 0<K*(η*(lp*hp))/(ζ*lp) := by
    have hk : 0<K := by linarith
    positivity
  have hTscale : (ζ*lp)*(K*(η*(lp*hp))/(ζ*lp))=K*(η*(lp*hp)) := by field_simp
  have hsmall : (ζ*lp)*(η*hp/r)≤2*(η*(lp*hp))/15 := by
    have hz : ζ≤2*r/15 := by linarith
    have hh := mul_le_mul_of_nonneg_right hz (show 0≤η*lp*hp by positivity)
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hr0).mpr
    nlinarith only [hh]
  have hD : 2*radialBudget Cr n (r*lp) (η*hp/r) A (η*(lp*hp)) (K*(η*(lp*hp))/(ζ*lp)) w≤
      (b*(ζ*lp))*(sourceLocalRadius CR lp hp r b ζ)^2 := by
    exact (mul_le_mul_of_nonneg_left hradial (by norm_num)).trans hscalar.2.1
  have hG : 4*normBudget Cg J n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp w Rp≤
      (b*(ζ*lp))*sourceLocalRadius CR lp hp r b ζ := by
    exact (mul_le_mul_of_nonneg_left hnorm (by norm_num)).trans hscalar.2.2.1
  have hext : (η*(lp*hp))/2≤2*(b*(ζ*lp))*sourceLocalRadius CR lp hp r b ζ/3-
      normBudget Cg J n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp w Rp := by
    linarith only [hscalar.2.2.2,hnorm]
  exact hcertificate n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp (K*(η*(lp*hp))/(ζ*lp))
    w b Rp (sourceLocalRadius CR lp hp r b ζ) K (by positivity) hA (by positivity) hscale
    (by positivity) hhp hT hb.le hbw hw1 hRp0 hK hTscale hscalar.1 hsmall hD hG hext F U u

end Bilevel.ChiBoundedChain
