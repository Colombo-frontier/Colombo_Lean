import Bilevel.ChiBoundedChainUniformLocal
import Bilevel.ChiBoundedChainSourceAmplitude

/-! One fixed radius works for every smaller resolution, including the
source base chain eta=1/K for all sufficiently large K. -/
noncomputable section
namespace Bilevel.ChiBoundedChain

theorem source_constants_mono_eta {Cg Cr J A K ζ cn Cp η ηmax : ℝ}
    (hA : 0≤A) (hK : 0≤K) (hζ : 0<ζ) (hη : 0≤η) (hle : η≤ηmax) :
    sourceNormConstant Cg J A ζ cn η Cp≤sourceNormConstant Cg J A ζ cn ηmax Cp ∧
    sourceRadialConstant Cr A K ζ cn η≤sourceRadialConstant Cr A K ζ cn ηmax ∧
    sourceAmplitudeConstant A K ζ cn η≤sourceAmplitudeConstant A K ζ cn ηmax := by
  have hsq : η^2≤ηmax^2 := by nlinarith
  have hterm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (show 0≤2*A*K by positivity)) hζ.le
  unfold sourceNormConstant sourceRadialConstant sourceAmplitudeConstant
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hle hA]
  · constructor <;> nlinarith [mul_le_mul_of_nonneg_left hle hA]

theorem source_uniform_eta_margins (A K ζ cn ηmax Cp : ℝ)
    (hA : 3≤A) (hK : 1≤K) (hζ : 0<ζ) (hζsmall : ζ≤2/15)
    (hcn : 0<cn) (hηmax : 0<ηmax) (hlen : 128≤cn/ηmax^2) (hCp : 0≤Cp) :
    ∃ CR : ℝ,1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ ∀ (η lp hp r b w Rp : ℝ),
      0<η → η≤ηmax → 0<lp → 0<hp → 1≤r → 0<b → b≤w → w≤1 → Rp≤0 → |Rp|≤Cp*lp*hp^2 →
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
  let R₀ := sourceRadiusConstant Cg Cr J A K ζ cn ηmax Cp
  let CR := R₀+1+ζ*Real.sqrt cn
  have hc := sourceRadiusConstant_bounds Cg Cr J A K ζ cn ηmax Cp
    hCg hCr hJ hA0 hK0 hζ hcn.le hηmax.le hCp
  have hCRle : R₀≤CR := by dsimp only [CR];nlinarith [mul_nonneg hζ.le (Real.sqrt_nonneg cn)]
  have hCR : 0<CR := hc.1.trans_le hCRle
  have hCR1 : 1≤CR := by dsimp only [CR];nlinarith [hc.1,mul_nonneg hζ.le (Real.sqrt_nonneg cn)]
  have hCRsqrt : ζ*Real.sqrt cn≤CR := by dsimp only [CR];linarith [hc.1]
  have hD : 2*ζ*sourceRadialConstant Cr A K ζ cn ηmax≤CR^2 :=
    hc.2.2.1.trans (by nlinarith [hc.1])
  have hex : ηmax/2≤2*CR/3-sourceNormConstant Cg J A ζ cn ηmax Cp := by
    have hh : ηmax/2≤2*R₀/3-sourceNormConstant Cg J A ζ cn ηmax Cp := hc.2.2.2
    exact hh.trans (sub_le_sub_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCRle (by norm_num : (0:ℝ)≤2))
        (by norm_num : (0:ℝ)≤3)) _)
  have hN0 : 0≤sourceNormConstant Cg J A ζ cn ηmax Cp := by unfold sourceNormConstant;positivity
  have hD0 : 0≤sourceRadialConstant Cr A K ζ cn ηmax := by unfold sourceRadialConstant;positivity
  refine ⟨CR,hCR1,hCRsqrt,?_⟩
  intro η lp hp r b w Rp hη hηle hlp hhp hr hb hbw hw1 hRp0 hRp F _ _ _ U u
  let n := sourceChainIndex cn r η
  have hr0 : 0<r := by linarith
  have hw0 : 0≤w := hb.le.trans hbw
  have hηsq : η^2≤ηmax^2 := by nlinarith
  have hlen' : 128≤cn/η^2 := hlen.trans (div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos hη) hηsq)
  have hn : (n:ℝ)+1≤cn*r/η^2 := (sourceChainIndex_length hcn hr hη hlen').2
  have hmono := source_constants_mono_eta (Cg:=Cg) (Cr:=Cr) (J:=J) (cn:=cn) (Cp:=Cp) hA0 hK0 hζ hη.le hηle
  have hnorm := (source_normBudget_bound Cg J A ζ cn η Cp lp hp r w Rp n
    hCg hJ hA0 hζ hcn hη hCp hlp hhp hr hw0 hw1 hRp hn).trans
      (mul_le_mul_of_nonneg_right hmono.1 (show 0≤lp*hp*Real.sqrt r by positivity))
  have hradial := (source_radialBudget_bound Cr A K ζ cn η lp hp r w n
    hCr hA0 hK0 hζ hcn hη hlp hhp hr hw0 hw1 hn).trans
      (mul_le_mul_of_nonneg_right hmono.2.1 (show 0≤lp*hp^2 by positivity))
  have hscalar := scalar_radius_calibration hN0 hD0 hηmax.le hCR hlp hhp hr hb (hbw.trans hw1) hζ
    (hc.2.1.trans hCRle) hD hex
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
  have hext : (η*(lp*hp))/2≤2*(b*(ζ*lp))*sourceLocalRadius CR lp hp r b ζ/3-
      normBudget Cg J n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp w Rp := by
    have hg := mul_le_mul_of_nonneg_right hηle (show 0≤lp*hp by positivity)
    linarith only [hscalar.2.2.2,hnorm,hg]
  exact hcertificate n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp (K*(η*(lp*hp))/(ζ*lp))
    w b Rp (sourceLocalRadius CR lp hp r b ζ) K (by positivity) hA (by positivity) hscale
    (by positivity) hhp hT hb.le hbw hw1 hRp0 hK hTscale hscalar.1 hsmall
    ((mul_le_mul_of_nonneg_left hradial (by norm_num)).trans hscalar.2.1)
    ((mul_le_mul_of_nonneg_left hnorm (by norm_num)).trans hscalar.2.2.1) hext F U u

end Bilevel.ChiBoundedChain
