import Bilevel.ChiBoundedChainSourceCalibration

/-! The stronger radius-to-chain-width relation used to absorb the entire
chain gradient in radial Hessian and third derivative estimates. -/
noncomputable section
namespace Bilevel.ChiBoundedChain

theorem source_radius_width_ratio {CR lp hp r b ζ cn η : ℝ}
    (hCR : 0≤CR) (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r)
    (hb : 0<b) (hζ : 0<ζ) (hcn : 0<cn) (hη : 0<η)
    (n : ℕ) (hn : (n:ℝ)+1≤cn*r/η^2) :
    CR*r/(b*ζ*Real.sqrt cn)≤
      sourceLocalRadius CR lp hp r b ζ/((η*hp/r)*Real.sqrt ((n:ℝ)+1)) := by
  have hr0 : 0<r := by linarith
  have hn0 : 0<(n:ℝ)+1 := by positivity
  have hleft : 0<b*ζ*Real.sqrt cn := by positivity
  have hright : 0<(η*hp/r)*Real.sqrt ((n:ℝ)+1) := by positivity
  apply (div_le_div_iff₀ hleft hright).mpr
  have he₁ : (CR*r)*((η*hp/r)*Real.sqrt ((n:ℝ)+1))=
      (CR*hp)*(η*Real.sqrt ((n:ℝ)+1)) := by field_simp;ring
  have he₂ : sourceLocalRadius CR lp hp r b ζ*(b*ζ*Real.sqrt cn)=
      (CR*hp)*(Real.sqrt cn*Real.sqrt r) := by
    unfold sourceLocalRadius
    field_simp
    ring
  rw [he₁,he₂]
  exact mul_le_mul_of_nonneg_left (scaled_sqrt_chain_length hcn.le hr0.le hη n hn) (by positivity)

theorem source_floor_radius_width_ratio {CR lp hp r b ζ cn η : ℝ}
    (hCR : 0≤CR) (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r)
    (hb : 0<b) (hζ : 0<ζ) (hcn : 0<cn) (hη : 0<η) (hlen : 128≤cn/η^2) :
    CR/(b*ζ*Real.sqrt cn)≤CR*r/(b*ζ*Real.sqrt cn) ∧
      CR*r/(b*ζ*Real.sqrt cn)≤sourceLocalRadius CR lp hp r b ζ/
        ((η*hp/r)*Real.sqrt (((sourceChainIndex cn r η:ℕ):ℝ)+1)) := by
  refine ⟨?_,source_radius_width_ratio hCR hlp hhp hr hb hζ hcn hη _
    (sourceChainIndex_length hcn hr hη hlen).2⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

theorem source_base_chain_index {cn K : ℝ} (_hK : 0<K) :
    sourceChainIndex cn 1 (1/K)=Nat.floor (cn*K^2)-1 := by
  unfold sourceChainIndex
  congr 2
  field_simp

theorem source_receiver_scales {lp hp r ζ η K : ℝ}
    (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r) (hζ : 0<ζ) (hζ1 : ζ≤1)
    (hη : 0<η) (hη1 : η≤1) (hK : 1≤K) :
    (ζ*lp)*(η*hp/r)≤η*(lp*hp) ∧ η*hp/r≤hp ∧
      η*hp/r≤K*(η*(lp*hp))/(ζ*lp) := by
  have hr0 : 0<r := by linarith
  have hzr : ζ≤r := hζ1.trans hr
  refine ⟨?_,?_,?_⟩
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hr0).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hzr (show 0≤η*lp*hp by positivity)]
  · apply (div_le_iff₀ hr0).mpr
    nlinarith only [mul_le_mul_of_nonneg_right (hη1.trans hr) hhp.le]
  · apply (div_le_div_iff₀ hr0 (mul_pos hζ hlp)).mpr
    have hkr : ζ≤K*r := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right hkr (show 0≤η*lp*hp by positivity)]

end Bilevel.ChiBoundedChain
