import Bilevel.ChiSplitPayloadJets
import Bilevel.ChiCarrierLocalBudgets

/-! Actual split-payload value and first-derivative normalization at source
scales, independent of source width ratio and transport length. -/
noncomputable section
namespace Bilevel.ChiSplitChain
open ChiBoundedChain ChiCarrier

theorem chain_abs_bound (n : ℕ) (ell h : ℝ) (hell : 0≤ell) (z : Latent n) :
    |chain n ell h z|≤(n+1)*gaussianBound*(ell*h^2) := by
  rw [chain,abs_mul,abs_of_nonneg (show 0≤ell*h^2 by positivity)]
  have hb := mul_le_mul_of_nonneg_left (value_abs_bound n (h⁻¹ • z)) (show 0≤ell*h^2 by positivity)
  nlinarith only [hb]

theorem payload_abs_bound (n : ℕ) (ell h A ν g hp T : ℝ)
    (hell : 0≤ell) (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hhp : 0<hp) (hT : 0<T)
    (z : Latent n) : |payload n ell h A ν g hp T z|≤
      (n+1)*gaussianBound*(ell*h^2)+(A*(3*ν*hp+g))*(3*hp)+(A*g)*(2*T) := by
  have hc := chain_abs_bound n ell h hell z
  have hpbound := positiveReceiver_abs_bound A ν g h hp (z.snd (Fin.last n)) hA hν hg hh hhp
  have hn := negativeReceiver_abs_bound A g h T (z.snd (Fin.last n)) hA hg hh hT
  have ht₀ := abs_add (chain n ell h z) (positiveReceiver A ν g h hp (z.snd (Fin.last n)))
  have ht₁ := abs_add (chain n ell h z+positiveReceiver A ν g h hp (z.snd (Fin.last n)))
    (negativeReceiver A g h T (z.snd (Fin.last n)))
  unfold payload
  linarith

theorem source_payload_amplitude (A K ζ cn η lp hp r : ℝ) (n : ℕ)
    (hA : 0≤A) (hK : 0<K) (hζ : 0<ζ) (_hcn : 0<cn) (hη : 0<η)
    (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r)
    (hn : (n:ℝ)+1≤cn*r/η^2) (z : Latent n) :
    |payload n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp (K*(η*(lp*hp))/(ζ*lp)) z|≤
      sourceAmplitudeConstant A K ζ cn η*(lp*hp^2) := by
  have hr0 : 0<r := by linarith
  have hvalue := payload_abs_bound n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp
    (K*(η*(lp*hp))/(ζ*lp)) (by positivity) hA (by positivity) (by positivity)
    (by positivity) hhp (by positivity) z
  have he : (cn*r/η^2)*((r*lp)*(η*hp/r)^2)=cn*(lp*hp^2) := by field_simp;ring
  have hc : ((n:ℝ)+1)*((r*lp)*(η*hp/r)^2)≤cn*(lp*hp^2) := by
    rw [← he]
    exact mul_le_mul_of_nonneg_right hn (by positivity)
  have hchain := mul_le_mul_of_nonneg_left hc gaussianBound_nonneg
  have hreceiver : (A*(3*(ζ*lp)*hp+η*(lp*hp)))*(3*hp)+
      (A*(η*(lp*hp)))*(2*(K*(η*(lp*hp))/(ζ*lp)))=
      (3*A*(3*ζ+η)+2*A*K*η^2/ζ)*(lp*hp^2) := by field_simp;ring
  unfold sourceAmplitudeConstant
  nlinarith only [hvalue,hchain,hreceiver]

theorem source_payload_value_normalized (A K ζ cn η lp hp r : ℝ)
    (hA : 0≤A) (hK : 0<K) (hζ : 0<ζ) (hcn : 0<cn) (hη : 0<η) (hη1 : η≤1)
    (hlp : 0<lp) (hhp : 0<hp) (hr : 1≤r) (hlen : 128≤cn/η^2)
    (z : Latent (sourceChainIndex cn r η)) :
    |payload (sourceChainIndex cn r η) (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp
      (K*(η*(lp*hp))/(ζ*lp)) z|≤
      valueConstant A K ζ cn*(((sourceChainIndex cn r η:ℕ):ℝ)+1)*((r*lp)*(η*hp/r)^2) := by
  have hr0 : 0<r := by linarith
  have hb := source_payload_amplitude A K ζ cn η lp hp r _ hA hK hζ hcn hη hlp hhp hr
    (sourceChainIndex_length hcn hr hη hlen).2 z
  have hmax := mul_le_mul_of_nonneg_right (amplitude_uniform_eta (cn:=cn) hA hK.le hζ hη.le hη1)
    (show 0≤lp*hp^2 by positivity)
  have hconstant : 0≤valueConstant A K ζ cn := by
    unfold valueConstant
    have := gaussianBound_nonneg
    positivity
  have he := mul_le_mul_of_nonneg_right (source_length_lower hcn hr hη hlen)
    (show 0≤(r*lp)*(η*hp/r)^2 by positivity)
  have heq : (cn*r/η^2/2)*((r*lp)*(η*hp/r)^2)=(cn/2)*(lp*hp^2) := by field_simp;ring
  rw [heq] at he
  have henergy := mul_le_mul_of_nonneg_left he hconstant
  have hcancel : valueConstant A K ζ cn*((cn/2)*(lp*hp^2))=
      (gaussianBound*cn+3*A*(3*ζ+1)+2*A*K/ζ)*(lp*hp^2) := by
    unfold valueConstant
    field_simp
    ring
  rw [hcancel] at henergy
  exact hb.trans (hmax.trans (by convert henergy using 1;ring))

theorem source_payload_first_normalized : ∃ Cg : ℝ,0≤Cg ∧
    ∀ (A K ζ cn η lp hp r : ℝ),0≤A → 0<K → 0<ζ → 0<cn → 0<η → η≤1 →
      128≤cn/η^2 → 0<lp → 0<hp → 1≤r →
      ∀ z : Latent (sourceChainIndex cn r η),
      ‖iteratedFDeriv ℝ 1 (payload (sourceChainIndex cn r η) (r*lp) (η*hp/r) A (ζ*lp)
        (η*(lp*hp)) hp (K*(η*(lp*hp))/(ζ*lp))) z‖≤
        gradientConstant Cg A ζ cn*((r*lp)*(η*hp/r))*Real.sqrt (((sourceChainIndex cn r η:ℕ):ℝ)+1) := by
  obtain ⟨Cg,hCg,hfirst⟩ := payload_first_uniform
  refine ⟨Cg,hCg,fun A K ζ cn η lp hp r hA _hK hζ hcn hη hη1 hlen hlp hhp hr z => ?_⟩
  let n := sourceChainIndex cn r η
  have hr0 : 0<r := by linarith only [hr]
  have hh : 0<η*hp/r := by positivity
  have he : (r*lp)*(η*hp/r)=η*(lp*hp) := by field_simp; ring
  have hgrad := hfirst n (r*lp) (η*hp/r) A (ζ*lp) (η*(lp*hp)) hp
    (K*(η*(lp*hp))/(ζ*lp)) (by positivity) hA (by positivity) (by positivity) hh hhp z
  have hbudget := source_normBudget_bound Cg 0 A ζ cn η 0 lp hp r 1 0 n
    hCg (by norm_num) hA hζ hcn hη (by norm_num) hlp hhp hr (by norm_num) (by norm_num)
    (by simp) (sourceChainIndex_length hcn hr hη hlen).2
  simp only [normBudget,one_mul,abs_zero,zero_mul,zero_div,add_zero] at hbudget
  have hN : sourceNormConstant Cg 0 A ζ cn η 0≤Cg*Real.sqrt cn+A*(3*ζ+2) := by
    unfold sourceNormConstant
    nlinarith only [mul_le_mul_of_nonneg_left hη1 hA]
  have hN0 : 0≤Cg*Real.sqrt cn+A*(3*ζ+2) := by positivity
  have hs := mul_le_mul_of_nonneg_left (source_sqrt_length_lower hcn hr hη hlen)
    (show 0≤lp*hp by positivity)
  have hsqrt : 0<Real.sqrt (cn/2) := by positivity
  have hnorm : (lp*hp*Real.sqrt r)≤
      (((r*lp)*(η*hp/r))*Real.sqrt ((n:ℝ)+1))/Real.sqrt (cn/2) := by
    apply (le_div_iff₀ hsqrt).mpr
    rw [he]
    dsimp [n]
    nlinarith only [hs]
  have hb₁ := mul_le_mul_of_nonneg_right hN (show 0≤lp*hp*Real.sqrt r by positivity)
  have hb₂ := mul_le_mul_of_nonneg_left hnorm hN0
  have hfinal := hgrad.trans (hbudget.trans (hb₁.trans hb₂))
  convert hfinal using 1
  unfold gradientConstant
  ring

end Bilevel.ChiSplitChain
