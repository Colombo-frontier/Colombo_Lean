import Bilevel.ChiUniformWidthCalibration

/-! Full-window macro/middle width calibration with actual fixed depth 1.
The public constants do not involve theta or a chosen log-log depth. -/
noncomputable section
namespace Bilevel.ChiIndependentWidths

theorem exists_fixed_width_calibration {η₀ bStar cS cn Cb t η ξ c₁ cold : ℝ}
    (hη₀ : 0<η₀) (hη₀1 : η₀≤1) (hb : 0<bStar) (hcn : 0<cn) (hCb : 0<Cb)
    (ht : 0<t) (hη : 0<η) (hξ : 0<ξ) (hc₁ : 0<c₁) (hcold : 0<cold)
    (hmacro : bStar^2≤cS/128) :
    ∃ c : ℝ,0<c ∧ c≤1 ∧ c≤cold ∧
      ∀ L Δ κ ε : ℝ,0<L → 0<Δ → 2≤κ → 0<ε → ε≤c*min L (Real.sqrt (L*Δ)) →
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1
      0<h/b ∧ h/b≤ξ ∧ ε≤c₁*(η₀*L)*b ∧
      64≤macroLength cS Δ (η₀*L) b ∧ 64≤middleLength cn b h ∧
      cS*cn*Δ/(4*(η₀*L)*h^2)≤((macroLength cS Δ (η₀*L) b*middleLength cn b h:ℕ):ℝ) := by
  let gain := (1/3)*(t*η)
  let cFloor := accuracyConstant η₀ bStar cn gain Cb
  let cRatio := accuracyConstant η₀ bStar (128*ξ^2) gain Cb
  let c := min cold (min 1 (min cFloor (min cRatio (c₁*η₀*bStar))))
  have hgain : 0<gain := by dsimp [gain]; positivity
  have hf : 0<cFloor := by dsimp [cFloor,accuracyConstant]; positivity
  have hr : 0<cRatio := by dsimp [cRatio,accuracyConstant]; positivity
  have hc : 0<c := by dsimp [c]; positivity
  have hc1 : c≤1 := (min_le_right _ _).trans (min_le_left _ _)
  have hcf : c≤cFloor := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcr : c≤cRatio := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcm : c≤c₁*η₀*bStar := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨c,hc,hc1,min_le_left _ _,?_⟩
  intro L Δ κ ε hL hΔ hκ hε hacc
  dsimp only
  have hK : 0<κ/6 := by linarith only [hκ]
  have hbp := macroWidth_pos hb hΔ (mul_pos hη₀ hL)
  have hhp : 0<middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1 := by unfold middleWidth; positivity
  have hKGain : gain≤(κ/6)*(t*η)^1 := by
    have hh := mul_le_mul_of_nonneg_right (show (1:ℝ)/3≤κ/6 by linarith only [hκ]) (mul_pos ht hη).le
    simpa only [pow_one] using hh
  have hscale : 0≤min L (Real.sqrt (L*Δ)) := by positivity
  have haf := hacc.trans (mul_le_mul_of_nonneg_right hcf hscale)
  have har := hacc.trans (mul_le_mul_of_nonneg_right hcr hscale)
  have hfloor := public_accuracy_width 1 hL hΔ hη₀ hη₀1 hb hcn hgain hCb hK (mul_pos ht hη) hε hKGain haf
  have hs := public_accuracy_width 1 hL hΔ hη₀ hη₀1 hb (show 0<128*ξ^2 by positivity) hgain hCb hK
    (mul_pos ht hη) hε hKGain har
  have hratio : middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1/macroWidth bStar Δ (η₀*L)≤ξ := by
    apply (div_le_iff₀ hbp).mpr
    apply (sq_le_sq₀ hhp.le (mul_pos hξ hbp).le).mp
    change (middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1)^2≤
      (128*ξ^2)*macroWidth bStar Δ (η₀*L)^2/128 at hs
    nlinarith only [hs]
  obtain ⟨hS,hn,hcount⟩ := independent_width_certificate hb hcn hΔ (mul_pos hη₀ hL) hhp hmacro hfloor
  exact ⟨div_pos hhp hbp,hratio,public_accuracy_macro_force hL hΔ hη₀ hη₀1 hb hc.le hcm hacc,hS,hn,hcount⟩

end Bilevel.ChiIndependentWidths
