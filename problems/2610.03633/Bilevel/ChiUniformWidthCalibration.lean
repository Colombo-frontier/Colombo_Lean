import Bilevel.ChiIndependentWidths
import Bilevel.ChiCurvatureThreshold

/-! The manuscript's full public accuracy window, with independent macro
and middle widths. All constants are chosen before public budgets. -/
noncomputable section
namespace Bilevel.ChiIndependentWidths

def middleWidth (Cb ε K L₀ ω : ℝ) (J : ℕ) : ℝ :=
  Cb*ε/(K*L₀*ω^J)

theorem uniform_polylog_envelope {A κ θ : ℝ} (hA : 1≤A) (hκ : 0≤κ)
    (hθ : 1≤θ) (hθκ : θ≤κ^2) (p : ℕ) :
    A^(chosenDepth θ+1)*((chosenDepth θ:ℝ)+1)^p ≤
      Real.exp (ChiCurvatureSchedule.thresholdExponent A p)*κ := by
  have hs : Real.sqrt θ≤κ := Real.sqrt_le_iff.mpr ⟨hκ,hθκ⟩
  exact (ChiCurvatureSchedule.depth_denominator_bound hθ hA p).trans
    (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le)

theorem public_accuracy_macro_force {L Δ η bStar c c₁ ε : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hη : 0<η) (hη1 : η≤1)
    (_hb : 0<bStar) (hc : 0≤c) (hcsmall : c≤c₁*η*bStar)
    (hacc : ε≤c*min L (Real.sqrt (L*Δ))) :
    ε≤c₁*(η*L)*macroWidth bStar Δ (η*L) := by
  have hs := public_scale_le (mul_pos hη hL) hΔ (by nlinarith : η*L≤L)
  have hm := mul_le_mul_of_nonneg_right hcsmall
    (show 0≤L*min 1 (Real.sqrt (Δ/(η*L))) by positivity)
  calc
    ε≤c*(L*min 1 (Real.sqrt (Δ/(η*L)))) :=
      hacc.trans (mul_le_mul_of_nonneg_left hs hc)
    _≤(c₁*η*bStar)*(L*min 1 (Real.sqrt (Δ/(η*L)))) := hm
    _=c₁*(η*L)*macroWidth bStar Δ (η*L) := by unfold macroWidth; ring

/-- The same fixed accuracy constant pays any prescribed base resolution
and macro-gradient slack, in addition to both actual natural floors. -/
theorem exists_uniform_width_calibration {η bStar cS cn cK Cb ω ξ c₁ : ℝ}
    (hη : 0<η) (hη1 : η≤1) (hb : 0<bStar) (hcn : 0<cn)
    (hcK : 0<cK) (hCb : 0<Cb) (hω : 0<ω) (hξ : 0<ξ) (hc₁ : 0<c₁)
    (hmacro : bStar^2≤cS/128) :
    ∃ c : ℝ,0<c ∧ c≤1 ∧
      ∀ L Δ κ θ K ε : ℝ,0<L → 0<Δ → 2≤κ → 1≤θ → θ≤κ^2 →
        cK*κ≤K → 0<ε → ε≤c*min L (Real.sqrt (L*Δ)) →
        let J := chosenDepth θ
        let b := macroWidth bStar Δ (η*L)
        let h := middleWidth Cb ε K (η*L) ω J
        0<h/b ∧ h/b≤ξ ∧ ε≤c₁*(η*L)*b ∧
        64≤macroLength cS Δ (η*L) b ∧ 64≤middleLength cn b h ∧
        cS*cn*Δ/(4*(η*L)*h^2)≤
          ((macroLength cS Δ (η*L) b*middleLength cn b h:ℕ):ℝ) := by
  let gain := cK*depthGain ω
  let cFloor := accuracyConstant η bStar cn gain Cb
  let cRatio := accuracyConstant η bStar (128*ξ^2) gain Cb
  let c := min 1 (min cFloor (min cRatio (c₁*η*bStar)))
  have hgain : 0<gain := mul_pos hcK (depthGain_pos ω)
  have hf : 0<cFloor := uniform_accuracy_constant_pos hη hb hcn hcK hCb
  have hr : 0<cRatio := uniform_accuracy_constant_pos hη hb (by positivity) hcK hCb
  have hc : 0<c := by dsimp [c]; positivity
  have hcf : c≤cFloor := (min_le_right _ _).trans (min_le_left _ _)
  have hcr : c≤cRatio := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcm : c≤c₁*η*bStar := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c,hc,min_le_left _ _,?_⟩
  intro L Δ κ θ K ε hL hΔ hκ hθ hθκ hK hε hacc
  dsimp only
  have hKp : 0<K := (mul_pos hcK (by linarith : 0<κ)).trans_le hK
  have hbp := macroWidth_pos hb hΔ (mul_pos hη hL)
  have hhp : 0<middleWidth Cb ε K (η*L) ω (chosenDepth θ) := by
    unfold middleWidth; positivity
  have hscale : 0≤min L (Real.sqrt (L*Δ)) := by positivity
  have haf := hacc.trans (mul_le_mul_of_nonneg_right hcf hscale)
  have har := hacc.trans (mul_le_mul_of_nonneg_right hcr hscale)
  have hKGain : gain≤K*ω^chosenDepth θ := by
    have hg := uniform_depth_gain (chosenDepth θ) hκ (by linarith) hθκ hω (chosenDepth_bound hθ)
    calc
      gain≤cK*(κ*ω^chosenDepth θ) := mul_le_mul_of_nonneg_left hg hcK.le
      _=(cK*κ)*ω^chosenDepth θ := by ring
      _≤K*ω^chosenDepth θ := mul_le_mul_of_nonneg_right hK (by positivity)
  have hs := public_accuracy_width (chosenDepth θ) hL hΔ hη hη1 hb
    (show 0<128*ξ^2 by positivity) hgain hCb hKp hω hε hKGain har
  change middleWidth Cb ε K (η*L) ω (chosenDepth θ)^2≤
    (128*ξ^2)*macroWidth bStar Δ (η*L)^2/128 at hs
  have hratio : middleWidth Cb ε K (η*L) ω (chosenDepth θ)/macroWidth bStar Δ (η*L)≤ξ := by
    apply (div_le_iff₀ hbp).mpr
    apply (sq_le_sq₀ hhp.le (mul_pos hξ hbp).le).mp
    nlinarith only [hs]
  obtain ⟨hS,hn,hcount⟩ := uniform_floor_certificate hL hΔ hη hη1 hb hcn hcK hCb
    hκ hθ hθκ hK hω hε hmacro haf
  exact ⟨div_pos hhp hbp,hratio,public_accuracy_macro_force hL hΔ hη hη1 hb hc.le hcm hacc,
    hS,hn,hcount⟩

end Bilevel.ChiIndependentWidths
