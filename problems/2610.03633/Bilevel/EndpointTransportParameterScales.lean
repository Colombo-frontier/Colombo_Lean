import Bilevel.EndpointTransportGainCalibration
import Bilevel.ChiUniformParameterCertificate

/-! Fixed numerical choices for the physical gain. The condition number
is unchanged; the auxiliary accuracy is at most 32 times the public one. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open ChiRecursive ChiIndependentWidths ChiExtensionCalibration ChiCurvatureSchedule EndpointTransportNormalization

theorem physical_parameter_scales
    {C B η₀ bStar Cb η t cn ζ CR cms cold : ℝ}
    (hC : 1≤C) (hB : 1≤B) (hη₀ : 0<η₀) (hη₀1 : η₀≤1) (hbs : 0<bStar)
    (hCb : 0<Cb) (hη : 0<η) (hη1 : η≤1) (ht : 0<t)
    (hcn : 0<cn) (hlen : 128≤cn/η^2) (hζ : 0<ζ) (hCR : 0<CR)
    (hcms : 0<cms) (hcold : 0<cold) :
    ∃ Cf CT c : ℝ,1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧ c≤cold ∧
      6*(max 1 (24*SmallGapLiftSupport.C/cms^2)*B^2)≤Cf ∧
      4*(B^2/t)^2≤Cf ∧ (C^2/(t*η))^2≤CT ∧ (1/(t*η))^2≤CT ∧
    ∀ L μ κ θ Δ ε : ℝ,0<L → 0<μ → 3200≤κ → θ≤κ^2 → wideBranchThreshold CT≤θ →
      0<Δ → 0<ε → ε≤c*min L (Real.sqrt (L*Δ)) →
      let J := chosenDepth θ
      let T := scale θ CT 6
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth Cb ε (EndpointTransportNormalization.gain κ) (η₀*L) (t*η) J
      let Kg := b/h
      let e := calibrationAccuracy κ ε
      1≤θ ∧ 1≤J ∧ 1≤T ∧ 0<b ∧ 0<h ∧ 0<Kg ∧ 1/η≤Kg ∧
      b/Kg=middleWidth Cb e (κ/6) (η₀*L) (t*η) J ∧
      (∀ j,0<resolution η Kg j ∧ resolution η Kg j≤1 ∧ 128≤cn/(resolution η Kg j)^2) ∧
      1≤fineParameter (θ*μ) (3*μ/2) (η₀*L*curvature T J) (normalCoefficient L J) Cf J ∧
      wideHessianConstant Cb η₀ η cn CR cms*(e/L)≤1/12 ∧
      (wideThirdCoarse η₀ cn η*C^(J+2)+wideThirdRadial ζ η₀)*((J:ℝ)+1)^2*T+
        2*θ/(3*6)≤2*θ/9 := by
  obtain ⟨cw,hcw,_hcw1,hwidthcal⟩ := exists_uniform_width_calibration
    (cS:=128*bStar^2) hη₀ hη₀1 hbs hcn (by norm_num : (0:ℝ)<1/6) hCb (mul_pos ht hη) hη
    (by norm_num : (0:ℝ)<1) (by ring_nf; rfl)
  obtain ⟨Cf,CT,c₀,hCf,hCT,hc₀,hc₀1,hcold₀,hCff,_hCfi,hCfw,_hCfiw,_hForce,hCTc,hCTr,_hCTf,hnum⟩ :=
    exists_wide_extension_constants (C:=C) (Bf:=B) (Bi:=1) (Braw:=0) (δ:=1/12) (Cleg:=3)
      hC hB (by norm_num) (by norm_num) hCb hη₀ hη ht hcn hζ hCR hcms
      (by norm_num) (by norm_num) (lt_min hcold hcw)
  have hCfFine : 6*(max 1 (24*SmallGapLiftSupport.C/cms^2)*B^2)≤Cf := by
    have hCn := SmallGapLiftSupport.C_pos
    apply le_trans _ hCff
    gcongr <;> norm_num
  have hsmall : c₀/32≤c₀ := by nlinarith
  refine ⟨Cf,CT,c₀/32,hCf,hCT,by positivity,hsmall.trans hc₀1,
    hsmall.trans (hcold₀.trans (min_le_left _ _)),hCfFine,hCfw,hCTc,hCTr,?_⟩
  intro L μ κ θ Δ ε hL hμ hκ hθκ hbranch hΔ hε hacc
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth Cb ε (EndpointTransportNormalization.gain κ) (η₀*L) (t*η) J
  let Kg := b/h
  let e := calibrationAccuracy κ ε
  obtain ⟨hθ,hJ,hT2⟩ := wide_branch_conditions hCT hbranch
  have hT : 1≤T := (by norm_num : (1:ℝ)≤2).trans hT2
  have hbp : 0<b := macroWidth_pos hbs hΔ (mul_pos hη₀ hL)
  have hgp := gain_pos hκ
  have hhp : 0<h := by dsimp [h,middleWidth]; positivity
  have hKg : 0<Kg := div_pos hbp hhp
  have hep : 0<e := calibrationAccuracy_pos hκ hε
  have heacc : e≤c₀*min L (Real.sqrt (L*Δ)) := calibration_accuracy_window hκ hε.le hacc
  have hecw : e≤cw*min L (Real.sqrt (L*Δ)) :=
    heacc.trans (mul_le_mul_of_nonneg_right (hcold₀.trans (min_le_right _ _)) (by positivity))
  have hcwidth := hwidthcal L Δ κ θ (κ/6) e hL hΔ (by linarith) hθ hθκ (by ring_nf; rfl) hep hecw
  dsimp only at hcwidth
  have hcal : middleWidth Cb e (κ/6) (η₀*L) (t*η) J=h := calibration_middleWidth hκ Cb ε (η₀*L) (t*η) J
  rw [hcal] at hcwidth
  have hKgη : 1/η≤Kg := by
    apply (div_le_iff₀ hη).mpr
    have hh := (div_le_iff₀ hbp).mp hcwidth.2.1
    dsimp [Kg]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hhp).mpr
    nlinarith only [hh]
  have hgain : b/Kg=middleWidth Cb e (κ/6) (η₀*L) (t*η) J := by
    rw [hcal]
    change b/(b/h)=h
    field_simp
  have hres := base_resolution_positive hη hKg
  have hresle := base_resolution_le hKg hKgη hη
  have hrange (j : ℕ) : 0<resolution η Kg j ∧ resolution η Kg j≤1 ∧ 128≤cn/(resolution η Kg j)^2 := by
    refine ⟨hres j,(hresle j).trans hη1,hlen.trans ?_⟩
    apply div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (hres j))
    exact pow_le_pow_left₀ (hres j).le (hresle j) 2
  have heL : e≤c₀*L := heacc.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hc₀.le)
  have hpaid := hnum L μ θ e (curvature T J) hL hμ hθ hep.le heL hJ
    (curvature_bounds hT J).1 (curvature_bounds hT J).2
  refine ⟨hθ,hJ,hT,hbp,hhp,hKg,hKgη,hgain,hrange,hpaid.1,hpaid.2.1,?_⟩
  convert hpaid.2.2.2 using 1 <;> norm_num

end Bilevel.EndpointTransportResponse
