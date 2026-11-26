import Bilevel.ChiUniformPhysicalBudgets
import Bilevel.ChiExtensionLedgerAbsorption
import Bilevel.SmallGapLiftSupport

/-! One fixed choice of fine, curvature, and accuracy constants pays both
full Hessians, the mean third derivative, and the finest active force.
The accuracy window remains c*min(L,sqrt(L*Delta)). -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiCurvatureSchedule ChiIndependentWidths

def wideHessianConstant (Cb η₀ η cn CR cms : ℝ) : ℝ :=
  192*SmallGapLiftSupport.C*Cb*(cn/η^2)^(2/3:ℝ)+
    1104*SmallGapLiftSupport.C*Cb/(cms*Real.sqrt (6*η₀))+144*CR*Cb

def wideForceConstant (Braw cms Cb η₀ : ℝ) : ℝ :=
  96*SmallGapLiftSupport.C*Braw*cms*Cb/Real.sqrt (6*η₀)

def wideThirdCoarse (η₀ cn η : ℝ) : ℝ :=
  64*SmallGapLiftSupport.C*η₀*(cn/η^2)^(1/3:ℝ)

def wideThirdRadial (ζ η₀ : ℝ) : ℝ := 72*ζ*η₀

theorem exists_wide_extension_constants
    {C Bf Bi Braw Cb η₀ η t cn ζ CR cms δ Cleg cold : ℝ}
    (hC : 1≤C) (hBf : 1≤Bf) (hBi : 1≤Bi) (hBraw : 0≤Braw)
    (hCb : 0<Cb) (hη₀ : 0<η₀) (hη : 0<η) (ht : 0<t)
    (hcn : 0<cn) (hζ : 0<ζ) (hCR : 0<CR) (hcms : 0<cms)
    (hδ : 0<δ) (hCleg : 1≤Cleg) (hcold : 0<cold) :
    ∃ Cf CT c : ℝ,1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧ c≤cold ∧
      2*Cleg*(max 1 (116*SmallGapLiftSupport.C/cms^2)*Bf^2)≤Cf ∧
      2*Cleg*(max 1 (116*SmallGapLiftSupport.C/cms^2)*Bi^2)≤Cf ∧
      4*(Bf^2/t)^2≤Cf ∧ 4*(Bi^2/t)^2≤Cf ∧ 4/t^2≤Cf ∧
      (C^2/(t*η))^2≤CT ∧ (1/(t*η))^2≤CT ∧ max 1 (12*η₀)*Cf≤CT ∧
      ∀ L μ θ ε a : ℝ,0<L → 0<μ → 1≤θ → 0≤ε → ε≤c*L →
        1≤chosenDepth θ → 1≤a → a≤scale θ CT 6 →
        let J := chosenDepth θ
        1≤fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J ∧
        wideHessianConstant Cb η₀ η cn CR cms*(ε/L)≤δ ∧
        wideForceConstant Braw cms Cb η₀*(ε/L)≤1/128 ∧
        (wideThirdCoarse η₀ cn η*C^(J+2)+wideThirdRadial ζ η₀)*((J:ℝ)+1)^2*scale θ CT 6+
          2*θ/(3*(2*Cleg))≤2*θ/(3*Cleg) := by
  let Q := max 1 (116*SmallGapLiftSupport.C/cms^2)
  let Cf := 1+2*Cleg*(Q*Bf^2)+2*Cleg*(Q*Bi^2)+4*(Bf^2/t)^2+4*(Bi^2/t)^2+4/t^2
  let S := wideThirdCoarse η₀ cn η
  let V := wideThirdRadial ζ η₀
  let A₃ := max 1 (S+V)*(C+1)^2
  let CT := 1+(C^2/(t*η))^2+(1/(t*η))^2+max 1 (12*η₀)*Cf+3*Cleg*A₃
  let H := wideHessianConstant Cb η₀ η cn CR cms
  let F := wideForceConstant Braw cms Cb η₀
  let c := min cold (min 1 (min (δ/(H+1)) (1/(128*(F+1)))))
  have hCn := SmallGapLiftSupport.C_pos
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hM : 0<Cleg := by linarith
  have hfn : 0≤2*Cleg*(Q*Bf^2) := by positivity
  have hin : 0≤2*Cleg*(Q*Bi^2) := by positivity
  have htn : 0≤4/t^2 := by positivity
  have hCf : 1≤Cf := by dsimp [Cf]; nlinarith only [hfn,hin,htn,sq_nonneg (Bf^2/t),sq_nonneg (Bi^2/t)]
  have hCfF : 2*Cleg*(Q*Bf^2)≤Cf := by dsimp [Cf]; nlinarith only [hin,htn,sq_nonneg (Bf^2/t),sq_nonneg (Bi^2/t)]
  have hCfI : 2*Cleg*(Q*Bi^2)≤Cf := by dsimp [Cf]; nlinarith only [hfn,htn,sq_nonneg (Bf^2/t),sq_nonneg (Bi^2/t)]
  have hCfF2 : 4*(Bf^2/t)^2≤Cf := by dsimp [Cf]; nlinarith only [hfn,hin,htn,sq_nonneg (Bi^2/t)]
  have hCfI2 : 4*(Bi^2/t)^2≤Cf := by dsimp [Cf]; nlinarith only [hfn,hin,htn,sq_nonneg (Bf^2/t)]
  have hCf1 : 4/t^2≤Cf := by dsimp [Cf]; nlinarith only [hfn,hin,sq_nonneg (Bf^2/t),sq_nonneg (Bi^2/t)]
  have hCfp : 0<Cf := by linarith
  have hS : 0≤S := by dsimp [S,wideThirdCoarse]; positivity
  have hV : 0≤V := by dsimp [V,wideThirdRadial]; positivity
  have hA₃ : 0≤A₃ := by dsimp [A₃]; positivity
  have hctfine : 0≤max 1 (12*η₀)*Cf := by positivity
  have hctthird : 0≤3*Cleg*A₃ := by positivity
  have hxc := sq_nonneg (C^2/(t*η))
  have hxr := sq_nonneg (1/(t*η))
  have hprefix : 0≤1+(C^2/(t*η))^2+(1/(t*η))^2 := add_nonneg (add_nonneg zero_le_one hxc) hxr
  have hCT : 1≤CT := by
    exact (le_add_of_nonneg_right hxc).trans
      ((le_add_of_nonneg_right hxr).trans
        ((le_add_of_nonneg_right hctfine).trans (le_add_of_nonneg_right hctthird)))
  have hCTc : (C^2/(t*η))^2≤CT := by
    exact (le_add_of_nonneg_left zero_le_one).trans
      ((le_add_of_nonneg_right hxr).trans
        ((le_add_of_nonneg_right hctfine).trans (le_add_of_nonneg_right hctthird)))
  have hCTr : (1/(t*η))^2≤CT := by
    exact (le_add_of_nonneg_left (add_nonneg zero_le_one hxc)).trans
      ((le_add_of_nonneg_right hctfine).trans (le_add_of_nonneg_right hctthird))
  have hCTf : max 1 (12*η₀)*Cf≤CT :=
    (le_add_of_nonneg_left hprefix).trans (le_add_of_nonneg_right hctthird)
  have hCT3 : 3*Cleg*A₃≤CT := le_add_of_nonneg_left (add_nonneg hprefix hctfine)
  have hCTp : 0<CT := by linarith
  have hH : 0≤H := by dsimp [H,wideHessianConstant]; positivity
  have hF : 0≤F := by dsimp [F,wideForceConstant]; positivity
  have hc : 0<c := by dsimp [c]; positivity
  have hcold' : c≤cold := min_le_left _ _
  have hc1 : c≤1 := (min_le_right _ _).trans (min_le_left _ _)
  have hcH : c≤δ/(H+1) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcF : c≤1/(128*(F+1)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨Cf,CT,c,hCf,hCT,hc,hc1,hcold',hCfF,hCfI,hCfF2,hCfI2,hCf1,hCTc,hCTr,hCTf,?_⟩
  intro L μ θ ε a hL hμ hθ _hε hεc hJ ha haT
  dsimp only
  have hec : ε/L≤c := (div_le_iff₀ hL).mpr hεc
  have hpaidH : H*c≤δ := by
    have hh := (le_div_iff₀ (show 0<H+1 by positivity)).mp hcH
    nlinarith only [hh,hc]
  have hpaidF : F*c≤1/128 := by
    have hh := (le_div_iff₀ (show 0<128*(F+1) by positivity)).mp hcF
    nlinarith only [hh,hc]
  have hthird := source_extension_third_absorption hS hV hC (show 0≤θ by linarith)
    (show 1≤3*Cleg by linarith) hCTp hCT3 6 (by norm_num)
  refine ⟨fineParameter_ge_one (by linarith) hμ hL hη₀ (by linarith) hCf hCTp hCTf 6 (by norm_num) hJ haT,
    (mul_le_mul_of_nonneg_left hec hH).trans hpaidH,
    (mul_le_mul_of_nonneg_left hec hF).trans hpaidF,?_⟩
  have he : θ/(3*Cleg)+2*θ/(3*(2*Cleg))=2*θ/(3*Cleg) := by field_simp; ring
  exact (add_le_add_right hthird _).trans_eq he

theorem wide_source_force_budget {L μ η₀ Cb ε κ θ a t η Cf Braw cms : ℝ}
    (hL : 0<L) (hμ : 0<μ) (hη₀ : 0<η₀) (hCb : 0≤Cb) (hε : 0≤ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hθκ : θ≤κ^2) (ha : 1≤a) (ht : 0<t) (ht1 : t≤1)
    (hη : 0<η) (hCf : 0<Cf) (hpay : 4/t^2≤Cf) (hB : 0≤Braw) (hc : 0≤cms)
    (J : ℕ) (hJ : 1≤J)
    (hsmall : wideForceConstant Braw cms Cb η₀*(ε/L)≤1/128) :
    let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
    let β := η^J*h/a
    let v := fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J
    1≤v → 2*SmallGapLiftSupport.C*Braw*cms*(η₀*L*a)*β^2/
      (normalCoefficient L J*Real.sqrt v)≤β/128 := by
  dsimp only
  intro hv
  have hpay' : 4*((1:ℝ)^2/t)^2≤Cf := by convert hpay using 1; ring
  have hs := wide_fine_hessian_factor hL hμ hη₀ hCb hε hκ hθ hθκ ha
    (by norm_num : (1:ℝ)≤1) ht ht1 hη hCf hpay' J hJ
  simp only [one_pow,one_mul] at hs
  have hC := SmallGapLiftSupport.C_pos
  have hap : 0<a := by linarith
  have hβ : 0≤η^J*middleWidth Cb ε (κ/6) (η₀*L) (t*η) J/a := by unfold middleWidth; positivity
  have hh := source_force_from_fine_factor hC.le hB hc (show 0≤η₀*L*a by positivity)
    hβ (normalCoefficient_pos hL hJ) hv hs
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_right hsmall hβ
  convert hm using 1 <;> dsimp only [wideForceConstant] <;> ring

end Bilevel.ChiExtensionCalibration

