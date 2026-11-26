import Bilevel.ChiFixedDepthPhysical
import Bilevel.SmallGapLiftSupport

/-! Fixed numerical parameters for the bounded-theta fallback. Fine Cf
is selected before the small curvature coefficient, avoiding a large-theta
threshold while paying the actual J=1 fine and coarse third derivatives. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

def fixedDepthHessian (C Cb η₀ η t cn CR cms : ℝ) : ℝ :=
  96*SmallGapLiftSupport.C*C^3*Cb/(t*η)*(cn/η^2)^(2/3:ℝ)+
    1104*SmallGapLiftSupport.C*Cb/(cms*Real.sqrt (6*η₀))+72*CR*Cb/(t*η)

def fixedDepthThird (C cn η ζ : ℝ) : ℝ :=
  64*SmallGapLiftSupport.C*C^3*(cn/η^2)^(1/3:ℝ)+72*ζ

theorem exists_fixed_depth_parameters {Cu C Ba Bi Cb t η cn ζ CR cms cold : ℝ}
    (hCu : 1≤Cu) (hC : 1≤C) (hBa : 1≤Ba) (hBi : 1≤Bi)
    (hCb : 0<Cb) (ht : 0<t) (hη : 0<η) (hcn : 0<cn) (hζ : 0<ζ)
    (hCR : 0<CR) (hcms : 0<cms) (hcold : 0<cold) :
    ∃ η₀ Cf c : ℝ,0<η₀ ∧ η₀≤1 ∧ η₀≤1/(4*Cu) ∧
      1≤Cf ∧ 6*(max 1 (116*SmallGapLiftSupport.C/cms^2)*Ba^2)≤Cf ∧
      6*(max 1 (116*SmallGapLiftSupport.C/cms^2)*Bi^2)≤Cf ∧
      4*(Ba^2/t)^2≤Cf ∧ 4*(Bi^2/t)^2≤Cf ∧
      0<c ∧ c≤1 ∧ c≤cold ∧
      fixedDepthThird C cn η ζ*η₀+1/9≤2/9 ∧
      ∀ L μ ε : ℝ,0<L → 0<μ → 0≤ε → ε≤c*L →
        1≤fineParameter μ (3*μ/2) (η₀*L) (normalCoefficient L 1) Cf 1 ∧
        fixedDepthHessian C Cb η₀ η t cn CR cms*(ε/L)≤1/12 := by
  let Q := max 1 (116*SmallGapLiftSupport.C/cms^2)
  let Cf := 1+6*(Q*Ba^2)+6*(Q*Bi^2)+4*(Ba^2/t)^2+4*(Bi^2/t)^2
  have hnormal := SmallGapLiftSupport.C_pos
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hBa0 : 0≤Ba := by linarith only [hBa]
  have hBi0 : 0≤Bi := by linarith only [hBi]
  have hC0 : 0≤C := by linarith only [hC]
  have hCu0 : 0<Cu := by linarith only [hCu]
  have ha : 0≤6*(Q*Ba^2) := by positivity
  have hi : 0≤6*(Q*Bi^2) := by positivity
  have hCf : 1≤Cf := by dsimp [Cf]; nlinarith only [ha,hi,sq_nonneg (Ba^2/t),sq_nonneg (Bi^2/t)]
  have hCfa : 6*(Q*Ba^2)≤Cf := by dsimp [Cf]; nlinarith only [hi,sq_nonneg (Ba^2/t),sq_nonneg (Bi^2/t)]
  have hCfi : 6*(Q*Bi^2)≤Cf := by dsimp [Cf]; nlinarith only [ha,sq_nonneg (Ba^2/t),sq_nonneg (Bi^2/t)]
  have hCfa2 : 4*(Ba^2/t)^2≤Cf := by dsimp [Cf]; nlinarith only [ha,hi,sq_nonneg (Bi^2/t)]
  have hCfi2 : 4*(Bi^2/t)^2≤Cf := by dsimp [Cf]; nlinarith only [ha,hi,sq_nonneg (Ba^2/t)]
  have hCfp : 0<Cf := by linarith only [hCf]
  let V := fixedDepthThird C cn η ζ
  have hV : 0≤V := by dsimp [V,fixedDepthThird]; positivity
  let den := 1+4*Cu+24*Cf^2+9*V
  let η₀ := 1/den
  have hd1 : 1≤den := by dsimp [den]; nlinarith only [hCu,hV,sq_nonneg Cf]
  have hd : 0<den := by linarith only [hd1]
  have hη₀ : 0<η₀ := by dsimp [η₀]; positivity
  have hη₀1 : η₀≤1 := (div_le_one hd).mpr hd1
  have hηCu : η₀≤1/(4*Cu) := by
    apply one_div_le_one_div_of_le (by positivity)
    dsimp [den]
    nlinarith only [hV,sq_nonneg Cf]
  have hηCf : η₀≤1/(24*Cf^2) := by
    apply one_div_le_one_div_of_le (by positivity)
    dsimp [den]
    nlinarith only [hCu,hV]
  have hthird : V*η₀+1/9≤2/9 := by
    have hh : V/den≤1/9 := (div_le_iff₀ hd).mpr (by dsimp [den]; nlinarith only [hCu,sq_nonneg Cf])
    dsimp only [η₀]
    rw [show V*(1/den)=V/den by ring]
    linarith only [hh]
  let H := fixedDepthHessian C Cb η₀ η t cn CR cms
  have hH : 0≤H := by dsimp [H,fixedDepthHessian]; positivity
  let c := min cold (min 1 (1/(12*(H+1))))
  have hc : 0<c := by dsimp [c]; positivity
  have hc1 : c≤1 := (min_le_right _ _).trans (min_le_left _ _)
  have hccold : c≤cold := min_le_left _ _
  have hcH : c≤1/(12*(H+1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η₀,Cf,c,hη₀,hη₀1,hηCu,hCf,hCfa,hCfi,hCfa2,hCfi2,hc,hc1,hccold,hthird,?_⟩
  intro L μ ε hL hμ _hε hacc
  refine ⟨fixed_depth_fine_ge_one hμ hL hη₀ hCfp hηCf,?_⟩
  have hr : ε/L≤c := (div_le_iff₀ hL).mpr hacc
  have hh := mul_le_mul_of_nonneg_left hr hH
  have hc' := (le_div_iff₀ (show 0<12*(H+1) by positivity)).mp hcH
  change H*(ε/L)≤1/12
  nlinarith only [hh,hc',hc]

end Bilevel.ChiExtensionCalibration
