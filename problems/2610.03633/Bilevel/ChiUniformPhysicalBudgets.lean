import Bilevel.ChiUniformHessianFactors

/-! Full-window Hessian and deepest-source-force factors at the actual
independent middle width h0. No hidden-force/blind-width ratio occurs. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiCurvatureSchedule ChiIndependentWidths

theorem sqrt_depth_product (J : ℕ) :
    Real.sqrt (2*(J:ℝ))*(J:ℝ)≤2*((J:ℝ)+1)^2 := by
  have hh := mul_le_mul_of_nonneg_right (sqrt_two_depth_le J) (Nat.cast_nonneg J : (0:ℝ)≤J)
  nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) J]

theorem wide_coarse_hessian_factor {L η₀ Cb ε κ θ C ω CT : ℝ}
    (hL : 0<L) (hη₀ : 0<η₀) (hCb : 0≤Cb) (hε : 0≤ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hθκ : θ≤κ^2) (hC : 1≤C) (hω : 0<ω) (hω1 : ω≤1)
    (hCT : 0<CT) (hpay : (C^2/ω)^2≤CT) :
    let J := chosenDepth θ
    let h := middleWidth Cb ε (κ/6) (η₀*L) ω J
    C^(J+2)*((η₀*L)*h/normalCoefficient L J)*(J:ℝ)*Real.sqrt (scale θ CT 6)≤
      48*Cb*(ε/L) := by
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  have hK : 0<κ/6 := by positivity
  have hfac := geometric_sqrt_scale_factor hθ hC hω hω1 hCT hpay
  have hp : Real.sqrt (2*(J:ℝ))*(J:ℝ)*(C^(J+2)/ω^J)*Real.sqrt T≤2*Real.sqrt θ := by
    calc
      _≤(2*((J:ℝ)+1)^2)*(C^(J+2)/ω^J)*Real.sqrt T := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (sqrt_depth_product J) (by positivity))
          (Real.sqrt_nonneg _)
      _=2*(C^(J+2)/ω^J*((J:ℝ)+1)^2*Real.sqrt T) := by ring
      _≤2*Real.sqrt θ := mul_le_mul_of_nonneg_left hfac (by norm_num)
  have hr : (Real.sqrt (2*(J:ℝ))*(J:ℝ)*(C^(J+2)/ω^J)*Real.sqrt T)/(κ/6)≤12 := by
    have hh := div_le_div_of_nonneg_right hp hK.le
    have hs := conditioning_sqrt_ratio hκ hθκ
    calc
      _≤2*(Real.sqrt θ/(κ/6)) := by convert hh using 1; ring
      _≤12 := by linarith only [hs]
  have he : C^(J+2)*((η₀*L)*middleWidth Cb ε (κ/6) (η₀*L) ω J/normalCoefficient L J)*
      (J:ℝ)*Real.sqrt T=
      (4*Cb*(ε/L))*((Real.sqrt (2*(J:ℝ))*(J:ℝ)*(C^(J+2)/ω^J)*Real.sqrt T)/(κ/6)) := by
    unfold middleWidth normalCoefficient
    field_simp
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hr (show 0≤4*Cb*(ε/L) by positivity)
  nlinarith only [hh]

theorem wide_fine_hessian_factor {L μ η₀ Cb ε κ θ a B t η Cf : ℝ}
    (hL : 0<L) (hμ : 0<μ) (hη₀ : 0<η₀) (hCb : 0≤Cb) (hε : 0≤ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hθκ : θ≤κ^2) (ha : 1≤a) (hB : 1≤B)
    (ht : 0<t) (ht1 : t≤1) (hη : 0<η) (hCf : 0<Cf)
    (hpay : 4*(B^2/t)^2≤Cf) (J : ℕ) (hJ : 1≤J) :
    let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
    let β := η^J*h/a
    let v := fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J
    B^(J+2)*((η₀*L*a)*β/normalCoefficient L J)*Real.sqrt v≤
      (48*Cb/Real.sqrt (6*η₀))*(ε/L) := by
  dsimp only
  let v := fineParameter (θ*μ) (3*μ/2) (η₀*L*a) (normalCoefficient L J) Cf J
  have hK : 0<κ/6 := by positivity
  have hs0 : 0<Real.sqrt (6*η₀) := Real.sqrt_pos.mpr (by positivity)
  have hfac := geometric_fine_factor hθ hμ hL hη₀ ha hCf hB ht ht1 hpay J hJ
  have hp : (B^(J+2)/t^J)*Real.sqrt (2*(J:ℝ))*Real.sqrt v≤
      2*Real.sqrt θ/Real.sqrt (6*η₀) := by
    calc
      _≤(B^(J+2)/t^J)*(2*((J:ℝ)+1))*Real.sqrt v := by
        gcongr
        exact sqrt_two_depth_le J
      _=2*(B^(J+2)/t^J*((J:ℝ)+1)*Real.sqrt v) := by ring
      _≤2*(Real.sqrt θ/Real.sqrt (6*η₀)) := mul_le_mul_of_nonneg_left hfac (by norm_num)
      _=_ := by ring
  have hr : ((B^(J+2)/t^J)*Real.sqrt (2*(J:ℝ))*Real.sqrt v)/(κ/6)≤
      12/Real.sqrt (6*η₀) := by
    have hh := div_le_div_of_nonneg_right hp hK.le
    have hs := mul_le_mul_of_nonneg_left (conditioning_sqrt_ratio hκ hθκ)
      (show 0≤2/Real.sqrt (6*η₀) by positivity)
    calc
      _≤(2*Real.sqrt θ/Real.sqrt (6*η₀))/(κ/6) := hh
      _≤12/Real.sqrt (6*η₀) := by convert hs using 1 <;> ring
  have hap : 0<a := by linarith
  have he : B^(J+2)*((η₀*L*a)*(η^J*middleWidth Cb ε (κ/6) (η₀*L) (t*η) J/a)/
      normalCoefficient L J)*Real.sqrt v=
      (4*Cb*(ε/L))*(((B^(J+2)/t^J)*Real.sqrt (2*(J:ℝ))*Real.sqrt v)/(κ/6)) := by
    unfold middleWidth normalCoefficient
    rw [mul_pow]
    field_simp
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hr (show 0≤4*Cb*(ε/L) by positivity)
  exact hh.trans_eq (by ring)

theorem source_force_from_fine_factor {P B cms ell β d v R : ℝ}
    (hP : 0≤P) (hB : 0≤B) (hc : 0≤cms) (hell : 0≤ell) (hβ : 0≤β)
    (hd : 0<d) (hv : 1≤v) (hf : ell*β/d*Real.sqrt v≤R) :
    2*P*B*cms*ell*β^2/(d*Real.sqrt v)≤(2*P*B*cms*R)*β := by
  have hs : 1≤Real.sqrt v := Real.one_le_sqrt.mpr hv
  have hsp : 0<Real.sqrt v := by linarith
  have hi : 1/Real.sqrt v≤Real.sqrt v := by
    apply (div_le_iff₀ hsp).mpr
    nlinarith only [hs]
  have hm := mul_le_mul_of_nonneg_left hi (show 0≤ell*β/d by positivity)
  have hb := hm.trans hf
  have hh := mul_le_mul_of_nonneg_left hb (show 0≤2*P*B*cms*β by positivity)
  convert hh using 1 <;> ring

end Bilevel.ChiExtensionCalibration
