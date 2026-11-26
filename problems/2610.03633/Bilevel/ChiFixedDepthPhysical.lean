import Bilevel.ChiUniformPhysicalBudgets

/-! Exact physical factors for the bounded-curvature fallback J=1,T=1.
There is no chosen-depth or large-parameter threshold in these lemmas. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiIndependentWidths

theorem sqrt_two_le_two : Real.sqrt 2≤2 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp := Real.sqrt_nonneg 2
  nlinarith only [hs,hp]

theorem fixed_depth_normal_curvature {η₀ L : ℝ} (hη₀ : 0≤η₀) (hL : 0<L) :
    η₀*L/normalCoefficient L 1≤8*η₀ := by
  have he : η₀*L/normalCoefficient L 1=4*Real.sqrt 2*η₀ := by
    unfold normalCoefficient
    norm_num
    field_simp
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_right sqrt_two_le_two hη₀
  nlinarith only [hh]

theorem fixed_depth_force_factor {L η₀ Cb ε κ t η b Kg : ℝ}
    (hL : 0<L) (hη₀ : 0<η₀) (hCb : 0≤Cb) (hε : 0≤ε) (hκ : 2≤κ)
    (ht : 0<t) (hη : 0<η)
    (hwidth : b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1) :
    (η₀*L)*b/(Kg*normalCoefficient L 1)≤(24*Cb/(t*η))*(ε/L) := by
  have hK : 0<κ/6 := by linarith only [hκ]
  have hr : Real.sqrt 2/(κ/6)≤6 := by
    apply (div_le_iff₀ hK).mpr
    have hh := sqrt_two_le_two
    linarith only [hh,hκ]
  have he : (η₀*L)*b/(Kg*normalCoefficient L 1)=
      (4*Cb/(t*η)*(ε/L))*(Real.sqrt 2/(κ/6)) := by
    rw [show (η₀*L)*b/(Kg*normalCoefficient L 1)=(η₀*L)*(b/Kg)/normalCoefficient L 1 by ring,hwidth]
    unfold middleWidth normalCoefficient
    norm_num
    field_simp
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hr (show 0≤4*Cb/(t*η)*(ε/L) by positivity)
  exact hh.trans_eq (by ring)

theorem fixed_depth_fine_parameter {μ L η₀ Cf : ℝ} (hμ : 0<μ) (hL : 0<L) :
    fineParameter μ (3*μ/2) (η₀*L) (normalCoefficient L 1) Cf 1=
      1/(12*Real.sqrt 2*η₀*Cf^2) := by
  have hh := fineParameter_source_formula (θ:=1) (η:=η₀) (a:=1) (Cfine:=Cf) hμ hL 1
  norm_num at hh
  exact hh.trans (by field_simp; ring)

theorem fixed_depth_fine_ge_one {μ L η₀ Cf : ℝ} (hμ : 0<μ) (hL : 0<L)
    (hη₀ : 0<η₀) (hCf : 0<Cf) (hsmall : η₀≤1/(24*Cf^2)) :
    1≤fineParameter μ (3*μ/2) (η₀*L) (normalCoefficient L 1) Cf 1 := by
  rw [fixed_depth_fine_parameter hμ hL]
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  apply (one_le_div (by positivity)).mpr
  have hc := (le_div_iff₀ (show 0<24*Cf^2 by positivity)).mp hsmall
  have hh := mul_le_mul_of_nonneg_right sqrt_two_le_two (show 0≤η₀*Cf^2 by positivity)
  nlinarith only [hc,hh]

end Bilevel.ChiExtensionCalibration
