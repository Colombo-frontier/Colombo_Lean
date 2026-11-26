import Bilevel.ChiSourceMacroFloors

/-! Numerical calibration of the direct upper placement on the full
accuracy window. The macro width is proportional to epsilon/L. -/
noncomputable section
namespace Bilevel.ChiUpperNoise
open ChiExtensionCalibration

def baseWidth (Cb ε η₀ L : ℝ) : ℝ := Cb*ε/(η₀*L)

theorem direct_upper_calibration {C Cgap Cb : ℝ} (hC : 1≤C) (hCg : 0<Cgap) (hCb : 0<Cb) :
    ∃ η₀ c : ℝ,0<η₀ ∧ η₀≤1 ∧ 0<c ∧ c≤1 ∧
      ∀ L Δ ε : ℝ,0<L → 0<Δ → 0<ε → ε≤c*min L (Real.sqrt (L*Δ)) →
      let ℓ := η₀*L
      let b := baseWidth Cb ε η₀ L
      let n := macroIndex Δ Cgap (ℓ*b^2)
      0<b ∧ ℓ*b=Cb*ε ∧ C*ℓ≤L/4 ∧ C*(ℓ*b)≤L/4 ∧
      128≤n ∧ Cgap*((n:ℝ)+1)*(ℓ*b^2)≤Δ ∧
      η₀*L*Δ/(4*Cgap*Cb^2*ε^2)≤(n:ℝ) := by
  have hCp : 0<C := by linarith only [hC]
  let η₀ := 1/(4*C)
  let c := min 1 (min (η₀/(256*Cgap*Cb^2)) (1/(4*C*Cb)))
  have hη₀ : 0<η₀ := by dsimp [η₀]; positivity
  have hη₀1 : η₀≤1 := by dsimp [η₀]; apply (div_le_one (by positivity)).mpr; linarith only [hC]
  have hc : 0<c := by dsimp [c]; positivity
  have hc1 : c≤1 := min_le_left _ _
  have hcGap : c≤η₀/(256*Cgap*Cb^2) := (min_le_right _ _).trans (min_le_left _ _)
  have hcGrad : c≤1/(4*C*Cb) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η₀,c,hη₀,hη₀1,hc,hc1,?_⟩
  intro L Δ ε hL hΔ hε hacc
  dsimp only
  let b := baseWidth Cb ε η₀ L
  have hb : 0<b := by dsimp [b,baseWidth]; positivity
  have hforce : (η₀*L)*b=Cb*ε := by dsimp [b,baseWidth]; field_simp
  have henergy : (η₀*L)*b^2=Cb^2*ε^2/(η₀*L) := by
    dsimp [b,baseWidth]
    field_simp
    ring
  have haccL : ε≤c*L := hacc.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le)
  have haccD : ε≤c*Real.sqrt (L*Δ) := hacc.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le)
  have hsq := pow_le_pow_left₀ hε.le haccD 2
  rw [mul_pow,Real.sq_sqrt (mul_pos hL hΔ).le] at hsq
  have hcsq : c^2≤c := by nlinarith only [hc,hc1]
  have hGapc := (le_div_iff₀ (show 0<256*Cgap*Cb^2 by positivity)).mp hcGap
  have hconst : Cgap*Cb^2*c^2≤η₀/256 := by
    have hh := mul_le_mul_of_nonneg_left hcsq (show 0≤Cgap*Cb^2 by positivity)
    nlinarith only [hh,hGapc]
  have hsmall : Cgap*((η₀*L)*b^2)≤Δ/256 := by
    rw [henergy,← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos hη₀ hL)).mpr
    have hh := mul_le_mul_of_nonneg_left hsq (show 0≤Cgap*Cb^2 by positivity)
    have hc' := mul_le_mul_of_nonneg_right hconst (mul_pos hL hΔ).le
    nlinarith only [hh,hc']
  obtain ⟨hn,hgap,hlower,_hupper⟩ := macroIndex_bounds hΔ hCg (mul_pos (mul_pos hη₀ hL) (sq_pos_of_pos hb)) hsmall
  refine ⟨hb,hforce,?_,?_,hn,hgap,?_⟩
  · dsimp only [η₀]
    apply le_of_eq
    field_simp
    ring
  · rw [hforce]
    have hh := mul_le_mul_of_nonneg_left haccL (mul_pos hCp hCb).le
    have hcg := (le_div_iff₀ (show 0<4*C*Cb by positivity)).mp hcGrad
    have hm := mul_le_mul_of_nonneg_right hcg hL.le
    nlinarith only [hh,hm]
  · apply le_trans _ hlower
    apply le_of_eq
    rw [henergy]
    field_simp
    ring

end Bilevel.ChiUpperNoise
