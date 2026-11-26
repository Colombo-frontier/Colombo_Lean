import SampleReuse.SlowSampleAdmissible
import SampleReuse.SlowParameters
import SampleReuse.CurvatureChainLength

open SecondOrder

namespace SampleReuse
noncomputable section

def slowModelScale (P : Parameters) : ℝ :=
  min 1 (min P.gradientNoise (min P.hessianNoise
    (min P.gradientLip (min P.hessianLip P.gradientBound))))

theorem slowModelScale_pos (P : Parameters) : 0 < slowModelScale P := by
  simp only [slowModelScale,lt_min_iff]
  exact ⟨by norm_num,P.gradientNoise_pos,P.hessianNoise_pos,
    P.gradientLip_pos,P.hessianLip_pos,P.gradientBound_pos⟩

theorem slowModelScale_bounds (P : Parameters) :
    slowModelScale P ≤ 1 ∧ slowModelScale P ≤ P.gradientNoise ∧
    slowModelScale P ≤ P.hessianNoise ∧ slowModelScale P ≤ P.gradientLip ∧
    slowModelScale P ≤ P.hessianLip ∧ slowModelScale P ≤ P.gradientBound := by
  simp [slowModelScale,min_le_iff]

def slowRegularityConstant : ℝ :=
  1+firstOrderGeometryConstant+firstOrderNoiseConstant+sampleNoiseThirdConstant

theorem slowRegularityConstant_bounds : 0 < slowRegularityConstant ∧
    firstOrderGeometryConstant ≤ slowRegularityConstant ∧
    firstOrderNoiseConstant ≤ slowRegularityConstant ∧
    sampleNoiseThirdConstant ≤ slowRegularityConstant := by
  have hg := firstOrderGeometryConstant_pos
  have hn := firstOrderNoiseConstant_pos
  have ht := sampleNoiseThirdConstant_pos
  unfold slowRegularityConstant
  constructor <;> [linarith; constructor <;> [linarith; constructor <;> linarith]]

def slowBiasConstant : ℝ := firstOrderGradientConstant/(64*slowRegularityConstant)
def slowCoefficientRadius (P : Parameters) (ε : ℝ) : ℝ :=
  slowBiasConstant*slowModelScale P/ε

theorem slowBiasConstant_pos : 0 < slowBiasConstant :=
  div_pos firstOrderGradientConstant_pos (mul_pos (by norm_num) slowRegularityConstant_bounds.1)

theorem slowAlpha_ge_one {d : ℕ} (hd : 0 < d) : 1 ≤ slowAlpha d := by
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hs := Real.sqrt_le_sqrt hd'
  have ht := Real.sqrt_le_sqrt hs
  simpa only [Real.sqrt_one] using ht

theorem slowDilation_le_one {d : ℕ} (hd : 0 < d) : slowDilation d ≤ 1 := by
  unfold slowDilation
  exact (inv_le_one₀ (slowAlpha_pos hd)).mpr (slowAlpha_ge_one hd)

theorem slowAmplitude_dilation {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    slowAmplitude d ε*slowDilation d = 4*ε/firstOrderGradientConstant :=
  (eq_div_iff firstOrderGradientConstant_pos.ne').mpr (slowAmplitude_scale hd ε)

theorem slowAmplitude_second_scale {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    slowAmplitude d ε*(Real.sqrt d)⁻¹ ≤ 4*ε/firstOrderGradientConstant := by
  rw [← slowDilation_sq]
  calc
    _ = (slowAmplitude d ε*slowDilation d)*slowDilation d := by ring
    _ ≤ (slowAmplitude d ε*slowDilation d)*1 :=
      mul_le_mul_of_nonneg_left (slowDilation_le_one hd)
        (mul_nonneg (slowAmplitude_pos hd hε).le (inv_nonneg.mpr (slowAlpha_pos hd).le))
    _ = _ := by rw [mul_one,slowAmplitude_dilation hd]

theorem slowCoefficientRadius_ge_two (P : Parameters) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ slowBiasConstant*slowModelScale P/2) :
    2 ≤ slowCoefficientRadius P ε := by
  apply (le_div_iff₀ hε).mpr
  linarith

/-- A single universal coefficient scale controls both sample smoothness and
both derivative noise bounds, uniformly in the block dimension. -/
theorem slow_regularity_budget (P : Parameters) {ε c₁ c₂ : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ slowBiasConstant*slowModelScale P/2)
    (h₁ : c₁ ≤ slowRegularityConstant) (h₂ : c₂ ≤ slowRegularityConstant) :
    (4*ε/firstOrderGradientConstant)*(c₁+c₂*(slowCoefficientRadius P ε+1)) ≤ slowModelScale P := by
  have hR := slowCoefficientRadius_ge_two P hε hsmall
  have hC := slowRegularityConstant_bounds.1
  have hbound : c₁+c₂*(slowCoefficientRadius P ε+1) ≤
      2*slowRegularityConstant*slowCoefficientRadius P ε := by
    have hm := mul_le_mul_of_nonneg_right h₂ (by linarith : 0 ≤ slowCoefficientRadius P ε+1)
    have hn := mul_le_mul_of_nonneg_left hR hC.le
    nlinarith only [h₁,hm,hn]
  calc
    _ ≤ (4*ε/firstOrderGradientConstant)*(2*slowRegularityConstant*slowCoefficientRadius P ε) :=
      mul_le_mul_of_nonneg_left hbound (by have := firstOrderGradientConstant_pos; positivity)
    _ = slowModelScale P/8 := by
      unfold slowCoefficientRadius slowBiasConstant
      field_simp [firstOrderGradientConstant_pos.ne',hC.ne',hε.ne']
      ring
    _ ≤ slowModelScale P := by linarith [slowModelScale_pos P]

theorem slow_four_sample_budgets (P : Parameters) {d : ℕ} (hd : 0 < d)
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ slowBiasConstant*slowModelScale P/2) :
    slowAmplitude d ε*(Real.sqrt d)⁻¹*
      (firstOrderGeometryConstant+firstOrderNoiseConstant*(slowCoefficientRadius P ε+1)) ≤ P.gradientLip ∧
    slowAmplitude d ε*slowDilation d*
      (firstOrderGeometryConstant+sampleNoiseThirdConstant*(slowCoefficientRadius P ε+1)) ≤ P.hessianLip ∧
    slowAmplitude d ε*slowDilation d*
      (firstOrderNoiseConstant*(slowCoefficientRadius P ε+1)) ≤ P.gradientNoise ∧
    slowAmplitude d ε*(Real.sqrt d)⁻¹*
      (firstOrderNoiseConstant*(slowCoefficientRadius P ε+1)) ≤ P.hessianNoise := by
  have hC := slowRegularityConstant_bounds
  have hs := slowModelScale_bounds P
  have hR := slowCoefficientRadius_ge_two P hε hsmall
  have hgeom := firstOrderGeometryConstant_pos
  have hnoise := firstOrderNoiseConstant_pos
  have hsec := slowAmplitude_second_scale hd hε
  have hfull := slow_regularity_budget P hε hsmall hC.2.1 hC.2.2.1
  have hthird := slow_regularity_budget P hε hsmall hC.2.1 hC.2.2.2
  have hnoise' := slow_regularity_budget P hε hsmall (c₁ := 0) hC.1.le hC.2.2.1
  simp only [zero_add] at hnoise'
  refine ⟨?_,?_,?_,?_⟩
  · exact ((mul_le_mul_of_nonneg_right hsec (by positivity)).trans hfull).trans hs.2.2.2.1
  · rw [slowAmplitude_dilation hd]
    exact hthird.trans hs.2.2.2.2.1
  · rw [slowAmplitude_dilation hd]
    exact hnoise'.trans hs.2.1
  · exact ((mul_le_mul_of_nonneg_right hsec (by positivity)).trans hnoise').trans hs.2.2.1

def slowPopulationGradientConstant : ℝ := 20+40*completionDerivativeBound

theorem slowPopulationGradientConstant_pos : 0 < slowPopulationGradientConstant := by
  norm_num [slowPopulationGradientConstant,completionDerivativeBound]

theorem slow_global_gradient_scale (P : Parameters) {d : ℕ} (hd : 0 < d)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : slowAmplitude d ε*n ≤ P.gap/40) :
    slowAmplitude d ε*slowDilation d*slowPopulationGradientConstant*Real.sqrt n ≤
      slowPopulationGradientConstant*Real.sqrt (P.gap/(10*firstOrderGradientConstant))*Real.sqrt ε := by
  let A := slowAmplitude d ε
  let β := slowDilation d
  have hA : 0 < A := slowAmplitude_pos hd hε
  have hβ : 0 < β := inv_pos.mpr (slowAlpha_pos hd)
  have hs : A*β^2 ≤ 4*ε/firstOrderGradientConstant := by
    simpa only [A,β,slowDilation_sq] using slowAmplitude_second_scale hd hε
  have hsq : (A*β*Real.sqrt n)^2 = (A*β^2)*(A*n) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)]
    ring
  have hm := mul_le_mul hs hn (by positivity : 0 ≤ A*(n:ℝ))
    (by have := firstOrderGradientConstant_pos; positivity : 0 ≤ 4*ε/firstOrderGradientConstant)
  have hr : (Real.sqrt (P.gap/(10*firstOrderGradientConstant))*Real.sqrt ε)^2 =
      (4*ε/firstOrderGradientConstant)*(P.gap/40) := by
    rw [mul_pow,Real.sq_sqrt (by have := P.gap_pos; have := firstOrderGradientConstant_pos; positivity),
      Real.sq_sqrt hε.le]
    ring
  have hbase : A*β*Real.sqrt n ≤ Real.sqrt (P.gap/(10*firstOrderGradientConstant))*Real.sqrt ε := by
    have hpos : 0 ≤ Real.sqrt (P.gap/(10*firstOrderGradientConstant))*Real.sqrt ε := by positivity
    nlinarith only [hsq,hm,hr,hpos,sq_nonneg
      (Real.sqrt (P.gap/(10*firstOrderGradientConstant))*Real.sqrt ε-A*β*Real.sqrt n)]
  have hh := mul_le_mul_of_nonneg_left hbase slowPopulationGradientConstant_pos.le
  change A*β*slowPopulationGradientConstant*Real.sqrt n ≤ _
  nlinarith only [hh]

end
end SampleReuse
