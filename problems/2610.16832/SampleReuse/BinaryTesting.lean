import SecondOrder.MeasureEntropyVariational

open MeasureTheory InformationTheory SecondOrder
open scoped Classical ENNReal

namespace SampleReuse
noncomputable section

def binaryTestingConstant : ℝ := (2/3:ℝ)*Real.log 2+Real.log ((2:ℝ)/3)

theorem binaryTestingConstant_pos : 0 < binaryTestingConstant := by
  have he : 3*binaryTestingConstant = Real.log ((32:ℝ)/27) := by
    unfold binaryTestingConstant
    rw [Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num),
      show (32:ℝ)=2^5 by norm_num,show (27:ℝ)=3^3 by norm_num,
      Real.log_pow,Real.log_pow]
    norm_num
    ring
  have hh := Real.log_pos (by norm_num : (1:ℝ)<32/27)
  linarith

/-- A constant information cost for testing success >=2/3 against a reference
success <=1/2. This is proved directly for arbitrary measurable seed spaces. -/
theorem binary_testing_information {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) (hp : (2/3:ℝ) ≤ μ.real s)
    (hq : ν.real s ≤ (1/2:ℝ)) (hfin : klDiv μ ν ≠ ∞) :
    binaryTestingConstant ≤ (klDiv μ ν).toReal := by
  let f : Ω → ℝ := fun x => s.indicator (fun _ => Real.log 2) x+Real.log ((2:ℝ)/3)
  have hf : Integrable f μ := ((integrable_const _).indicator hs).add (integrable_const _)
  have he : (fun x => Real.exp (f x)) = fun x =>
      s.indicator (fun _ => (4/3:ℝ)) x+sᶜ.indicator (fun _ => (2/3:ℝ)) x := by
    funext x
    by_cases hx : x ∈ s
    · simp only [f,Set.indicator_of_mem hx,Set.indicator_of_not_mem
        (show x ∉ sᶜ from by simpa),add_zero,Real.exp_add,
        Real.exp_log (by norm_num : (0:ℝ)<2),Real.exp_log (by norm_num : (0:ℝ)<2/3)]
      norm_num
    · simp only [f,Set.indicator_of_not_mem hx,Set.indicator_of_mem (show x ∈ sᶜ from hx),
        zero_add,Real.exp_log (by norm_num : (0:ℝ)<2/3)]
  have hi : Integrable (fun x => Real.exp (f x)) ν := by
    rw [he]
    exact ((integrable_const _).indicator hs).add ((integrable_const _).indicator hs.compl)
  have hmgf : (∫ x, Real.exp (f x) ∂ν) ≤ 1 := by
    rw [he,integral_add ((integrable_const _).indicator hs) ((integrable_const _).indicator hs.compl),
      integral_indicator_const _ hs,integral_indicator_const _ hs.compl,
      measureReal_compl hs,measureReal_univ_eq_one]
    simp only [smul_eq_mul]
    linarith
  have hh := integral_le_klDiv_of_exp_integral_le_one hfin hf hi hmgf
  have hv : (∫ x, f x ∂μ) = μ.real s*Real.log 2+Real.log ((2:ℝ)/3) := by
    rw [show f = fun x => s.indicator (fun _ => Real.log 2) x+Real.log ((2:ℝ)/3) from rfl,
      integral_add ((integrable_const _).indicator hs) (integrable_const _),
      integral_indicator_const _ hs,integral_const,measureReal_univ_eq_one,one_smul]
    rfl
  rw [hv] at hh
  have hm := mul_le_mul_of_nonneg_right hp (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  unfold binaryTestingConstant
  linarith

theorem binary_testing_information_ennreal {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) (hp : (2/3:ℝ) ≤ μ.real s) (hq : ν.real s ≤ (1/2:ℝ)) :
    ENNReal.ofReal binaryTestingConstant ≤ klDiv μ ν := by
  by_cases hfin : klDiv μ ν = ∞
  · simp [hfin]
  · exact (ENNReal.ofReal_le_ofReal (binary_testing_information hs hp hq hfin)).trans_eq
      (ENNReal.ofReal_toReal hfin)

end
end SampleReuse
