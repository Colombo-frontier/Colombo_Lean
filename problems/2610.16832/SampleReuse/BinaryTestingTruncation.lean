import SampleReuse.HiddenBinaryTesting

open MeasureTheory ProbabilityTheory InformationTheory SecondOrder
open scoped Classical ENNReal

namespace SampleReuse
noncomputable section

/-- The strict gap below two-thirds allows truncating an arbitrary halting
algorithm by total time while charging only gradient evaluations. -/
def truncatedTestingConstant : ℝ := (3/5:ℝ)*Real.log 2+Real.log ((2:ℝ)/3)

theorem truncatedTestingConstant_pos : 0 < truncatedTestingConstant := by
  have he : 5*truncatedTestingConstant = Real.log ((256:ℝ)/243) := by
    unfold truncatedTestingConstant
    rw [Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num),
      show (256:ℝ)=2^8 by norm_num,show (243:ℝ)=3^5 by norm_num,
      Real.log_pow,Real.log_pow]
    norm_num
    ring
  have hh := Real.log_pos (by norm_num : (1:ℝ)<256/243)
  linarith

theorem truncated_testing_information {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) (hp : (3/5:ℝ) ≤ μ.real s)
    (hq : ν.real s ≤ (1/2:ℝ)) (hfin : klDiv μ ν ≠ ∞) :
    truncatedTestingConstant ≤ (klDiv μ ν).toReal := by
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
  unfold truncatedTestingConstant
  linarith

theorem truncated_testing_information_ennreal {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) (hp : (3/5:ℝ) ≤ μ.real s) (hq : ν.real s ≤ (1/2:ℝ)) :
    ENNReal.ofReal truncatedTestingConstant ≤ klDiv μ ν := by
  by_cases hfin : klDiv μ ν = ∞
  · simp [hfin]
  · exact (ENNReal.ofReal_le_ofReal (truncated_testing_information hs hp hq hfin)).trans_eq
      (ENNReal.ofReal_toReal hfin)

variable {S A Key : Type} [Fintype A] [MeasurableSpace S]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace Key] [MeasurableSingletonClass Key] [Countable Key]

theorem truncated_hidden_binary_testing_calls
    (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : Bool → Key → PMF A) (q : Key → PMF A) (target : Key → Prop)
    (hsame : ∀ θ key, ¬target key → p θ key = q key)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hKL : ∀ θ key, klDiv (p θ key).toMeasure (q key).toMeasure ≤ ENNReal.ofReal κ)
    (N : ℕ) (classify : FiniteHistory S A N → Bool) (hc : Measurable classify)
    (hsuccess : (3/5:ℝ) ≤
      (adaptiveKernelLaw ((PMF.uniformOfFintype Bool).toMeasure.prod μ)
        (hiddenDisclosureKernel query hq p) N).real
        {h | classify (finiteHistoryMapInitial Prod.snd N h) = (finiteHistoryInitial N h).1}) :
    truncatedTestingConstant ≤ κ*∫ h, finiteHistoryCost (hiddenSelectedCost query target 1) N h
      ∂adaptiveKernelLaw ((PMF.uniformOfFintype Bool).toMeasure.prod μ)
        (hiddenDisclosureKernel query hq p) N := by
  have hs : MeasurableSet {h : FiniteHistory (Bool × S) A N |
      classify (finiteHistoryMapInitial Prod.snd N h) = (finiteHistoryInitial N h).1} :=
    measurableSet_eq_fun_of_countable
      (hc.comp (finiteHistoryMapInitial_measurable measurable_snd N))
      (measurable_fst.comp (finiteHistoryInitial_measurable N))
  have hlo := truncated_testing_information_ennreal hs hsuccess
    (hidden_binary_classification_reference μ (measurableDisclosureKernel query hq q) N classify hc)
  have hup := hidden_selected_disclosure_information μ query hq p q target hsame hκ hKL N
  exact (ENNReal.ofReal_le_ofReal_iff'.mp (hlo.trans hup)).resolve_right
    (not_le_of_gt truncatedTestingConstant_pos)

end
end SampleReuse
