import SecondOrder.MeasureEntropyVariational

open MeasureTheory InformationTheory
open scoped ENNReal Classical

namespace SecondOrder
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Binary-event entropy bound directly on arbitrary probability measures.
The reference probability may vanish; only its positive upper bound is used. -/
theorem measure_event_entropy_lower (hfin : klDiv μ ν ≠ ∞) {s : Set Ω}
    (hs : MeasurableSet s) {q : ℝ} (hq : 0 < q) (hrare : ν.real s ≤ q) :
    μ.real s*Real.log (1/q)-Real.log 2 ≤ (klDiv μ ν).toReal := by
  let f : Ω → ℝ := fun x => s.indicator (fun _ => Real.log (1/q)) x-Real.log 2
  have hf : Integrable f μ := ((integrable_const _).indicator hs).sub (integrable_const _)
  have he : (fun x => Real.exp (f x)) = fun x =>
      s.indicator (fun _ => 1/(2*q)) x+sᶜ.indicator (fun _ => (1/2:ℝ)) x := by
    funext x
    by_cases hx : x ∈ s
    · simp only [f,Set.indicator_of_mem hx,Set.indicator_of_not_mem (show x ∉ sᶜ from by simpa),
        add_zero,Real.exp_sub,Real.exp_log (one_div_pos.mpr hq),Real.exp_log (by norm_num : (0:ℝ)<2)]
      ring
    · simp only [f,Set.indicator_of_not_mem hx,Set.indicator_of_mem (show x ∈ sᶜ from hx),
        zero_sub,zero_add,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2),one_div]
  have hi : Integrable (fun x => Real.exp (f x)) ν := by
    rw [he]
    exact ((integrable_const _).indicator hs).add ((integrable_const _).indicator hs.compl)
  have hmgf : (∫ x, Real.exp (f x) ∂ν) ≤ 1 := by
    rw [he,integral_add ((integrable_const _).indicator hs) ((integrable_const _).indicator hs.compl),
      integral_indicator_const _ hs,integral_indicator_const _ hs.compl]
    simp only [smul_eq_mul]
    have h₁ : ν.real s*(1/(2*q)) ≤ 1/2 := by
      calc
        _ ≤ q*(1/(2*q)) := mul_le_mul_of_nonneg_right hrare (by positivity)
        _ = 1/2 := by field_simp; ring
    have h₂ : ν.real sᶜ*(1/2) ≤ (1/2:ℝ) := by
      have hh : ν.real sᶜ ≤ 1 := measureReal_le_one
      linarith
    linarith
  have hh := integral_le_klDiv_of_exp_integral_le_one hfin hf hi hmgf
  have hv : (∫ x, f x ∂μ) = μ.real s*Real.log (1/q)-Real.log 2 := by
    rw [show f = fun x => s.indicator (fun _ => Real.log (1/q)) x-Real.log 2 from rfl,
      integral_sub ((integrable_const _).indicator hs) (integrable_const _),
      integral_indicator_const _ hs,integral_const]
    simp only [smul_eq_mul,measureReal_def,measure_univ,ENNReal.toReal_one,one_mul]
  rwa [hv] at hh

theorem measure_rare_event_bound {s : Set Ω} (hs : MeasurableSet s)
    {q K L : ℝ} (hq : 0 < q) (hK : 0 ≤ K) (hKL : klDiv μ ν ≤ ENNReal.ofReal K)
    (hL : 0 < L) (hlog : L ≤ Real.log (1/q)) (hrare : ν.real s ≤ q) :
    μ.real s ≤ (K+Real.log 2)/L := by
  have hfin : klDiv μ ν ≠ ∞ := (lt_of_le_of_lt hKL ENNReal.ofReal_lt_top).ne
  have hl := measure_event_entropy_lower hfin hs hq hrare
  have hk := ENNReal.toReal_le_of_le_ofReal hK hKL
  have hm := mul_le_mul_of_nonneg_left hlog (measureReal_nonneg (μ := μ) (s := s))
  apply (le_div_iff₀ hL).mpr
  nlinarith

end
end SecondOrder
