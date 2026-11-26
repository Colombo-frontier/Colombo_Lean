import SecondOrder.RademacherTransfer

open MeasureTheory Filter
open scoped Classical

namespace SecondOrder
noncomputable section

theorem uniform_probability_indicator {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (S : Set α) :
    (PMF.uniformOfFintype α).toMeasure.real S =
      uniformMean (fun a => if a ∈ S then (1:ℝ) else 0) := by
  have hm : MeasurableSet S := (Set.toFinite S).measurableSet
  have hi : (∫ a, S.indicator (fun _ => (1:ℝ)) a ∂(PMF.uniformOfFintype α).toMeasure) =
      uniformMean (fun a => if a ∈ S then (1:ℝ) else 0) := PMF.integral_eq_sum _ _
  rw [integral_indicator_const (1:ℝ) hm] at hi
  simpa using hi

/-- An average within ε/4 of a common upper bound puts at least half of
the uniform candidates within ε/2 of that bound. -/
theorem uniform_candidate_probability {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (R : α → ℝ) {ℓ ε : ℝ}
    (hε : 0 < ε) (hupper : ∀ i, R i ≤ ℓ) (hmean : ℓ-ε/4 ≤ uniformMean R) :
    (1:ℝ)/2 ≤ (PMF.uniformOfFintype α).toMeasure.real {i | ℓ-ε/2 ≤ R i} := by
  rw [uniform_probability_indicator]
  have hp (i : α) : R i ≤ (ℓ-ε/2) + (ε/2)*(if ℓ-ε/2 ≤ R i then (1:ℝ) else 0) := by
    split_ifs with hi
    · simpa using hupper i
    · have hh := lt_of_not_ge hi
      simp only [mul_zero,add_zero]
      exact hh.le
  have hm := uniformMean_mono hp
  rw [uniformMean_add,uniformMean_const,uniformMean_mul] at hm
  have hmul : (ε/2)*(1/2) ≤ (ε/2)*uniformMean (fun i => if ℓ-ε/2 ≤ R i then (1:ℝ) else 0) := by
    linarith
  exact (mul_le_mul_left (by positivity : 0 < ε/2)).mp hmul

theorem product_success_of_sections_ae {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ρ : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    {G : Set Ω} (hG : MeasurableSet G) {S : Set (Ω × Ξ)} (hS : MeasurableSet S)
    {c : ℝ} (hs : ∀ᵐ z ∂μ, z ∈ G → c ≤ ρ.real {w | (z,w) ∈ S}) :
    c * μ.real G ≤ (μ.prod ρ).real S := by
  let I : Ω × Ξ → ℝ := S.indicator (fun _ => 1)
  have hi : Integrable I (μ.prod ρ) := (integrable_const (1:ℝ)).indicator hS
  have hsections (z : Ω) : (∫ w, I (z,w) ∂ρ) = ρ.real {w | (z,w) ∈ S} := by
    have hm : MeasurableSet {w | (z,w) ∈ S} := hS.preimage (measurable_const.prodMk measurable_id)
    exact integral_indicator_one hm
  have hb : (∫ z, G.indicator (fun _ => c) z ∂μ) ≤ ∫ z, ∫ w, I (z,w) ∂ρ ∂μ := by
    apply integral_mono_ae ((integrable_const c).indicator hG) hi.integral_prod_left
    filter_upwards [hs] with z hz
    change G.indicator (fun _ => c) z ≤ ∫ w, I (z,w) ∂ρ
    rw [hsections]
    by_cases hzg : z ∈ G
    · simpa only [Set.indicator_of_mem hzg] using hz hzg
    · simp only [Set.indicator_of_not_mem hzg]
      exact ENNReal.toReal_nonneg
  rw [integral_indicator_const c hG, ← integral_prod _ hi] at hb
  have hiS : (∫ z, I z ∂μ.prod ρ) = (μ.prod ρ).real S := integral_indicator_one hS
  rw [hiS] at hb
  simpa only [smul_eq_mul,mul_comm] using hb

end
end SecondOrder
