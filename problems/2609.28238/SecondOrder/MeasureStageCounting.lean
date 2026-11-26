import SecondOrder.SequentialStageCounting
import SecondOrder.MeasureRareEvent

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The final counting step for arbitrary probability spaces and measurable
stage events. It requires no independence between the stages. -/
theorem measure_sequential_completion_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T N n₀ : ℕ} (hT : 0<T) (hn₀ : 0<n₀)
    (L : Fin T → Ω → ℕ) (reached : Fin T → Set Ω) (complete : Set Ω)
    (hcomplete_meas : MeasurableSet complete)
    (hfast_meas : ∀ i, MeasurableSet {ω | ω ∈ reached i ∧ L i ω<n₀})
    (hcomplete : ∀ ω ∈ complete, ∀ i, ω ∈ reached i)
    (hcharge : ∀ ω, ∑ i, L i ω≤N) (hbudget : 2*N≤T*n₀)
    (hfast : ∀ i, μ.real {ω | ω ∈ reached i ∧ L i ω<n₀}≤1/32) :
    μ.real complete≤1/16 := by
  let f : Fin T → Ω → ℝ := fun i => {ω | ω ∈ reached i ∧ L i ω<n₀}.indicator (fun _ => 1)
  have hf (i : Fin T) : Integrable (f i) μ := (integrable_const 1).indicator (hfast_meas i)
  have hc : Integrable (complete.indicator (fun _ : Ω => (1:ℝ))) μ :=
    (integrable_const 1).indicator hcomplete_meas
  have hpoint (ω : Ω) : (T:ℝ)*complete.indicator (fun _ => (1:ℝ)) ω ≤ 2*∑ i, f i ω := by
    by_cases hx : ω ∈ complete
    · simp only [Set.indicator_of_mem hx,mul_one]
      have he (i : Fin T) : f i ω = if L i ω<n₀ then (1:ℝ) else 0 := by
        simp only [f,Set.indicator_apply,Set.mem_setOf_eq,hcomplete ω hx i,true_and]
      simp_rw [he]
      exact sequential_fast_stages_count hn₀ (fun i => L i ω) (hcharge ω) hbudget
    · simp only [Set.indicator_of_not_mem hx,mul_zero]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => by
        simp only [f,Set.indicator_apply]; split_ifs <;> norm_num))
  have hmean := integral_mono (hc.const_mul (T:ℝ))
    ((integrable_finset_sum _ (fun i _ => hf i)).const_mul 2) hpoint
  rw [integral_const_mul,integral_const_mul,integral_finset_sum _ (fun i _ => hf i),
    integral_indicator_const _ hcomplete_meas] at hmean
  have he (i : Fin T) : (∫ ω, f i ω ∂μ) = μ.real {ω | ω ∈ reached i ∧ L i ω<n₀} := by
    rw [show f i = {ω | ω ∈ reached i ∧ L i ω<n₀}.indicator (fun _ => (1:ℝ)) from rfl,
      integral_indicator_const _ (hfast_meas i)]
    simp only [smul_eq_mul,mul_one]
  simp_rw [he] at hmean
  simp only [smul_eq_mul,mul_one] at hmean
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfast i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have ht : (0:ℝ)<T := by exact_mod_cast hT
  nlinarith

theorem measure_success_of_completion_and_jump (μ : Measure Ω) [IsProbabilityMeasure μ]
    {success complete jump : Set Ω} (hs : success ⊆ complete ∪ jump)
    (hc : μ.real complete≤1/16) (hj : μ.real jump≤1/16) : μ.real success≤1/8 := by
  calc
    _ ≤ μ.real (complete ∪ jump) := measureReal_mono hs
    _ ≤ μ.real complete+μ.real jump := measureReal_union_le _ _
    _ ≤ 1/8 := by linarith

theorem exists_lt_of_integral_lt (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) {c : ℝ} (hmean : (∫ x, f x ∂μ)<c) :
    ∃ x, f x<c := by
  by_contra hn
  have hp : ∀ x, c≤f x := by simpa only [not_exists,not_lt] using hn
  have hi := integral_mono (integrable_const c) hf hp
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hi
  exact not_lt_of_ge hi hmean

end
end SecondOrder
