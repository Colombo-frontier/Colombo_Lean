import NCConcave16991.BaselineCounting

/-! # Actual short-stage counting and its expectation/Markov bound -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.SequentialStages

open BaselineCounting

theorem shortStage_count_lower {J r : ℕ} (hr : 0 < r) (cost : Fin J → ℕ)
    (hbudget : 2 * (∑ j, cost j) ≤ r * J) :
    (J : ℝ) / 2 ≤ ∑ j, score (cost j < r) := by
  have hp (j : Fin J) : (r : ℝ) * (1 - score (cost j < r)) ≤ (cost j : ℝ) := by
    by_cases hj : cost j < r
    · simp only [score, hj, ite_true, sub_self, mul_zero]
      positivity
    · have hh : (r : ℝ) ≤ cost j := by exact_mod_cast le_of_not_gt hj
      simpa only [score, hj, ite_false, sub_zero, mul_one] using hh
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin J))) ↦ hp j)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hb : (2 : ℝ) * (∑ j, (cost j : ℝ)) ≤ (r : ℝ) * J := by exact_mod_cast hbudget
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  by_contra h
  have hm := mul_pos hrR (sub_pos.mpr (lt_of_not_ge h))
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def eventCount {J : ℕ} (E : Fin J → Set Ω) (ω : Ω) : ℝ := ∑ j, score (ω ∈ E j)

theorem eventCount_nonneg {J : ℕ} (E : Fin J → Set Ω) (ω : Ω) : 0 ≤ eventCount E ω := by
  classical
  exact Finset.sum_nonneg (fun j _ ↦ by unfold score; split_ifs <;> norm_num)

theorem eventCount_measurable {J : ℕ} (E : Fin J → Set Ω) (hE : ∀ j, MeasurableSet (E j)) :
    Measurable (eventCount E) := by
  classical
  have he (j : Fin J) : (fun ω ↦ score (ω ∈ E j)) = (E j).indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    simp only [score, Set.indicator_apply]
  unfold eventCount
  apply Finset.measurable_sum
  intro j _
  rw [he]
  exact measurable_const.indicator (hE j)

theorem eventCount_integral {J : ℕ} (E : Fin J → Set Ω) (hE : ∀ j, MeasurableSet (E j)) :
    (∫ ω, eventCount E ω ∂μ) = ∑ j, μ.real (E j) := by
  unfold eventCount
  rw [integral_finsetSum _ (fun j _ ↦ score_integrable μ (hE j))]
  simp only [integral_score μ (hE _)]

theorem many_events_probability_le {J : ℕ} (hJ : 0 < J) (E : Fin J → Set Ω)
    (hE : ∀ j, MeasurableSet (E j)) {p : ℝ} (hprob : ∀ j, μ.real (E j) ≤ p) :
    μ.real {ω | (J : ℝ) / 2 ≤ eventCount E ω} ≤ 2 * p := by
  have hint : Integrable (eventCount E) μ :=
    integrable_finsetSum _ (fun j _ ↦ score_integrable μ (hE j))
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (eventCount_nonneg E)) hint ((J : ℝ) / 2)
  rw [eventCount_integral μ E hE] at hm
  have hs : (∑ j, μ.real (E j)) ≤ (J : ℝ) * p := by
    calc
      _ ≤ ∑ _j : Fin J, p := Finset.sum_le_sum (fun j _ ↦ hprob j)
      _ = _ := by simp
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  by_contra h
  have hp := lt_of_not_ge h
  have hh := mul_pos hJR (sub_pos.mpr hp)
  nlinarith

/-- No independence of short-stage events is required. Their actual marginal
probability bounds and the actual assigned-call costs suffice. -/
theorem completion_probability_le {J r : ℕ} (hJ : 0 < J) (hr : 0 < r)
    (E : Fin J → Set Ω) (hE : ∀ j, MeasurableSet (E j)) {p : ℝ}
    (hprob : ∀ j, μ.real (E j) ≤ p) (S : Set Ω)
    (cost : Ω → Fin J → ℕ)
    (hbudget : ∀ ω ∈ S, 2 * (∑ j, cost ω j) ≤ r * J)
    (hshort : ∀ ω ∈ S, ∀ j, cost ω j < r → ω ∈ E j) : μ.real S ≤ 2 * p := by
  have hsub : S ⊆ {ω | (J : ℝ) / 2 ≤ eventCount E ω} := by
    intro ω hω
    apply (shortStage_count_lower hr (cost ω) (hbudget ω hω)).trans
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : cost ω j < r
    · simp only [score, hj, hshort ω hω j hj, ite_true]
      exact le_rfl
    · simp only [score, hj, ite_false]
      split_ifs <;> norm_num
  exact (measureReal_mono hsub).trans (many_events_probability_le μ hJ E hE hprob)

end NCConcave16991.SequentialStages
