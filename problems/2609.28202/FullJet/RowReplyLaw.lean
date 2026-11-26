import FullJet.VectorRows
import FullJet.FiniteProbability

open scoped BigOperators ENNReal

namespace FullJet

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- The entire new row has the product Bernoulli law predicted by sampling
without replacement, under the actual conditional table PMF. -/
theorem vectorColumnLaw_next_row_mass (U : Finset α) (k : ι → ℕ)
    (hk : ∀ j, k j ≤ U.card) (ask : List (ι → Bool) → α) (past rows : List (ι → Bool))
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw U k hk).support) (i : α)
    (hi : ∀ j, i ∈ U \ (vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j))
    (b : ι → Bool) :
    ((((vectorColumnLaw U k hk).filter {S | vectorRowAnswers ask S past rows.length = rows} hpos).map
      (fun S j => decide (i ∈ S j))) b).toReal =
      finiteProductWeight (fun j => bitWeight
        (((k j - (vectorPositiveLabels ask past rows j).card : ℕ) : ℝ) /
          (U \ (vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j)).card)) b := by
  have hprob (j : ι) :
      ((PMF.uniformOfFinset (compatibleColumnSamples U k ask past rows j)
        (vectorColumnLaw_history_feasible U k hk ask past rows hpos j)).toOuterMeasure {S | i ∈ S}).toReal =
        ((k j - (vectorPositiveLabels ask past rows j).card : ℕ) : ℝ) /
          (U \ (vectorPositiveLabels ask past rows j ∪ vectorNegativeLabels ask past rows j)).card := by
    have hcoord := vectorColumnLaw_conditional_coordinate_probability U k hk ask past rows hpos j {S | i ∈ S}
    simp only [Set.mem_setOf_eq] at hcoord
    rw [← hcoord]
    exact vectorColumnLaw_next_probability U k hk ask past rows hpos j i (hi j)
  rw [vectorColumnLaw_condition_history]
  rw [uniformPi_map_coordinates (compatibleColumnSamples U k ask past rows)
    (vectorColumnLaw_history_feasible U k hk ask past rows hpos) (fun _ (S : Finset α) => decide (i ∈ S)) b]
  unfold finiteProductWeight
  apply Finset.prod_congr rfl
  intro j hj
  have hbit := pmf_decide_event
    (PMF.uniformOfFinset (compatibleColumnSamples U k ask past rows j)
      (vectorColumnLaw_history_feasible U k hk ask past rows hpos j)) {S | i ∈ S} (b j)
  simp only [Set.mem_setOf_eq] at hbit
  rw [hbit, hprob]

end FullJet
