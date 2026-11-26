import HaarRebalancing

/-!
The Haar-basis union bound uses the proved marginal column laws and never
assumes independent columns.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Task006.HaarRebalancing
noncomputable section
variable {d : ℕ}

/-- A finite union over all columns, with no independence premise. -/
theorem basis_bad_union_le (bad : Fin d → Set (EuclideanSpace ℝ (Fin d))) :
    (orthogonalHaarProbability d).real {Q | ∃ i, column Q i ∈ bad i} ≤
      ∑ i : Fin d, (orthogonalHaarProbability d).real {Q | column Q i ∈ bad i} := by
  have hset : {Q : OrthogonalGroup d | ∃ i, column Q i ∈ bad i} =
      ⋃ i : Fin d, {Q | column Q i ∈ bad i} := by
    ext Q
    simp only [mem_setOf_eq, mem_iUnion]
  rw [hset]
  exact measureReal_iUnion_fintype_le _

/-- Identical upper bounds for the column marginals give the exact d factor. -/
theorem basis_bad_probability_le (bad : Set (EuclideanSpace ℝ (Fin d))) {p : ℝ}
    (hcolumn : ∀ i : Fin d, (orthogonalHaarProbability d).real
      {Q | column Q i ∈ bad} ≤ p) :
    (orthogonalHaarProbability d).real {Q | ∃ i, column Q i ∈ bad} ≤ (d : ℝ) * p := by
  calc
    (orthogonalHaarProbability d).real {Q | ∃ i, column Q i ∈ bad} ≤
        ∑ i : Fin d, (orthogonalHaarProbability d).real {Q | column Q i ∈ bad} :=
      basis_bad_union_le (fun _ => bad)
    _ ≤ ∑ _i : Fin d, p := Finset.sum_le_sum (fun i _ => hcolumn i)
    _ = (d : ℝ) * p := by simp

end
end Task006.HaarRebalancing
